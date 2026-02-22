# NVDA Add-on: Enchanced Speech History
# Copyright (C) 2012 Tyler Spivey
# Copyright (C) 2015-2025 James Scholes
# This add-on is free software, licensed under the terms of the GNU General Public License (version 2).
# See the file LICENSE for more details.

from collections import deque
import json
import os
import re
import tempfile
import threading
import weakref
from urllib import error as urlError
from urllib import request as urlRequest

import wx

import addonHandler
import api
import config
import globalPluginHandler
import gui
import speech
import speechViewer
import tones
import ui
import versionInfo
from queueHandler import queueFunction, eventQueue
from eventHandler import FocusLossCancellableSpeechCommand
from gui import guiHelper, nvdaControls
from gui.dpiScalingHelper import DpiScalingHelperMixinWithoutInit
from gui.settingsDialogs import NVDASettingsDialog, SettingsPanel
from globalCommands import SCRCAT_SPEECH

try:
	from gui import addonGui
except Exception:
	addonGui = None

try:
	import nh3
	BROWSE_MODE_HISTORY_SUPPORTED = True
except ImportError:
	BROWSE_MODE_HISTORY_SUPPORTED = False


addonHandler.initTranslation()

BUILD_YEAR = getattr(versionInfo, 'version_year', 2021)
CONFIG_SECTION = 'enchancedSpeechHistory'

DEFAULT_HISTORY_ENTRIES = 500
MIN_HISTORY_ENTRIES = 1
MAX_HISTORY_ENTRIES = 10000000

POST_COPY_NOTHING = 'nothing'
POST_COPY_BEEP = 'beep'
POST_COPY_SPEAK = 'speak'
POST_COPY_BOTH = 'speakAndBeep'

DEFAULT_POST_COPY_ACTION = POST_COPY_BEEP

DEFAULT_BEEP_FREQUENCY = 400 # Hz
MIN_BEEP_FREQUENCY = 1 # Hz
MAX_BEEP_FREQUENCY = 20000 # Hz

DEFAULT_BEEP_DURATION = 20 # ms
MIN_BEEP_DURATION = 1 # ms
MAX_BEEP_DURATION = 500 # ms

BOUNDARY_BEEP_FREQUENCY = 200 # Hz
BOUNDARY_BEEP_DURATION = 100 # ms

HTML_CONTAINER_START = '<ul style="list-style: none">'
HTML_CONTAINER_END = '</ul>'
HTML_ITEM_START = '<li>'
HTML_ITEM_END = '</li>'

UPDATE_REPOSITORY = "VIPPotato/nvda-enchanced-speech-history"
LATEST_RELEASE_API_URL = f"https://api.github.com/repos/{UPDATE_REPOSITORY}/releases/latest"
UPDATE_CHECK_TIMEOUT_SECONDS = 8
UPDATE_DOWNLOAD_TIMEOUT_SECONDS = 120


def makeHTMLList(strings):
	listItems = ''.join((f'{HTML_ITEM_START}{string}{HTML_ITEM_END}' for string in map(nh3.clean_text, strings)))
	return f'{HTML_CONTAINER_START}{listItems}{HTML_CONTAINER_END}'


def _versionToTuple(version):
	versionString = str(version).strip().lstrip("vV")
	parts = [int(part) for part in re.findall(r"\d+", versionString)]
	if not parts:
		return (0,)
	return tuple(parts)


def _isVersionNewer(currentVersion, latestVersion):
	currentParts = _versionToTuple(currentVersion)
	latestParts = _versionToTuple(latestVersion)
	maxLen = max(len(currentParts), len(latestParts))
	currentParts += (0,) * (maxLen - len(currentParts))
	latestParts += (0,) * (maxLen - len(latestParts))
	return latestParts > currentParts


def _fetchLatestReleaseInfo():
	request = urlRequest.Request(
		LATEST_RELEASE_API_URL,
		headers={
			"Accept": "application/vnd.github+json",
			"User-Agent": "NVDA-enchancedSpeechHistory-Updater",
		},
	)
	with urlRequest.urlopen(request, timeout=UPDATE_CHECK_TIMEOUT_SECONDS) as response:
		data = json.loads(response.read().decode("utf-8"))
	latestVersion = data.get("tag_name") or data.get("name")
	if not latestVersion:
		raise ValueError("Latest release version is missing from GitHub response")
	downloadUrl = None
	for asset in data.get("assets", []):
		assetName = str(asset.get("name", ""))
		assetUrl = asset.get("browser_download_url")
		if assetName.lower().endswith(".nvda-addon") and assetUrl:
			downloadUrl = str(assetUrl)
			break
	return str(latestVersion), downloadUrl


def _getCurrentAddonVersion():
	try:
		addon = addonHandler.getCodeAddon()
		version = addon.manifest.get("version")
		if version:
			return str(version)
	except Exception:
		pass
	return "0"


class GlobalPlugin(globalPluginHandler.GlobalPlugin):
	_instanceRef = None

	@classmethod
	def getInstance(cls):
		if cls._instanceRef is None:
			return None
		return cls._instanceRef()

	def __init__(self, *args, **kwargs):
		super().__init__(*args, **kwargs)
		confspec = {
			'maxHistoryLength': f'integer(default={DEFAULT_HISTORY_ENTRIES}, min={MIN_HISTORY_ENTRIES}, max={MAX_HISTORY_ENTRIES})',
			'postCopyAction': f'string(default={DEFAULT_POST_COPY_ACTION})',
			'beepFrequency': f'integer(default={DEFAULT_BEEP_FREQUENCY}, min={MIN_BEEP_FREQUENCY}, max={MAX_BEEP_FREQUENCY})',
			'beepDuration': f'integer(default={DEFAULT_BEEP_DURATION}, min={MIN_BEEP_DURATION}, max={MAX_BEEP_DURATION})',
			'beepBoundaryPanning': 'boolean(default=false)',
			'checkForUpdatesOnStartup': 'boolean(default=true)',
			'trimWhitespaceFromStart': 'boolean(default=false)',
			'trimWhitespaceFromEnd': 'boolean(default=false)',
		}
		config.conf.spec[CONFIG_SECTION] = confspec
		NVDASettingsDialog.categoryClasses.append(SpeechHistorySettingsPanel)
		GlobalPlugin._instanceRef = weakref.ref(self)

		self._history = deque(maxlen=config.conf[CONFIG_SECTION]['maxHistoryLength'])
		self._recorded = []
		self._recording = False
		self._updateCheckInProgress = False
		self._updateDownloadInProgress = False
		self.history_pos = 0
		self._patch()
		if config.conf[CONFIG_SECTION]['checkForUpdatesOnStartup']:
			self.checkForUpdates(manual=False)

	def _patch(self):
		if BUILD_YEAR >= 2021:
			self.oldSpeak = speech.speech.speak
			speech.speech.speak = self.mySpeak
		else:
			self.oldSpeak = speech.speak
			speech.speak = self.mySpeak

	def _speakMessage(self, message):
		self.oldSpeak([message])

	def _performPostCopyFeedback(self):
		postCopyAction = config.conf[CONFIG_SECTION]['postCopyAction']
		if postCopyAction in (POST_COPY_BEEP, POST_COPY_BOTH):
			tones.beep(
				config.conf[CONFIG_SECTION]['beepFrequency'],
				config.conf[CONFIG_SECTION]['beepDuration'],
			)
		if postCopyAction in (POST_COPY_SPEAK, POST_COPY_BOTH):
			# Translators: A short confirmation message spoken after copying a Enchanced Speech History item.
			self._speakMessage(_('Copied'))

	def _beepHistoryBoundary(self, atBeginning):
		if config.conf[CONFIG_SECTION]['beepBoundaryPanning']:
			if atBeginning:
				tones.beep(BOUNDARY_BEEP_FREQUENCY, BOUNDARY_BEEP_DURATION, 0, 100)
			else:
				tones.beep(BOUNDARY_BEEP_FREQUENCY, BOUNDARY_BEEP_DURATION, 100, 0)
			return
		tones.beep(BOUNDARY_BEEP_FREQUENCY, BOUNDARY_BEEP_DURATION)

	def checkForUpdates(self, manual=False):
		if self._updateCheckInProgress:
			if manual:
				# Translators: Message reported if an update check is already running.
				ui.message(_('Enchanced Speech History update check is already in progress.'))
			return
		self._updateCheckInProgress = True
		threading.Thread(
			target=self._checkForUpdatesWorker,
			args=(manual,),
			daemon=True,
		).start()

	def _checkForUpdatesWorker(self, manual):
		currentVersion = _getCurrentAddonVersion()
		latestVersion = None
		downloadUrl = None
		errorMessage = None
		isNewVersion = False

		try:
			latestVersion, downloadUrl = _fetchLatestReleaseInfo()
			isNewVersion = _isVersionNewer(currentVersion, latestVersion)
		except (urlError.URLError, ValueError, json.JSONDecodeError) as e:
			errorMessage = str(e)
		except Exception as e:
			errorMessage = str(e)

		wx.CallAfter(
			self._onUpdateCheckComplete,
			manual,
			currentVersion,
			latestVersion,
			downloadUrl,
			isNewVersion,
			errorMessage,
		)

	def _onUpdateCheckComplete(
			self,
			manual,
			currentVersion,
			latestVersion,
			downloadUrl,
			isNewVersion,
			errorMessage,
	):
		self._updateCheckInProgress = False

		if errorMessage:
			if manual:
				# Translators: Message when Enchanced Speech History can't check for updates.
				ui.message(_('Could not check for Enchanced Speech History updates.'))
			return

		if isNewVersion and latestVersion:
			# Translators: Prompt shown when a new Enchanced Speech History version is available.
			message = _(
				'A new Enchanced Speech History version {latestVersion} is available. '
				'You are currently using {currentVersion}. '
				'Do you want to download and install it now?'
			).format(
				latestVersion=latestVersion,
				currentVersion=currentVersion,
			)
			# Translators: Title for Enchanced Speech History update prompt dialog.
			title = _('Enchanced Speech History update available')
			if gui.messageBox(message, title, wx.YES_NO | wx.ICON_INFORMATION) == wx.YES:
				self.downloadAndInstallUpdate(downloadUrl, latestVersion)
			return

		if manual:
			# Translators: Message reported when no new Enchanced Speech History update is available.
			ui.message(_('You are using the latest Enchanced Speech History version.'))

	def downloadAndInstallUpdate(self, downloadUrl, latestVersion):
		if self._updateDownloadInProgress:
			# Translators: Message reported if update download/installation is already running.
			ui.message(_('Enchanced Speech History update download is already in progress.'))
			return
		if not downloadUrl:
			# Translators: Message reported if a newer version exists but no installable package asset is available.
			ui.message(_('Update found, but no .nvda-addon package is available in this release.'))
			return
		# Translators: Message reported when Enchanced Speech History starts downloading an update package.
		ui.message(_('Downloading Enchanced Speech History update.'))
		self._updateDownloadInProgress = True
		threading.Thread(
			target=self._downloadAndInstallUpdateWorker,
			args=(downloadUrl, latestVersion),
			daemon=True,
		).start()

	def _downloadAndInstallUpdateWorker(self, downloadUrl, latestVersion):
		errorMessage = None
		downloadedPath = None
		try:
			request = urlRequest.Request(
				downloadUrl,
				headers={"User-Agent": "NVDA-enchancedSpeechHistory-Updater"},
			)
			with urlRequest.urlopen(request, timeout=UPDATE_DOWNLOAD_TIMEOUT_SECONDS) as response:
				data = response.read()
			if not data:
				raise ValueError("Downloaded update package is empty")
			safeVersion = re.sub(r"[^0-9A-Za-z._-]", "-", str(latestVersion))
			fileName = f"enchancedSpeechHistory-{safeVersion}.nvda-addon"
			downloadedPath = os.path.join(tempfile.gettempdir(), fileName)
			with open(downloadedPath, "wb") as addonPackage:
				addonPackage.write(data)
		except Exception as e:
			errorMessage = str(e)

		wx.CallAfter(
			self._onUpdateDownloadComplete,
			downloadedPath,
			errorMessage,
		)

	def _onUpdateDownloadComplete(self, downloadedPath, errorMessage):
		self._updateDownloadInProgress = False
		if errorMessage:
			# Translators: Message reported when update download fails.
			ui.message(_('Enchanced Speech History update download failed.'))
			return
		if not downloadedPath or not os.path.isfile(downloadedPath):
			# Translators: Message reported when update package is missing after download.
			ui.message(_('Enchanced Speech History update package could not be prepared.'))
			return
		# Translators: Message reported when the add-on begins installation of a downloaded update package.
		ui.message(_('Installing Enchanced Speech History update.'))
		if addonGui and hasattr(addonGui, "handleRemoteAddonInstall"):
			addonGui.handleRemoteAddonInstall(downloadedPath)
			return
		# Translators: Message reported when NVDA install API is unavailable.
		ui.message(_('Automatic install is not available in this NVDA version.'))

	def script_copyLast(self, gesture):
		if not self._history:
			# Translators: A message shown when users try to copy a history item but history is empty.
			self._speakMessage(_('No history items.'))
			return
		text = self.getSequenceText(self._history[self.history_pos])
		if config.conf[CONFIG_SECTION]['trimWhitespaceFromStart']:
			text = text.lstrip()
		if config.conf[CONFIG_SECTION]['trimWhitespaceFromEnd']:
			text = text.rstrip()

		if api.copyToClip(text):
			self._performPostCopyFeedback()

	# Translators: Documentation string for copy currently selected Enchanced Speech History item script
	script_copyLast.__doc__ = _('Copy the currently selected Enchanced Speech History item to the clipboard, which by default will be the most recently spoken text by NVDA.')
	script_copyLast.category = SCRCAT_SPEECH

	def script_prevString(self, gesture):
		if not self._history:
			# Translators: A message shown when users try to review history but it is empty.
			self._speakMessage(_('No history items.'))
			return
		self.history_pos += 1
		if self.history_pos > len(self._history) - 1:
			self._beepHistoryBoundary(atBeginning=False)
			self.history_pos -= 1
		self.oldSpeak(self._history[self.history_pos])
	# Translators: Documentation string for previous Enchanced Speech History item script
	script_prevString.__doc__ = _('Review the previous item in NVDA\'s Enchanced Speech History.')
	script_prevString.category = SCRCAT_SPEECH

	def script_nextString(self, gesture):
		if not self._history:
			# Translators: A message shown when users try to review history but it is empty.
			self._speakMessage(_('No history items.'))
			return
		self.history_pos -= 1
		if self.history_pos < 0:
			self._beepHistoryBoundary(atBeginning=True)
			self.history_pos += 1

		self.oldSpeak(self._history[self.history_pos])
	# Translators: Documentation string for next Enchanced Speech History item script
	script_nextString.__doc__ = _('Review the next item in NVDA\'s Enchanced Speech History.')
	script_nextString.category = SCRCAT_SPEECH

	def script_startRecording(self, gesture):
		if self._recording:
			# Translators: Message spoken when speech recording is already active
			self._speakMessage(_('Already recording speech'))
			return

		# Translators: Message spoken when speech recording is started
		self._speakMessage(_('Started recording speech'))
		self._recording = True
	# Translators: Documentation string for start recording script
	script_startRecording.__doc__ = _('Start recording NVDA\'s speech output, for copying multiple announcements to the clipboard.')
	script_startRecording.category = SCRCAT_SPEECH

	def script_stopRecording(self, gesture):
		if not self._recording:
			# Translators: Message spoken when speech recording is not already active
			self._speakMessage(_('Not currently recording speech'))
			return

		self._recording = False
		recordedText = '\n'.join(self._recorded)
		self._recorded.clear()
		if recordedText:
			api.copyToClip(recordedText)
			# Translators: Message spoken when speech recording is stopped.
			self._speakMessage(_('Recorded speech copied to clipboard'))
		else:
			# Translators: Message spoken when recording is stopped but no announcements were captured.
			self._speakMessage(_('No recorded speech to copy'))
	# Translators: Documentation string for stop recording script
	script_stopRecording.__doc__ = _('Stop recording NVDA\'s speech output, and copy the recorded announcements to the clipboard.')
	script_stopRecording.category = SCRCAT_SPEECH

	def script_showHistory(self, gesture):
		if not BROWSE_MODE_HISTORY_SUPPORTED:
			# Translators: A message shown when users try to view their Enchanced Speech History while running a version of NVDA where this function is not supported.
			message = _('Viewing Enchanced Speech History is not supported in this version of NVDA for security reasons.')
		elif not self._history:
			# Translators: A message shown when users try to view their Enchanced Speech History but it's empty.
			message = _('No history items.')
		else:
			message = makeHTMLList((self.getSequenceText(item) for item in self._history))

		# Translators: The title of the Enchanced Speech History window.
		title = _('Enchanced Speech History')

		try:
			ui.browseableMessage(message=message, title=title, isHtml=True, closeButton=True, sanitizeHtmlFunc=lambda string: string)
		except TypeError:
			ui.browseableMessage(message=message, title=title, isHtml=True)
	# Translators: Documentation string for show Enchanced Speech History script
	script_showHistory.__doc__ = _("Show NVDA's Enchanced Speech History in a browseable list")
	script_showHistory.category = SCRCAT_SPEECH

	def script_showHistoryDialog(self, gesture):
		gui.mainFrame.prePopup()
		dialog = HistoryDialog(gui.mainFrame, self)
		dialog.Show()
		dialog.Raise()
		gui.mainFrame.postPopup()
	# Translators: Documentation string for show Enchanced Speech History dialog script.
	script_showHistoryDialog.__doc__ = _('Open a dialog showing recent items spoken by NVDA.')
	script_showHistoryDialog.category = SCRCAT_SPEECH

	def terminate(self, *args, **kwargs):
		super().terminate(*args, **kwargs)
		if BUILD_YEAR >= 2021:
			speech.speech.speak = self.oldSpeak
		else:
			speech.speak = self.oldSpeak
		NVDASettingsDialog.categoryClasses.remove(SpeechHistorySettingsPanel)
		if GlobalPlugin.getInstance() is self:
			GlobalPlugin._instanceRef = None

	def append_to_history(self, seq):
		seq = [command for command in seq if not isinstance(command, FocusLossCancellableSpeechCommand)]
		self._history.appendleft(seq)
		self.history_pos = 0
		if self._recording:
			self._recorded.append(self.getSequenceText(seq))

	def mySpeak(self, sequence, *args, **kwargs):
		self.oldSpeak(sequence, *args, **kwargs)
		text = self.getSequenceText(sequence)
		if text.strip():
			queueFunction(eventQueue, self.append_to_history, sequence)

	def getSequenceText(self, sequence):
		return speechViewer.SPEECH_ITEM_SEPARATOR.join([x for x in sequence if isinstance(x, str)])

	def clearHistory(self):
		self._history.clear()
		self.history_pos = 0
		self._recorded.clear()

	__gestures = {
		'kb:f12': 'copyLast',
		'kb:shift+f11': 'prevString',
		'kb:shift+f12': 'nextString',
		'kb:NVDA+shift+f11': 'startRecording',
		'kb:NVDA+shift+f12': 'stopRecording',
		'kb:NVDA+h': 'showHistory',
		'kb:NVDA+alt+f12': 'showHistoryDialog',
	}


class SpeechHistorySettingsPanel(SettingsPanel):
	# Translators: the label/title for the Enchanced Speech History settings panel.
	title = _('Enchanced Speech History')

	def makeSettings(self, settingsSizer):
		helper = guiHelper.BoxSizerHelper(self, sizer=settingsSizer)

		# Translators: the label for the preference to choose the maximum number of stored history entries
		maxHistoryLengthLabelText = _('&Maximum number of history entries (requires NVDA restart to take effect)')
		self.maxHistoryLengthEdit = helper.addLabeledControl(maxHistoryLengthLabelText, nvdaControls.SelectOnFocusSpinCtrl, min=MIN_HISTORY_ENTRIES, max=MAX_HISTORY_ENTRIES, initial=config.conf[CONFIG_SECTION]['maxHistoryLength'])

		# Translators: The label for the preference of what to do after copying a Enchanced Speech History item to the clipboard. The options are "Do nothing", "Beep", "Speak", or "Beep and speak".
		postCopyActionComboText = _('&After copying speech:')
		postCopyActionChoices = [
			# Translators: A SpeechHistory option to have NVDA do nothing (no beep or speech) after copying a history item.
			_('Do nothing'),
			# Translators: A SpeechHistory option to have NVDA beep after copying a history item.
			_('Beep'),
			# Translators: A SpeechHistory option to have NVDA speak confirmation after copying a history item.
			_('Speak'),
			# Translators: A SpeechHistory option to have NVDA both beep and speak as confirmation after copying a history item.
			_('Both beep and speak'),
		]
		self.postCopyActionValues = (POST_COPY_NOTHING, POST_COPY_BEEP, POST_COPY_SPEAK, POST_COPY_BOTH)
		self.postCopyActionCombo = helper.addLabeledControl(postCopyActionComboText, wx.Choice, choices=postCopyActionChoices)
		self.postCopyActionCombo.SetSelection(self.postCopyActionValues.index(config.conf[CONFIG_SECTION]['postCopyAction']))
		self.postCopyActionCombo.defaultValue = self.postCopyActionValues.index(DEFAULT_POST_COPY_ACTION)
		self.postCopyActionCombo.Bind(wx.EVT_CHOICE, lambda evt: self.refreshUI())

		# Translators: The label for the Enchanced Speech History setting controlling the frequency of the post-copy beep (in Hz).
		beepFrequencyLabelText = _('Beep &frequency (Hz)')
		self.beepFrequencyEdit = helper.addLabeledControl(beepFrequencyLabelText, nvdaControls.SelectOnFocusSpinCtrl, min=MIN_BEEP_FREQUENCY, max=MAX_BEEP_FREQUENCY, initial=config.conf[CONFIG_SECTION]['beepFrequency'])

		# Translators: The label for the Enchanced Speech History setting controlling the length of the post-copy beep (in milliseconds).
		beepDurationLabelText = _('Beep &duration (ms)')
		self.beepDurationEdit = helper.addLabeledControl(beepDurationLabelText, nvdaControls.SelectOnFocusSpinCtrl, min=MIN_BEEP_DURATION, max=MAX_BEEP_DURATION, initial=config.conf[CONFIG_SECTION]['beepDuration'])

		# Translators: The label of a button in the Enchanced Speech History settings panel for playing a sample beep to test the user's chosen frequency and duration settings.
		self.beepButton = helper.addItem(wx.Button(self, label=_('&Play example beep')))
		self.Bind(wx.EVT_BUTTON, self.onBeepButton, self.beepButton)

		self.refreshUI()

		# Translators: the label for the preference to trim whitespace from the start of text
		self.trimWhitespaceFromStartCB = helper.addItem(wx.CheckBox(self, label=_('Trim whitespace from &start when copying text')))
		self.trimWhitespaceFromStartCB.SetValue(config.conf[CONFIG_SECTION]['trimWhitespaceFromStart'])

		# Translators: the label for the preference to trim whitespace from the end of text
		self.trimWhitespaceFromEndCB = helper.addItem(wx.CheckBox(self, label=_('Trim whitespace from &end when copying text')))
		self.trimWhitespaceFromEndCB.SetValue(config.conf[CONFIG_SECTION]['trimWhitespaceFromEnd'])

		# Translators: The label for enabling left/right panning of boundary beeps while navigating history.
		self.beepBoundaryPanningCB = helper.addItem(wx.CheckBox(self, label=_('Pan history boundary beeps to left/right channels')))
		self.beepBoundaryPanningCB.SetValue(config.conf[CONFIG_SECTION]['beepBoundaryPanning'])

		# Translators: Checkbox label for enabling automatic update checks when NVDA starts.
		self.checkForUpdatesOnStartupCB = helper.addItem(wx.CheckBox(self, label=_('Check for Enchanced Speech History updates when NVDA starts')))
		self.checkForUpdatesOnStartupCB.SetValue(config.conf[CONFIG_SECTION]['checkForUpdatesOnStartup'])

		# Translators: Button label for manually checking Enchanced Speech History updates.
		self.checkForUpdatesButton = helper.addItem(wx.Button(self, label=_('Check for &updates now')))
		self.Bind(wx.EVT_BUTTON, self.onCheckForUpdatesButton, self.checkForUpdatesButton)

	def refreshUI(self):
		postCopyAction = self.postCopyActionValues[self.postCopyActionCombo.GetSelection()]
		enableBeepSettings = postCopyAction in (POST_COPY_BEEP, POST_COPY_BOTH)
		self.beepFrequencyEdit.Enable(enableBeepSettings)
		self.beepDurationEdit.Enable(enableBeepSettings)
		self.beepButton.Enable(enableBeepSettings)

	def onBeepButton(self, event):
		tones.beep(self.beepFrequencyEdit.GetValue(), self.beepDurationEdit.GetValue())

	def onCheckForUpdatesButton(self, event):
		addon = GlobalPlugin.getInstance()
		if addon is None:
			# Translators: Message reported when update check cannot run because add-on instance is unavailable.
			ui.message(_('Enchanced Speech History update check is unavailable right now.'))
			return
		addon.checkForUpdates(manual=True)

	def onSave(self):
		config.conf[CONFIG_SECTION]['maxHistoryLength'] = self.maxHistoryLengthEdit.GetValue()
		config.conf[CONFIG_SECTION]['postCopyAction'] = self.postCopyActionValues[self.postCopyActionCombo.GetSelection()]
		config.conf[CONFIG_SECTION]['beepFrequency'] = self.beepFrequencyEdit.GetValue()
		config.conf[CONFIG_SECTION]['beepDuration'] = self.beepDurationEdit.GetValue()
		config.conf[CONFIG_SECTION]['beepBoundaryPanning'] = self.beepBoundaryPanningCB.GetValue()
		config.conf[CONFIG_SECTION]['checkForUpdatesOnStartup'] = self.checkForUpdatesOnStartupCB.GetValue()
		config.conf[CONFIG_SECTION]['trimWhitespaceFromStart'] = self.trimWhitespaceFromStartCB.GetValue()
		config.conf[CONFIG_SECTION]['trimWhitespaceFromEnd'] = self.trimWhitespaceFromEndCB.GetValue()


class HistoryDialog(
		DpiScalingHelperMixinWithoutInit,
		wx.Dialog  # wxPython does not reliably call base class initializer, put last in MRO
):
	@classmethod
	def _instance(cls):
		"""type: () -> HistoryDialog
		Return None until replaced with a weakref.ref object.
		"""
		return None

	helpId = "enchancedSpeechHistoryElementsList"

	def __new__(cls, *args, **kwargs):
		instance = HistoryDialog._instance()
		if instance is None:
			return super(HistoryDialog, cls).__new__(cls, *args, **kwargs)
		return instance

	def __init__(self, parent, addon):
		if HistoryDialog._instance() is not None:
			self.updateHistory()
			self.Raise()
			return

		HistoryDialog._instance = weakref.ref(self)
		# Translators: The title of the history elements dialog.
		title = _("Enchanced Speech History items")
		super().__init__(
			parent,
			title=title,
			style=wx.DEFAULT_DIALOG_STYLE | wx.RESIZE_BORDER | wx.MAXIMIZE_BOX,
		)

		self.addon = addon
		self.history = []
		self.searchHistory = []
		self.searches = {"": 0}
		self.curSearch = ""
		self.selection = set()

		szMain = guiHelper.BoxSizerHelper(self, sizer=wx.BoxSizer(wx.VERTICAL))
		szCurrent = guiHelper.BoxSizerHelper(self, sizer=wx.BoxSizer(wx.HORIZONTAL))
		szBottom = guiHelper.BoxSizerHelper(self, sizer=wx.BoxSizer(wx.HORIZONTAL))

		# Translators: The label for the search text field in the Enchanced Speech History dialog.
		self.searchTextField = szMain.addLabeledControl(
			_("&Search"),
			wx.TextCtrl,
			style=wx.TE_PROCESS_ENTER,
		)
		self.searchTextField.Bind(wx.EVT_TEXT_ENTER, self.onSearch)
		self.searchTextField.Bind(wx.EVT_KILL_FOCUS, self.onSearch)

		# Translators: The label for the history entries list in the Enchanced Speech History dialog.
		entriesLabel = _("History list")
		self.historyList = nvdaControls.AutoWidthColumnListCtrl(
			parent=self,
			autoSizeColumn=1,
			style=wx.LC_REPORT | wx.LC_NO_HEADER,
		)
		szMain.addItem(self.historyList, flag=wx.EXPAND, proportion=4)
		# This list has one hidden header column used as a placeholder.
		self.historyList.InsertColumn(0, entriesLabel)
		self.historyList.Bind(wx.EVT_LIST_ITEM_SELECTED, self.onSelect)
		self.historyList.Bind(wx.EVT_LIST_ITEM_DESELECTED, self.onDeselect)

		# Multiline field containing full text from selected items.
		self.currentTextElement = szCurrent.addItem(
			wx.TextCtrl(self, style=wx.TE_MULTILINE | wx.TE_READONLY),
			flag=wx.EXPAND,
			proportion=1,
		)

		# Translators: Label for the copy button in the Enchanced Speech History dialog.
		self.copyButton = szCurrent.addItem(wx.Button(self, label=_("&Copy item")), proportion=0)
		self.copyButton.Bind(wx.EVT_BUTTON, self.onCopy)
		szMain.addItem(
			szCurrent.sizer,
			border=guiHelper.BORDER_FOR_DIALOGS,
			flag=wx.EXPAND,
			proportion=1,
		)

		szMain.addItem(
			wx.StaticLine(self),
			border=guiHelper.BORDER_FOR_DIALOGS,
			flag=wx.ALL | wx.EXPAND,
		)

		# Translators: Label for the copy all button in the Enchanced Speech History dialog.
		self.copyAllButton = szBottom.addItem(wx.Button(self, label=_("Copy &all")))
		self.copyAllButton.Bind(wx.EVT_BUTTON, self.onCopyAll)

		# Translators: Label for the clear history button in the Enchanced Speech History dialog.
		self.clearHistoryButton = szBottom.addItem(wx.Button(self, label=_("C&lear history")))
		self.clearHistoryButton.Bind(wx.EVT_BUTTON, self.onClear)

		# Translators: Label for the refresh button in the Enchanced Speech History dialog.
		self.refreshButton = szBottom.addItem(wx.Button(self, label=_("&Refresh history")))
		self.refreshButton.Bind(wx.EVT_BUTTON, self.onRefresh)

		# Translators: The label of a button to close the Enchanced Speech History dialog.
		closeButton = wx.Button(self, label=_("C&lose"), id=wx.ID_CLOSE)
		closeButton.Bind(wx.EVT_BUTTON, lambda evt: self.Close())
		szBottom.addItem(closeButton)
		self.Bind(wx.EVT_CLOSE, self.onClose)
		self.EscapeId = wx.ID_CLOSE

		szMain.addItem(
			szBottom.sizer,
			border=guiHelper.BORDER_FOR_DIALOGS,
			flag=wx.ALL | wx.EXPAND,
			proportion=1,
		)
		szMain = szMain.sizer
		szMain.Fit(self)
		self.SetSizer(szMain)
		self.updateHistory()

		self.SetMinSize(szMain.GetMinSize())
		self.SetSize(self.scaleSize((763, 509)))
		self.CentreOnScreen()
		self.historyList.SetFocus()

	def updateHistory(self):
		self.selection = set()
		self.history = [self.addon.getSequenceText(item) for item in self.addon._history]
		self.doSearch(self.curSearch)

	def doSearch(self, text=""):
		self.selection = set()
		if not text:
			self.searchHistory = list(self.history)
		else:
			self.searchHistory = [item for item in self.history if text in item.lower()]
		self.historyList.DeleteAllItems()
		self.currentTextElement.SetValue("")
		for item in self.searchHistory:
			self.historyList.Append((item[0:100],))
		if self.searchHistory:
			index = self.searches.get(text, 0)
			if index >= len(self.searchHistory):
				index = len(self.searchHistory) - 1
			index = max(index, 0)
			self.historyList.Select(index, on=1)
			self.historyList.SetItemState(index, wx.LIST_STATE_FOCUSED, wx.LIST_STATE_FOCUSED)

	def updateSelection(self):
		self.currentTextElement.SetValue(self.itemsToString(sorted(self.selection)))

	def itemsToString(self, items):
		return "\n".join([self.searchHistory[index] for index in items if index < len(self.searchHistory)])

	def onSearch(self, evt):
		text = self.searchTextField.GetValue().lower()
		if text == self.curSearch:
			return
		index = self.historyList.GetFocusedItem()
		if index < 0:
			index = 0
		self.searches[self.curSearch] = index
		self.curSearch = text
		self.doSearch(text)

	def onClose(self, evt):
		self.DestroyChildren()
		self.Destroy()

	def onCopy(self, evt):
		text = self.currentTextElement.GetValue()
		if text and api.copyToClip(text):
			self.addon._performPostCopyFeedback()

	def onCopyAll(self, evt):
		text = self.itemsToString(range(0, len(self.searchHistory)))
		if text and api.copyToClip(text):
			self.addon._performPostCopyFeedback()

	def onClear(self, evt):
		self.addon.clearHistory()
		self.searches = {"": 0}
		self.Close()

	def onRefresh(self, evt):
		self.updateHistory()

	def onSelect(self, evt):
		index = evt.GetIndex()
		self.selection.add(index)
		self.updateSelection()

	def onDeselect(self, evt):
		index = evt.GetIndex()
		self.selection.discard(index)
		self.updateSelection()
