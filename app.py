#!/usr/bin/env python
# -*- coding: utf-8 -*-

# beta   - Under development
# 1.0.0  - Initial release, change backend to ociotool.exe
#        - Add progress bar to show per file progress
#        - Add error handling
# 1.1.0  - Fix status display color
#        - Add overall progress bar
#        - Fix wrong file list got from selection 
# 1.2.0  - Fix bug: failed conversion when file texture has space
#        - Fix bug: double call on populate
#        - Add map type linear for HDR linear gamma maps, plate for backplate sRGB maps. 
#        - Add support for HDR, auto map type now recgonize .hdr and choose map type "linear"
#        - Add sort item by selected map type
#        - Move file populate function to another thread
#        - Allow multiple map type combobox change (user select multiple + hold Ctrl) 
# 1.2.1  - Update: better looking progress bars
# 1.2.2  - Fix bug: Maya crashed when open
#        - Fix bug: Directory browse dialog does not show files
# 1.2.3  - Fix bug: Error converting path with space(s)
# 1.3.0  - Add feature: mode output - sRGB for converting ACEScg --> sRGB matching exact color

_title = 'ACES Converter'
_version = '1.2.3'
_des = ''
uiName = 'AcesConverter'

# python modules
import sys
import os
script_root = '%s/core' % os.environ.get('RFSCRIPT')
if not script_root in sys.path:
    sys.path.append(script_root)
import tempfile
import logging
import glob
import getpass
import shutil
import fnmatch
import subprocess
from datetime import datetime
from functools import partial
from collections import OrderedDict, defaultdict

# import config
import rf_config as config

# logging
from rf_utils import log_utils
from rf_utils.ui import stylesheet
user = '{}-{}'.format(config.Env.localuser, getpass.getuser()) or 'unknown'
logFile = log_utils.name(uiName, user)
logger = log_utils.init_logger(logFile)
logger.setLevel(logging.DEBUG)

# QT
os.environ['QT_PREFERRED_BINDING'] = os.pathsep.join(['PySide', 'PySide2'])
from Qt import QtCore
from Qt import QtWidgets
from Qt import QtGui
from Qt import QtCompat

# pipeline modules
from rf_utils.oiio import run_oiio
from rf_utils.widget.file_widget import Icon
from rf_utils import thread_pool
from rf_utils import file_utils
from rf_utils import admin
from rf_utils import fileTexturePathResolver as tex_resolver
from rf_utils.context import context_info

moduleDir = os.path.dirname(sys.modules[__name__].__file__).replace('\\', '/')
ACES_MAP_HINT = ['.exr']
HDR_MAPS_HINT = ['.hdr']
COLOR_MAPS_HINT = ['diffuse', 'albedo', 'specular', 'reflection']
PLATE_MAPS_HINT = ['backplate']
ACES_EXT = '.exr'
SRGB_EXT = '.png'

class TextureMapTreeWidgetItem(QtWidgets.QTreeWidgetItem):
    def __lt__(self, other):
        if (not isinstance(other, TextureMapTreeWidgetItem)):
            return super(TextureMapTreeWidgetItem, self).__lt__(other)

        tree = self.treeWidget()
        if (not tree):
            column = 0
        else:
            column = tree.sortColumn()

        return self.sortData(column) < other.sortData(column)

    def __init__(self, *args):
        super(TextureMapTreeWidgetItem, self).__init__(*args)
        self._sortData = {}

    def sortData(self, column):
        return self._sortData.get(column, self.text(column))

    def setSortData(self, column, data):
        self._sortData[column] = data

class AcesConverter(QtWidgets.QMainWindow):
    ''' Application class '''
    progress_status = QtCore.Signal(tuple)
    progress_title = QtCore.Signal(str)
    file_progress = QtCore.Signal(tuple)
    overall_progress = QtCore.Signal(tuple)
    item_result_color = QtCore.Signal(tuple)
    item_result_title_color = QtCore.Signal(tuple)

    def __init__(self, parent=None):
        # setup Window
        super(AcesConverter, self).__init__(parent)

        # app vars
        self.threadpool = QtCore.QThreadPool()
        self.temp_dir = None
        self.directory = os.path.expanduser('~')
        self.hdr = 'HDR'
        self.ldr = 'Color'
        self.raw = 'Data'
        self.plate = 'Plate'
        self.outSRGB = 'Out-sRGB'
        self.ext_map =  OrderedDict([(self.raw, ACES_EXT), 
                                    (self.ldr, ACES_EXT), 
                                    (self.hdr, ACES_EXT), 
                                    (self.plate, ACES_EXT), 
                                    (self.outSRGB, SRGB_EXT)])
        self.map_func = OrderedDict([(self.raw, ('Utility - Raw', 'ACES - ACEScg')), 
                                    (self.ldr, ('Utility - sRGB - Texture', 'ACES - ACEScg')), 
                                    (self.hdr, ('Utility - Linear - sRGB', 'ACES - ACEScg')), 
                                    (self.plate, ('Output - sRGB', 'ACES - ACEScg')), 
                                    (self.outSRGB, ('ACES - ACEScg', 'Output - sRGB'))])
        self.extensions = OrderedDict([("sRGB Images", ['*.png', '*.jpg', '*.jpeg', '*.tif', '*.tiff']), 
                                        ("HDR Images", ['*.exr', '*.hdr']), 
                                        ("All Files", ['*.*'])])

        # ui vars
        self.w = 520
        self.h = 585
        self.app_icon = '{}/icons/app_icon.png'.format(moduleDir)
        self.logo_icon = '{}/icons/riff_logo.png'.format(moduleDir)
        self.aces_icon = '{}/icons/aces_icon.png'.format(moduleDir)
        self.current_icon = '{}/icons/current_icon.png'.format(moduleDir)
        self.convert_icon = '{}/icons/convert_icon.png'.format(moduleDir)
        self.folder_icon = '{}/icons/folder_icon.png'.format(moduleDir)
        self.red_brush = QtGui.QBrush(QtGui.QColor(200, 32, 32))
        self.green_brush = QtGui.QBrush(QtGui.QColor(32, 150, 32))
        self.yellow_brush = QtGui.QBrush(QtGui.QColor(200, 200, 32))
        self.grey_brush = QtGui.QBrush(QtGui.QColor(150, 150, 150))
        self.white_brush = QtGui.QBrush(QtGui.QColor(255, 255, 255))
        self.italic_font = QtGui.QFont()
        self.italic_font.setItalic(True)
        self.white_col = (255, 255, 255)
        self.yellow_col = (255, 255, 32)
        self.green_col = (32, 220, 32)
        self.red_col = (255, 32, 32)

        # init functions
        self.setupUi()
        self.init_signals()
        self.set_default()
        
    def setupUi(self):
        self.setObjectName(uiName)
        self.setWindowTitle('{} {} {}'.format(_title, _version, _des))
        self.setWindowIcon(QtGui.QIcon(self.app_icon))
        self.setLocale(QtCore.QLocale(QtCore.QLocale.English, QtCore.QLocale.UnitedStates))

        self.centralwidget = QtWidgets.QWidget(self)
        self.setCentralWidget(self.centralwidget)
        self.resize(self.w, self.h)

        # main layout
        self.main_layout = QtWidgets.QVBoxLayout(self.centralwidget)
        self.main_layout.setContentsMargins(9, 9, 9, 18)
        self.main_layout.setSpacing(9)

        # header layout
        self.header_layout = QtWidgets.QHBoxLayout()
        self.header_layout.setSpacing(5)
        self.main_layout.addLayout(self.header_layout)

        # logo
        self.logo = QtWidgets.QLabel()
        self.logo.setPixmap(QtGui.QPixmap(self.logo_icon).scaled(48, 48, QtCore.Qt.KeepAspectRatio))
        self.logo.setFixedSize(QtCore.QSize(48, 48))
        self.header_layout.addWidget(self.logo)

        # line
        self.line1 = QtWidgets.QFrame()
        self.line1.setFrameShape(QtWidgets.QFrame.VLine)
        self.line1.setFrameShadow(QtWidgets.QFrame.Sunken)
        self.header_layout.addWidget(self.line1)

        # option layout
        self.input_layout = QtWidgets.QGridLayout()
        self.input_layout.setColumnStretch(0, 0)
        self.input_layout.setColumnStretch(1, 1)
        self.input_layout.setColumnStretch(2, 1)
        self.input_layout.setColumnStretch(3, 1)
        self.input_layout.setContentsMargins(0, 0, 0, 0)
        self.input_layout.setSpacing(5)
        self.header_layout.addLayout(self.input_layout)

        self.dir_label = QtWidgets.QLabel('Directory')
        self.dir_label.setMaximumSize(QtCore.QSize(70, 25))
        self.input_layout.addWidget(self.dir_label, 0, 0, 1, 1, QtCore.Qt.AlignRight)

        self.dir_lineEdit = QtWidgets.QLineEdit()
        self.dir_lineEdit.setPlaceholderText('< Paste or browse texture directory... >')
        self.input_layout.addWidget(self.dir_lineEdit, 0, 1, 1, 3)

        # browse button
        self.browse_button = QtWidgets.QPushButton('...')
        self.browse_button.setMaximumSize(QtCore.QSize(25, 25))
        self.browse_button.setFocusPolicy(QtCore.Qt.ClickFocus)
        self.input_layout.addWidget(self.browse_button, 0, 4, 1, 1)

        # opendir button
        self.opendir_button = QtWidgets.QPushButton('')
        self.opendir_button.setIcon(QtGui.QIcon(self.folder_icon))
        self.opendir_button.setMaximumSize(QtCore.QSize(25, 25))
        self.opendir_button.setFocusPolicy(QtCore.Qt.ClickFocus)
        self.input_layout.addWidget(self.opendir_button, 0, 5, 1, 1)

        # current scene button
        self.current_scene_button = QtWidgets.QPushButton('')
        self.current_scene_button.setIcon(QtGui.QIcon(self.current_icon))
        self.current_scene_button.setMaximumSize(QtCore.QSize(25, 25))
        self.current_scene_button.setFocusPolicy(QtCore.Qt.ClickFocus)
        self.input_layout.addWidget(self.current_scene_button, 0, 6, 1, 1)

        self.filter_label = QtWidgets.QLabel('Filter')
        self.filter_label.setMaximumSize(QtCore.QSize(70, 25))
        self.input_layout.addWidget(self.filter_label, 1, 0, 1, 1, QtCore.Qt.AlignRight)

        self.filter_comboBox = QtWidgets.QComboBox()
        self.filter_comboBox.setMaximumWidth(60)
        self.filter_comboBox.addItems(self.extensions.keys())
        self.filter_comboBox.setMinimumWidth(125)
        self.input_layout.addWidget(self.filter_comboBox, 1, 1, 1, 1)

        # self.header_layout.setStretch(0, 0)
        # self.header_layout.setStretch(0, 5)
        # ----- view layout
        self.view_layout = QtWidgets.QVBoxLayout()
        self.main_layout.addLayout(self.view_layout)

        # tree widget
        self.tree_widget = QtWidgets.QTreeWidget()
        self.tree_widget.setColumnCount(3)
        self.tree_widget.setSortingEnabled(True)
        self.tree_widget.setSelectionMode(QtWidgets.QAbstractItemView.ExtendedSelection)
        header_item = self.tree_widget.headerItem()
        header_item.setText(0, "Name")
        header_item.setText(1, "Details")
        header_item.setText(2, "Map Type")
        header_item.setTextAlignment(1, QtCore.Qt.AlignCenter)
        # header_item.setTextAlignment(2, QtCore.Qt.AlignCenter)

        header = self.tree_widget.header()
        header.resizeSection(0, 285)
        header.resizeSection(1, 130)
        header.resizeSection(2, 60)
        QtCompat.setSectionResizeMode(header, 0, QtWidgets.QHeaderView.Interactive)
        QtCompat.setSectionResizeMode(header, 1, QtWidgets.QHeaderView.Stretch)
        QtCompat.setSectionResizeMode(header, 2, QtWidgets.QHeaderView.ResizeToContents)
        header.setStretchLastSection(False)

        self.view_layout.addWidget(self.tree_widget)

        # convert layout
        self.convert_layout = QtWidgets.QHBoxLayout()
        self.convert_layout.setContentsMargins(0, 0, 0, 0)
        self.main_layout.addLayout(self.convert_layout)

        # progress bar
        self.progress_layout = QtWidgets.QFormLayout()
        self.progress_layout.setContentsMargins(0, 3, 0, 3)
        self.progress_layout.setSpacing(5)
        self.convert_layout.addLayout(self.progress_layout)

        self.file_progressbar = QtWidgets.QProgressBar()
        self.file_progressbar.setMaximumHeight(17)
        self.file_progressbar.setMinimum(0)
        self.file_progressbar.setMaximum(100)
        self.file_progressbar.setValue(0)
        self.progress_layout.addRow('Current', self.file_progressbar)

        self.overall_progressbar = QtWidgets.QProgressBar()
        self.overall_progressbar.setMaximumHeight(23)
        self.overall_progressbar.setMinimum(0)
        self.overall_progressbar.setMaximum(100)
        self.overall_progressbar.setValue(0)
        self.progress_layout.addRow(' Overall', self.overall_progressbar)

        # spacerItem2 = QtWidgets.QSpacerItem(24, 24, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
        # self.convert_layout.addItem(spacerItem2)
        
        # convert button
        self.convert_button = QtWidgets.QPushButton('Convert')
        self.convert_button.setIcon(QtGui.QIcon(self.convert_icon))
        self.convert_button.setFocusPolicy(QtCore.Qt.ClickFocus)
        self.convert_button.setMinimumSize(QtCore.QSize(105, 45))
        self.convert_layout.addWidget(self.convert_button)

        # status line
        self.statusBar = QtWidgets.QStatusBar()
        status_font = QtGui.QFont()
        status_font.setItalic(True)
        self.statusBar.setFont(status_font)
        self.main_layout.addWidget(self.statusBar)


        # tooltips
        self.dir_lineEdit.setToolTip('Directory path of textures')
        self.browse_button.setToolTip('Browse for texture directory')
        self.opendir_button.setToolTip('Open current directory in explorer')
        self.filter_comboBox.setToolTip('Select specific image type to show in viewer')
        self.tree_widget.setToolTip('Select texture item(s) to be used in conversion')
        self.convert_button.setToolTip('Click to convert selected textures')
        self.file_progressbar.setToolTip('Progress of current convert item')
        self.overall_progressbar.setToolTip('The overall progress of conversion')

    def init_signals(self):
        self.browse_button.clicked.connect(self.browse_directory)
        self.opendir_button.clicked.connect(self.open_dir)
        self.filter_comboBox.currentIndexChanged.connect(self.apply_filter)
        # self.dir_lineEdit.editingFinished.connect(self.directory_changed)
        self.dir_lineEdit.textChanged.connect(self.clear)
        self.dir_lineEdit.returnPressed.connect(self.directory_changed)
        self.current_scene_button.clicked.connect(self.get_dir_from_scene)
        self.convert_button.clicked.connect(self.thread_convert)

        # signals
        self.progress_status.connect(self.show_progress_status)
        self.progress_title.connect(self.select_item)
        self.file_progress.connect(self.update_file_progressbar)
        self.overall_progress.connect(self.update_overall_progressbar)
        self.item_result_color.connect(self.set_item_result_color)
        self.item_result_title_color.connect(self.set_item_result_title_color)

    def focusOutEvent(self):
        pass

    def set_default(self):
        if config.isMaya:
            self.current_scene_button.setVisible(True)
            # set default path
            from maya.cmds import file as mc_file
            scene = context_info.ContextPathInfo(path=mc_file(q=True, sn=True))

            tex_dir_path = ''
            try:
                tex_dir_path = scene.path.scheme(key='publishTexture').abs_path()
            except KeyError:
                pass
            if os.path.exists(tex_dir_path):
                self.dir_lineEdit.setText(tex_dir_path)
                self.directory_changed()
        else:
            self.current_scene_button.setVisible(False)

        self.show_status('Ready.', 'normal')
        self.reset_progressbars()
        self.tree_widget.setFocus()

    def get_dir_from_scene(self):
        if config.isMaya:
            import pymel.core as pm
            files = [n for n in pm.ls(type='file') if not n.isReferenced()]
            if files:
                tex_path = str(files[0].fileTextureName.get())
                dir_name = os.path.dirname(tex_path)
                if os.path.exists(dir_name):
                    self.dir_lineEdit.setText(dir_name)
                    self.directory_changed()

    def browse_directory(self):
        dirpath = QtWidgets.QFileDialog.getExistingDirectory(parent=self, 
                                                            caption='Browse Directory',
                                                            dir=self.directory,
                                                            options=QtWidgets.QFileDialog.DontUseNativeDialog)
        if dirpath:
            self.dir_lineEdit.setText(dirpath.replace('\\', '/'))
            self.directory_changed()

    def directory_changed(self):
        self.clear()
        path = str(self.dir_lineEdit.text())
        if '\\' in path:
            self.dir_lineEdit.returnPressed.disconnect()
            path = path.replace('\\', '/')
            self.dir_lineEdit.setText(path)
            self.dir_lineEdit.returnPressed.connect(self.directory_changed)
        if os.path.exists(path):
            self.directory = path
            self.thread_populate()
            self.tree_widget.setFocus()
        else:
            self.directory = os.path.expanduser('~')
            self.show_status('Invalid directory!', level='error')
            self.clear()
            
    def thread_populate(self):
        QtWidgets.QApplication.setOverrideCursor(QtCore.Qt.WaitCursor)
        self.show_status('Populating texture maps...', level='working')
        self.set_ui_enabled(False)

        worker = thread_pool.Worker(self.populate, self.directory)
        worker.signals.result.connect(self.populate_finished)
        self.threadpool.start(worker)

    def populate(self, directory):
        all_files = sorted([f.replace('\\', '/') for f in glob.glob('{}/*.*'.format(directory))])
        file_groups = OrderedDict()  # {displayname: [f1, ..., fn]}
        if not all_files:
            return file_groups
        
        num_files = len(all_files)
        for i, file in enumerate(all_files):
            group_name = os.path.basename(tex_resolver.getFilePatternString(file, 0, 3))
            if group_name not in file_groups:
                file_groups[group_name] = []
            file_groups[group_name].append(file)
            self.progress_status.emit(('Resolving file names: {}/{}'.format(i+1, num_files), 'working'))

        return file_groups

    def populate_finished(self, file_groups):
        self.show_status('Updating UI...', level='working')
        mode_tooltips = '\n'.join(['Data: Maps describes data (Normal, Displacement, Roughness and others)', 
                                'Color: Maps describes color (Diffuse/Albedo)', 
                                'HDR: High-Dynamic range color maps (Diffuse/Albedo)', 
                                'Plate: Maps needs identical look after conversion (Back plate)', 
                                '\n* Hold Ctrl to change multiple items at once'])
        map_keys = self.map_func.keys()
        for group_name, files in file_groups.items():
            group_item = TextureMapTreeWidgetItem(self.tree_widget)

            # set data
            group_item.setData(QtCore.Qt.UserRole, 0, files)

            # set alignment
            group_item.setTextAlignment(1, QtCore.Qt.AlignCenter)
            # set group name
            group_item.setText(0, group_name)
            file_str = 'file(s)' if len(files) > 1 else 'file'
            group_item.setText(1, '{} {}'.format(len(files), file_str))
            group_item.setFont(1, self.italic_font)
            group_item.setForeground(1, self.grey_brush)

            type_combobox = QtWidgets.QComboBox(self)
            type_combobox.addItems(map_keys)
            type_combobox.setMaximumSize(QtCore.QSize(90, 22))
            type_combobox.setToolTip(mode_tooltips)
            
            self.tree_widget.setItemWidget(group_item, 2, type_combobox)


            # guess map type
            lower_file_name = os.path.basename(files[0]).lower()
            lfn, lext = os.path.splitext(lower_file_name)

            if lext in HDR_MAPS_HINT:
                type_combobox.setCurrentIndex(map_keys.index(self.hdr))
                group_item.setSortData(2, map_keys.index(self.hdr))
            elif lext in ACES_MAP_HINT:
                type_combobox.setCurrentIndex(map_keys.index(self.outSRGB))
                group_item.setSortData(2, map_keys.index(self.outSRGB))
            elif [typ for typ in COLOR_MAPS_HINT if typ in lfn]:
                type_combobox.setCurrentIndex(map_keys.index(self.ldr))
                group_item.setSortData(2, map_keys.index(self.ldr))
            elif [typ for typ in PLATE_MAPS_HINT if typ in lfn]:
                type_combobox.setCurrentIndex(map_keys.index(self.plate))
                group_item.setSortData(2, map_keys.index(self.plate))
            else:  # it's a raw data type
                type_combobox.setCurrentIndex(map_keys.index(self.raw))
                group_item.setSortData(2, map_keys.index(self.raw))

            # set combobox signal
            type_combobox.currentIndexChanged.connect(partial(self.change_convert_mode, group_item))

            # set icon
            fn, ext = os.path.splitext(files[0])
            iconWidget = QtGui.QIcon()
            iconPath = Icon.extMap.get(ext.lower(), Icon.extMap['unknown'])
            iconWidget.addPixmap(QtGui.QPixmap(iconPath), QtGui.QIcon.Normal, QtGui.QIcon.Off)
            group_item.setIcon(0, iconWidget)
            for file in files:
                fn, ext = os.path.splitext(file)
                file_item = TextureMapTreeWidgetItem(group_item)
                file_item.setTextAlignment(1, QtCore.Qt.AlignCenter)
                # set data
                file_item.setData(QtCore.Qt.UserRole, 0, file)
                # set filename
                file_item.setText(0, os.path.basename(file))
                # set modified time
                time_stamp = os.path.getmtime(file)
                mod_time = datetime.fromtimestamp(time_stamp).strftime('%y/%m/%d %H:%M:%S')
                file_item.setText(1, mod_time)

                # font color
                file_item.setFont(0, self.italic_font)
                file_item.setFont(1, self.italic_font)
                file_item.setForeground(0, self.grey_brush)
                file_item.setForeground(1, self.grey_brush)

        self.tree_widget.sortItems(0, QtCore.Qt.AscendingOrder)
        self.apply_filter()

        self.set_ui_enabled(True)
        self.show_status('Populate finished', level='success')
        QtWidgets.QApplication.restoreOverrideCursor()
        

    def clear(self):
        self.tree_widget.clear()

    def change_convert_mode(self, curr_item, index):
        curr_item.setSortData(2, index)
        sels = self.tree_widget.selectedItems()
        if not sels:
            return

        for item in sels:
            sel_combobox = self.tree_widget.itemWidget(item, 2)
            curr_index = sel_combobox.currentIndex()
            if curr_index != index:
                sel_combobox.blockSignals(True)
                sel_combobox.setCurrentIndex(index)
                item.setSortData(2, index)
                sel_combobox.blockSignals(False)
        curr_item.setSelected(True)

    def apply_filter(self):
        selected_filters = self.extensions[self.filter_comboBox.currentText()]
        # hide files that doesn't match filter
        rootItem = self.tree_widget.invisibleRootItem()
        for i in range(rootItem.childCount()):
            group_item = rootItem.child(i)
            data = group_item.data(QtCore.Qt.UserRole, 0)[0]
            show = False
            for fil in selected_filters:
                if fnmatch.fnmatch(data, fil):
                    show = True
                    break

            if not show:
                group_item.setHidden(True)
                group_item.setSelected(False)
            else:
                group_item.setHidden(False)
    
    def thread_convert(self):
        sels = self.tree_widget.selectedItems()
        if not sels:
            self.show_status('Please select an item!', level='error')
            return
        file_paths = OrderedDict()  # {title: {mode:mode, files:[f1, ..., fn]}}
        for item in sels:
            parent_item = item.parent()
            
            if not parent_item:  # it's top level item
                title = item.text(0)
                if title not in file_paths:
                    file_paths[title] = {'mode':None, 'files': []}
                combobox = self.tree_widget.itemWidget(item, 2)
                mode = combobox.currentText()
                item_paths = item.data(QtCore.Qt.UserRole, 0)
                file_paths[title] = {'mode': mode, 'files':item_paths}
            else:  # it's child item
                title = parent_item.text(0)
                if title not in file_paths:
                    file_paths[title] = {'mode':None, 'files': []}
                if not parent_item.isSelected():  # if shot item is selected individually
                    combobox = self.tree_widget.itemWidget(parent_item, 2)
                    mode = combobox.currentText()
                    item_path = item.data(QtCore.Qt.UserRole, 0)
                    file_paths[title]['mode'] = mode
                    file_paths[title]['files'].append(item_path)

        detailedText = 'List of file(s) to convert\n'
        for title, file_data in file_paths.items():
            mode = file_data['mode']
            paths = file_data['files']
            detailedText += '- {}\n  {} File(s), Type: {}'.format(title, len(paths), mode)
            num_files = len(paths)
            detailedText += '\n'

        qmsgBox = QtWidgets.QMessageBox(self)
        qmsgBox.setText('Click "Show Details..." to see convert list.\nStart conversion?')
        qmsgBox.setWindowTitle('Confirm')
        qmsgBox.setDetailedText(detailedText)
        qmsgBox.setIcon(QtWidgets.QMessageBox.Question)
        qmsgBox.addButton('    Yes    ', QtWidgets.QMessageBox.AcceptRole)
        qmsgBox.addButton('    No    ', QtWidgets.QMessageBox.RejectRole)
        answer = qmsgBox.exec_()
        if answer == 1: 
            return

        # prepare args for convert function
        self.show_status('Preparing to convert...', level='working')
        func_args = []
        self.temp_dir = tempfile.mkdtemp().replace('\\', '/') 
        is_writable = file_utils.is_writable(self.dir_lineEdit.text())
        num_srcs = len(file_paths)

        for title, file_data in file_paths.items():
            mode = file_data['mode']
            src_paths = file_data['files']
            dest_paths = []
            des_ext = self.ext_map[mode] 
            for p in src_paths:
                fn, ext = os.path.splitext(os.path.basename(p))
                ext_path = '{}/{}{}'.format(self.temp_dir, fn, des_ext)
                dest_paths.append(ext_path)
            from_cs, to_cs = self.map_func[mode]
            func_args.append([title, src_paths, dest_paths, from_cs, to_cs])

        QtWidgets.QApplication.setOverrideCursor(QtCore.Qt.WaitCursor)
        self.show_status('Converting texture maps...', level='working')
        self.set_ui_enabled(False)
        self.reset_progressbars()
        self.file_progressbar.setTextVisible(True)
        self.overall_progressbar.setTextVisible(True)

        worker = thread_pool.Worker(self.convert, func_args, is_writable, num_srcs)
        worker.signals.result.connect(self.convert_finished)
        self.threadpool.start(worker)

    def convert(self, func_args, is_writable, num_srcs):
        result = True
        i = 0
        errors = []
        for title, srcs, dests, from_cs, to_cs in func_args:
            progress_txt = '({}/{})'.format(i+1, num_srcs)
            self.progress_title.emit(title)
            self.item_result_title_color.emit((title, None))
            convert_results = []
            m = 0
            batch_result = True
            num_imgs = len(srcs)
            copy_func = shutil.copy2 if is_writable else admin.copyfile
            for src, dst in zip(srcs, dests):
                filename = os.path.basename(src)
                self.item_result_color.emit((title, filename, None))
                self.progress_status.emit(('Converting {}: {}'.format(progress_txt, filename), 'working'))
                convert_result = run_oiio.convert_colorspace_oiio(src, dst, from_cs, to_cs)

                if not convert_result:
                    self.progress_status.emit(('Error converting {}: {}'.format(progress_txt, filename), 'error'))
                    result = False
                    batch_result = False
                    self.item_result_color.emit((title, filename, False))
                    errors.append(filename)
                else:  # copy result
                    self.progress_status.emit(('Convert success {}: {}'.format(progress_txt, filename), 'success'))
                    src_dir = os.path.dirname(src)
                    res_fn = os.path.basename(convert_result)
                    des = '{}/{}'.format(src_dir, res_fn)
                    copy_func(convert_result, des)
                    self.item_result_color.emit((title, filename, True))
                m += 1
                self.file_progress.emit((m, num_imgs))

            i += 1
            self.overall_progress.emit((i, num_srcs))
            self.item_result_title_color.emit((title, batch_result))
            
        return result, errors

    def convert_finished(self, results):
        result, errors = results

        QtWidgets.QApplication.restoreOverrideCursor()
        self.set_ui_enabled(True)
        self.reset_progressbars()
        qmsgBox = QtWidgets.QMessageBox(self)
        # clear temp
        if os.path.exists(self.temp_dir):
            self.show_status('Removing temp: {}'.format(self.temp_dir), 'working')
            try:
                shutil.rmtree(self.temp_dir)
            except:
                pass
            self.temp_dir = None
        if result:
            result_path = self.dir_lineEdit.text()
            self.show_status('Finished.', level='success')
            qmsgBox.setWindowTitle('Finished')
            qmsgBox.setText('Please check your result.\n{}'.format(result_path))
            qmsgBox.setIcon(QtWidgets.QMessageBox.Information)
            qmsgBox.addButton('  Done  ', QtWidgets.QMessageBox.AcceptRole)
            see_result_button = qmsgBox.addButton(' See Results ', QtWidgets.QMessageBox.YesRole)
            see_result_button.clicked.connect(partial(self.open_dir, result_path))
        else:
            err_msg = 'Something went wrong during conversion,\nplease see details.'
            self.show_status(err_msg, level='error')
            qmsgBox.setWindowTitle('Error')
            qmsgBox.setText(err_msg)
            detailedText = '{} Failed image(s):\n- {}'.format(len(errors), '\n- '.join(errors))
            qmsgBox.setDetailedText(detailedText)
            qmsgBox.setIcon(QtWidgets.QMessageBox.Critical)
            qmsgBox.addButton('  Done  ', QtWidgets.QMessageBox.AcceptRole)
        qmsgBox.exec_()

    def open_dir(self, path=None):
        if not path:
            path = str(self.dir_lineEdit.text())
        if os.path.exists(path):
            subprocess.Popen(r'explorer {}'.format(path.replace('/', '\\')))

    def show_status(self, message, level='normal'):
        level_dict = {'normal': self.white_col, 'working': self.yellow_col, 'success': self.green_col, 'error': self.red_col}
        self.statusBar.showMessage(message)
        self.statusBar.setStyleSheet('color: rgb{}'.format(level_dict.get(level, self.white_col)))

    def show_progress_status(self, args):
        message, level = args
        self.show_status(message=message, level=level)

    def get_item_with_title(self, title):
        rootItem = self.tree_widget.invisibleRootItem()
        for i in range(rootItem.childCount()):
            item = rootItem.child(i)
            item_title = item.text(0)
            if item_title == title:
                return item

    def select_item(self, title):
        self.tree_widget.clearSelection()
        item = self.get_item_with_title(title)
        if item:
            item.setSelected(True)

    def set_item_result_color(self, results):
        ''' set tree widget item color '''
        title, child_name, result = results
        item = self.get_item_with_title(title)
        if item:
            child_items = [item.child(c) for c in range(item.childCount()) if item.child(c).text(0)==child_name]
            if child_items:
                brush_dict = {None: self.yellow_brush, True: self.green_brush, False: self.red_brush}
                child_items[0].setForeground(0, brush_dict[result])

    def set_item_result_title_color(self, results):
        title, result = results
        item = self.get_item_with_title(title)
        if item:
            brush_dict = {None: self.yellow_brush, True: self.green_brush, False: self.red_brush}
            item.setForeground(0, brush_dict[result])

    def update_file_progressbar(self, progresses):
        current, total = progresses
        percentage = (float(current) / total) * 100.0
        self.file_progressbar.setValue(int(percentage))

    def update_overall_progressbar(self, progresses):
        current, total = progresses
        percentage = (float(current) / total) * 100.0
        self.overall_progressbar.setValue(int(percentage))

    def reset_progressbars(self):
        self.file_progressbar.setValue(0)
        self.overall_progressbar.setValue(0)
        self.file_progressbar.setTextVisible(False)
        self.overall_progressbar.setTextVisible(False)

    def set_ui_enabled(self, enabled):
        self.dir_lineEdit.setReadOnly(not enabled)
        self.filter_comboBox.setEnabled(enabled)
        self.convert_button.setEnabled(enabled)

def show():
    bg = 'background-image:url("{}/icons/aces_bg.png");'.format(moduleDir)
    if config.isMaya:
        from rftool.utils.ui import maya_win
        logger.info('Run in Maya\n')
        maya_win.deleteUI(uiName)
        myApp = AcesConverter(parent=maya_win.getMayaWindow())
        myApp.tree_widget.setStyleSheet(bg)
        myApp.show()
    elif config.isNuke:
        from rf_nuke import nuke_win 
        logger.info('Run in Nuke\n')
        nuke_win.deleteUI(uiName)
        myApp = AcesConverter(parent=nuke_win._nuke_main_window())
        myApp.tree_widget.setStyleSheet(bg)
        myApp.show()
    else:
        logger.info('Run in standalone\n')
        app = QtWidgets.QApplication.instance()
        if not app:
            app = QtWidgets.QApplication(sys.argv)
        myApp = AcesConverter(parent=None)
        myApp.show()
        stylesheet.set_default(app)
        myApp.tree_widget.setStyleSheet(bg)
        sys.exit(app.exec_())
    
    return myApp

if __name__ == '__main__':
    show()
