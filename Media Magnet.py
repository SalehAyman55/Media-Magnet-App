import yt_dlp
import os
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog
import pyperclip
import time
import threading
from datetime import datetime
import requests
from urllib.parse import urlparse, urljoin
import subprocess
import json
import os.path
import tempfile
import aiohttp
import asyncio
import logging
import ffmpeg
from PIL import Image, ImageTk
import sys
import dropbox
from bs4 import BeautifulSoup
from plyer import notification
from urllib.parse import parse_qs, urlparse, urlencode, urlunparse
import hashlib
import queue
import csv
import glob
import io
import re
import urllib.parse
import shutil
import socket
"import libtorrent as lt"

# Ensure console supports UTF-8 for Arabic text
if sys.stdout.encoding != 'UTF-8':
    sys.stdout = io.TextIOWrapper(
        sys.stdout.buffer,
        encoding='utf-8',
        line_buffering=True
    )


class UltimateDownloaderPro:
    def __init__(self, root):
        self.root = root
        self.root.title("MediaMagnet")
        self.root.geometry("1000x700")

        # إعدادات الألوان لواجهة المستخدم
        self.primary_color = "#1E3A8A"
        self.secondary_color = "#F3F4F6"
        self.accent_color = "#F59E0B"
        self.dark_mode = False

        # تحميل إعدادات المستخدم
        settings = self.load_settings()
        self.language = settings["language"]
        print(f"تهيئة اللغة: {self.language}")
        self.save_path = settings["save_path"]
        self.batch_save_path = self.save_path
        self.playlist_save_path = self.save_path
        self.download_path = self.save_path  # إضافة self.download_path
        self.batch_available_qualities = {}
        self.batch_formats_cache = {}
        self.playlist_available_qualities = {}  # إضافة لقائمة التشغيل
        self.playlist_formats_cache = {}  # إضافة لقائمة التشغيل
        self.max_workers = settings["max_workers"]
        self.max_speed = settings["max_speed"]
        self.ffmpeg_path = settings["ffmpeg_path"]
        self.cloud_enabled = settings["cloud_enabled"]
        self.cloud_token = settings["cloud_token"]
        self.incomplete_downloads_list = {}

        # متغيرات لتتبع Combobox الحالية
        self.current_combobox = None
        self.current_combobox_row = None
        self.current_combobox_column = None
        self.current_combobox_tree = None

        # متغيرات التحميل
        self.active_downloads = 0
        self.download_queue = []
        self.running = True  # Flag to control queue manager thread
        self.history_file = os.path.join(self.save_path, "download_history.log")
        self.incomplete_file = os.path.join(self.save_path, "incomplete_downloads.json")
        self.stats_file = os.path.join(self.save_path, "download_stats.json")

        # تهيئة التحميلات الغير مكتملة
        self.incomplete_downloads = self.load_incomplete_downloads()

        # تهيئة الإحصائيات
        self.stats = self.load_stats()

        # قواميس تتبع التحميل
        self.formats_cache = {}
        self.download_windows = {}
        self.download_threads = {}
        self.current_download_threads = {}
        self.download_states = {}
        self.icons = {}
        self.total_progress = 0
        self.total_tasks = 0
        self.ffmpeg_available = True
        self.max_speed = 0
        self.cloud_enabled = False
        self.secondary_color = "#E5E7EB"
        self.batch_urls = []
        self.batch_quality_selections = {}
        self.failed_quality_urls = []
        self.batch_download_items = []
        self.batch_quality_comboboxes = {}  # إضافة لتتبع Comboboxes لكل فيديو

        # إعدادات أخرى
        self.auto_shutdown = False
        self.ffmpeg_available = False
        self.playlist_videos = []
        self.video_qualities = {}
        self.single_quality_value = ""
        self.playlist_url_var = tk.StringVar()
        self.thumbnail_cache = {}  # لتخزين الصور المصغرة
        self.tooltip_windows = {}  # لتتبع الـ Tooltips
        self.combobox_widgets = {}  # لتتبع الـ Comboboxes
        self.action_buttons = {}   # لتتبع أزرار الإجراءات

        # خيارات التحميل
        self.mp3_var = tk.BooleanVar(value=False)
        self.subtitles_var = tk.BooleanVar(value=False)

        # إعداد مكونات التطبيق
        self.setup_translations()
        self.load_icons()
        self.setup_styles()
        self.setup_ui()
        self.update_ui_language()
        self.start_queue_manager()
        self.setup_clipboard_monitor()
        self.load_history()
        self.setup_directories()
        self.check_ffmpeg()
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)

        # إضافة مفتاح VirusTotal API
        self.virus_total_api_key = "de8e2fe523c1da59bfe2b423dd6183a2c62fb0027e015039ba93cd30d8776962"
    def load_settings(self):
        # استخدام المجلد الرئيسي للمستخدم كبديل إذا كان المسار الافتراضي غير
        # صالح
        default_save_path = os.path.expanduser("~/Desktop")
        if not os.path.isdir(default_save_path):
            default_save_path = os.path.expanduser("~")
        settings_file = os.path.join(default_save_path, "settings.json")
        default_settings = {
            "language": "ar",
            "save_path": default_save_path,
            "max_workers": 8,
            "max_speed": 0,
            "ffmpeg_path": r"C:\Program Files\ffmpeg\bin\ffmpeg.exe",
            "cloud_enabled": False,
            "cloud_token": ""
        }

        loaded_settings = None
        if os.path.exists(settings_file):
            try:
                with open(settings_file, 'r', encoding='utf-8') as f:
                    loaded_settings = json.load(f)
            except Exception as e:
                print(f"خطأ في تحميل الإعدادات من {settings_file}: {e}")

        if loaded_settings:
            if "language" in loaded_settings and loaded_settings["language"] in [
                "ar", "en"]:
                default_settings["language"] = loaded_settings["language"]
                print(f"تم تحميل اللغة: {loaded_settings['language']}")
            else:
                print(
                    "اللغة غير موجودة أو غير صالحة في settings.json، يتم استخدام الافتراضي: ar")

            if "save_path" in loaded_settings and os.path.isdir(
                loaded_settings["save_path"]):
                default_settings["save_path"] = loaded_settings["save_path"]
                print(f"تم تحميل مسار الحفظ: {default_settings['save_path']}")
            else:
                print(
    f"مسار الحفظ {
        loaded_settings.get(
            'save_path',
             'غير موجود')} غير صالح، يتم استخدام الافتراضي: {default_save_path}")
                default_settings["save_path"] = default_save_path

            default_settings.update(
                {k: v for k, v in loaded_settings.items() if k not in ["language", "save_path"]})
        else:
            print(
    f"ملف الإعدادات غير موجود في {settings_file}، يتم استخدام اللغة الافتراضية: {
        default_settings['language']}")
            try:
                os.makedirs(default_save_path, exist_ok=True)
                with open(settings_file, 'w', encoding='utf-8') as f:
                    json.dump(
    default_settings,
    f,
    ensure_ascii=False,
     indent=4)
                print(
    f"تم إنشاء ملف إعدادات جديد في {settings_file} باللغة الافتراضية: {
        default_settings['language']}")
            except Exception as e:
                print(f"فشل إنشاء ملف الإعدادات في {settings_file}: {e}")

        new_settings_file = os.path.join(
    default_settings["save_path"], "settings.json")
        if new_settings_file != settings_file and os.path.exists(
            settings_file):
            try:
                os.makedirs(default_settings["save_path"], exist_ok=True)
                with open(new_settings_file, 'w', encoding='utf-8') as f:
                    json.dump(
    default_settings,
    f,
    ensure_ascii=False,
     indent=4)
                print(f"تم تحديث موقع ملف الإعدادات إلى: {new_settings_file}")
                os.remove(settings_file)
                print(f"تم إزالة ملف الإعدادات القديم في: {settings_file}")
            except Exception as e:
                print(f"فشل تحديث موقع ملف الإعدادات: {e}")

        return default_settings

    def setup_translations(self):
        """Set up translations for the application."""
        self.translations = {
            "ar": {
                "app_title": "MediaMagnet",
                "welcome": "مرحبًا بك في MediaMagnet",
                "hello_mr_saleh": "مرحبًا السيد صالح",
                "settings": "الإعدادات",
                "dark_mode": "الوضع الليلي",
                "pause": "إيقاف",
                "resume": "استئناف",
                "clear": "مسح",
                "single_download": "تنزيل فردي",
                "batch_download": "تنزيل جماعي",
                "playlist_download": "تنزيل قائمة تشغيل",
                "extract_audio": "استخراج الصوت",
                "export_playlist_data": "تصدير بيانات قائمة التشغيل",
                "export_subtitles": "تصدير الترجمات",
                "history": "السجل",
                "incomplete": "التنزيلات الناقصة",
                "stats": "الإحصائيات",
                "playlist": "قائمة تشغيل",
                "url_label": "الرابط:",
                "extract_links": "استخراج روابط الفيديو",
                "quality_button": "جلب الجودات",
                "publish_date": "تاريخ النشر",
                "use_single_quality": "استخدام جودة موحدة للجميع",
                "download_completed": "اكتمل تنزيل: {}",
                "individual_quality": "اختيار جودة فردية",
                "quality_label": "الجودة:",
                "start_download": "بدء التنزيل",
                "general_url_label": "رابط ملف أو فيديو آخر:",
                "select_folder": "اختيار المجلد",
                "filename_label": "مسار الملف:",
                "batch_settings": "إعدادات التنزيل الجماعي",
                "download_path": "مسار التنزيل",
                "start_batch": "بدء التنزيل الجماعي",
                "batch_status": "جاري بدء التنزيل الجماعي...",
                "invalid_url": "رابط غير صالح",
                "clear_batch": "مسح الكل",
                "downloading": "جاري تنزيل: {}",
                "search_history": "بحث في السجل:",
                "error": "خطأ",
                "clear_history": "مسح السجل",
                "time": "الوقت",
                "type": "النوع",
                "status": "الحالة",
                "details": "التفاصيل",
                "ready": "جاهز",
                "paused": "تم إيقاف: {}",
                "resumed": "تم استئناف: {}",
                "success": "نجاح",
                "failed": "فشل",
                "canceled": "تم الإلغاء",
                "retrying": "إعادة المحاولة {}/{}",
                "added_to_queue": "تمت الإضافة إلى قائمة الانتظار: {}",
                "batch_added": "تمت إضافة {} رابط للتنزيل الجماعي",
                "cleared": "تم المسح",
                "ffmpeg_ready": "FFmpeg جاهز: {}",
                "ffmpeg_error": "خطأ في FFmpeg",
                "ffmpeg_not_found": "FFmpeg غير موجود. يرجى التأكد من المسار أو تثبيت FFmpeg.",
                "download_success": "تم التنزيل بنجاح",
                "no_url": "يرجى إدخال رابط",
                "no_batch_urls": "يرجى إدخال روابط للتنزيل الجماعي",
                "no_qualities": "يرجى اختيار جودة",
                "found_formats": "تم العثور على {} جودة",
                "open_file": "فتح الملف",
                "open_folder": "فتح المجلد",
                "copy_link": "نسخ الرابط",
                "analyze_file": "تحليل الملف",
                "info": "معلومات",
                "close": "إغلاق",
                "download_complete": "اكتمل التنزيل",
                "duration": "المدة: {}",
                "file_size": "حجم الملف: {:.2f} MB",
                "resolution": "الدقة: {}",
                "cloud_upload": "تم الرفع إلى السحابة",
                "update_stats": "تم تحديث الإحصائيات",
                "stats_text": "الملفات: {} | الحجم: {:.2f} MB | السرعة: {:.2f} Mbps | التنزيلات: {}",
                "json_error": "خطأ في ملف JSON",
                "no_incomplete": "لا توجد تنزيلات ناقصة محددة",
                "file_type": "نوع الملف: {}",
                "extracted_links": "تم استخراج {} رابط فيديو",
                "download_finished": "اكتمل تنزيل: {}",
                "download_failed": "فشل تنزيل: {}",
                "multi_part": "تنزيل متعدد الأجزاء مفعل",
                "tooltip_settings": "فتح إعدادات البرنامج",
                "tooltip_dark_mode": "تبديل الوضع الليلي",
                "tooltip_pause": "إيقاف/استئناف جميع التنزيلات",
                "eta": "الوقت المتبقي: {} دقيقة",
                "unsafe_link": "تحذير: الرابط {} قد يكون غير آمن!",
                "duplicate_found": "مكرر: {}. اختر: (تخطي/استبدال/إعادة تسمية)",
                "ffmpeg_missing_warning": "FFmpeg غير موجود. سيتم تنزيل أفضل تنسيق مدمج متاح.",
                "fetch_videos": "جلب الفيديوهات",
                "select_videos": "تحديد الفيديوهات للتنزيل",
                "title": "العنوان",
                "duration_label": "المدة",
                "size": "الحجم",
                "no_videos": "لم يتم العثور على فيديوهات في قائمة التشغيل",
                "warning": "تحذير",
                "select_all": "تحديد الكل",
                "deselect_all": "إلغاء تحديد الكل",
                "download_selected": "تنزيل المحدد",
                "pause_download": "إيقاف التنزيل",
                "resume_download": "استئناف التنزيل",
                "batch_urls": "الروابط",
                "no_batch_urls": "يرجى إدخال روابط صالحة",
                "batch_added": "تمت إضافة {} رابط/روابط",
                "found_formats": "تم العثور على {} جودة/جودات",
                "preview": "معاينة الفيديو",
                "cancel_download": "إلغاء التنزيل",
                "playlist_url": "رابط قائمة التشغيل",
                "select_quality": "اختر الجودة",
                "video_quality": "جودة الفيديو",
                "url": "الرابط",  # لإصلاح المشكلة الحالية
                "title": "العنوان",  # مطلوب في Treeview
                "duration": "المدة",  # مطلوب في Treeview
                "quality": "الجودة",  # مطلوب في Treeview
                "size": "الحجم",  # مطلوب في Treeview
                "video_only": "فيديو فقط",
                "audio_only": "صوت فقط (MP3)",
                "video_with_subtitles": "فيديو مع ترجمة",
                "batch_url": "الرابط",
                "batch_quality": "الجودة",
                "batch_size": "الحجم",
                "fetch_quality": "جلب الجودات",
                "no_quality_selected": "يرجى اختيار جودة للرابط: {}",
                "add_url": "إضافة رابط",
                "remove_url": "إزالة رابط",
                "filename": "اسم الملف",
                "download_time": "وقت التنزيل: {}",
                "select_country": "اختر الدولة للترجمة",
                "fetching_videos": "جارٍ جلب الفيديوهات",
                "fetching_qualities": "جارٍ جلب الجودات...",
                "save_path": "مسار الحفظ",
                "quality": "الجودة",
                "playlist_url_label": "رابط قائمة التشغيل:",
                "playlist_path_label": "مسار الحفظ:",
                "download_started": "بدأ تنزيل {0} رابط/روابط",
                "download_error": "خطأ في تنزيل {0}: {1}",
                "all_downloads_complete": "اكتمل تنزيل جميع الروابط",
                "no_selected_urls": "لم يتم تحديد أي روابط",
                "batch_urls": "الروابط",
                "enter_urls": "أدخل الروابط",
                "clear_urls": "حذف الروابط",
                "info": "المعلومات",
                "download_speed": "سرعة التنزيل: {:.2f} ميجابت/ث",
                "remaining_time": "المدة المتبقية: {} دقيقة",
                "progress": "التقدم",
                "download_details": "تفاصيل التنزيل",
                "browse": "تصفح",
                "completed_downloads": "التنزيلات المكتملة",
                "confirm": "تأكيد",
                "invalid_path": "مسار الحفظ غير صالح",
                # ترجمات جديدة لتحميل التورنت
                "torrent_download": "تنزيل تورنت",
                "select_torrent": "اختر ملف تورنت أو أدخل رابط Magnet",
                "torrent_files": "ملفات التورنت",
                "select_files": "اختر الملفات",
                "virus_scan": "فحص الفيروسات",
                "virus_clean": "الرابط آمن",
                "virus_detected": "تم اكتشاف تهديد!",
                "no_files_selected": "لم يتم اختيار ملفات للتنزيل"
            },
            "en": {
                "app_title": "Ultimate Downloader Pro",
                "welcome": "Welcome to UltimateDownloaderPro",
                "hello_mr_saleh": "Hello Mr Saleh",
                "settings": "Settings",
                "dark_mode": "Dark Mode",
                "pause": "Pause",
                "resume": "Resume",
                "clear": "Clear",
                "single_download": "Single Download",
                "batch_download": "Batch Download",
                "playlist_download": "Playlist Download",
                "extract_audio": "Extract Audio",
                "export_playlist_data": "Export Playlist Data",
                "export_subtitles": "Export Subtitles",
                "history": "History",
                "incomplete": "Incomplete Downloads",
                "stats": "Statistics",
                "playlist": "Playlist",
                "url_label": "URL:",
                "extract_links": "Extract Video Links",
                "quality_button": "Fetch Qualities",
                "publish_date": "Publish Date",
                "use_single_quality": "Use Single Quality for All",
                "download_completed": "Download Completed: {}",
                "individual_quality": "Select Individual Quality",
                "quality_label": "Quality:",
                "start_download": "Start Download",
                "general_url_label": "General File or Video URL:",
                "select_folder": "Select Folder",
                "filename_label": "File Path:",
                "batch_settings": "Batch Download Settings",
                "download_path": "Download Path",
                "start_batch": "Start Batch",
                "batch_status": "Starting batch download...",
                "warning": "Warning",
                "clear_batch": "Clear All",
                "search_history": "Search History:",
                "clear_history": "Clear History",
                "downloading": "Downloading: {}",
                "time": "Time",
                "type": "Type",
                "status": "Status",
                "details": "Details",
                "ready": "Ready",
                "paused": "Paused: {}",
                "resumed": "Resumed: {}",
                "success": "Success",
                "preview": "Preview",
                "failed": "Failed",
                "canceled": "Canceled",
                "retrying": "Retrying {}/{}",
                "added_to_queue": "Added to queue: {}",
                "batch_added": "Added {} URLs to batch",
                "cleared": "Cleared",
                "ffmpeg_ready": "FFmpeg ready: {}",
                "ffmpeg_error": "FFmpeg error",
                "ffmpeg_not_found": "FFmpeg not found. Please ensure the path is correct or install FFmpeg.",
                "download_success": "Download completed successfully",
                "no_url": "Please enter a URL",
                "no_batch_urls": "Please enter URLs for batch",
                "no_qualities": "Please select a quality",
                "found_formats": "Found {} formats",
                "open_file": "Open File",
                "open_folder": "Open Folder",
                "copy_link": "Copy Link",
                "analyze_file": "Analyze File",
                "close": "Close",
                "invalid_url": "Invalid URL",
                "download_complete": "Download Complete",
                "duration": "Duration: {}",
                "file_size": "File Size: {:.2f} MB",
                "resolution": "Resolution: {}",
                "cloud_upload": "Uploaded to cloud",
                "update_stats": "Stats updated",
                "stats_text": "Files: {} | Size: {:.2f} MB | Speed: {:.2f} Mbps | Downloads: {}",
                "json_error": "Error in JSON file",
                "no_incomplete": "No incomplete downloads selected",
                "file_type": "File Type: {}",
                "extracted_links": "{} video links extracted",
                "download_finished": "Download Finished: {}",
                "download_failed": "Download Failed: {}",
                "multi_part": "Multi-Part Download Enabled",
                "tooltip_settings": "Open program settings",
                "tooltip_dark_mode": "Toggle dark mode",
                "tooltip_pause": "Pause/Resume all downloads",
                "eta": "Estimated Time: {} minutes",
                "unsafe_link": "Warning: The link {} may be unsafe!",
                "duplicate_found": "Duplicate file: {}. Choose: (Skip/Replace/Rename)",
                "ffmpeg_missing_warning": "FFmpeg is not available. Downloading best available combined format.",
                "fetch_videos": "Fetch Videos",
                "select_videos": "Select videos to download",
                "title": "Title",
                "duration_label": "Duration",
                "size": "Size",
                "no_videos": "No videos found in the playlist",
                "select_all": "Select All",
                "deselect_all": "Deselect All",
                "download_selected": "Download Selected",
                "pause_download": "Pause Download",
                "resume_download": "Resume Download",
                "cancel_download": "Cancel Download",
                "error": "Error",
                "playlist_url": "Playlist URL",
                "select_quality": "Select Quality",
                "video_quality": "Video Quality",
                "browse": "Browse",
                "video_only": "Video Only",
                "audio_only": "Audio Only (MP3)",
                "video_with_subtitles": "Video with Subtitles",
                "batch_url": "URL",
                "batch_quality": "Quality",
                "batch_size": "Size",
                "fetch_quality": "Fetch Qualities",
                "no_quality_selected": "Please select a quality for URL: {}",
                "add_url": "Add URL",
                "remove_url": "Remove URL",
                "filename": "File Name",
                "download_time": "Download Time: {}",
                "select_country": "Select Country for Subtitles",
                "fetching_videos": "Fetching videos...",
                "fetching_qualities": "Fetching qualities...",
                "save_path": "Save Path",
                "quality": "Quality",
                "playlist_url_label": "Playlist URL:",
                "playlist_path_label": "Save Prairie Path:",
                "download_started": "Started downloading {0} URL(s)",
                "download_error": "Error downloading {0}: {1}",
                "all_downloads_complete": "All downloads completed",
                "no_selected_urls": "No URLs selected",
                "batch_urls": "URLs",
                "info": "Info",
                "quality": "Quality",
                "title": "Title",
                "duration": "Duration",
                "size": "Size",
                "url": "URL",  # المفتاح اللي كان ناقص
                "download_speed": "Download Speed: {:.2f} Mbps",
                "remaining_time": "Remaining Time: {} minutes",
                "progress": "Progress",
                "download_details": "Download Details",
                "completed_downloads": "Completed Downloads",
                "enter_urls": " Enter_URLS",
                "clear_urls": " Clear_URLS",
                "confirm": "Confirm",
                "invalid_path": "Invalid save path",
                # ترجمات جديدة لتحميل التورنت
                "torrent_download": "Torrent Download",
                "select_torrent": "Select Torrent File or Enter Magnet Link",
                "torrent_files": "Torrent Files",
                "select_files": "Select Files",
                "virus_scan": "Virus Scan",
                "virus_clean": "Link is safe",
                "virus_detected": "Threat detected!",
                "no_files_selected": "No files selected for download"
            }
        }
    def setup_ui(self):
        self.root.configure(bg=self.primary_color)
        self.header_frame = ttk.Frame(self.root, style="Header.TFrame")
        self.header_frame.pack(fill=tk.X)

        self.welcome_label = ttk.Label(
            self.header_frame,
            text=self.translations[self.language]['welcome'],
            font=("Segoe UI", 18, "bold"),
            foreground=self.accent_color,
            background=self.primary_color,
            padding=(10, 10)
        )
        self.welcome_label.pack(side=tk.LEFT, padx=10)

        self.hello_label = ttk.Label(
            self.header_frame,
            text=self.translations[self.language]['hello_mr_saleh'],
            font=("Segoe UI", 16),
            foreground=self.accent_color,
            background=self.primary_color,
            padding=(10, 10)
        )
        self.hello_label.pack(side=tk.LEFT, padx=10)

        self.main_frame = ttk.Frame(self.root, style="TFrame", padding=7)
        self.main_frame.pack(fill=tk.BOTH, expand=True)

        self.setup_toolbar()

        self.notebook = ttk.Notebook(self.main_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True, pady=7)

        self.create_download_tab()
        self.create_batch_tab()
        self.create_history_tab()
        self.create_incomplete_tab()
        self.create_stats_tab()
        self.create_playlist_tab()
        self.create_torrent_tab()  # إضافة تبويب التورنت

        # Add a frame for overall progress (status_frame)
        self.status_frame = ttk.Frame(self.root, style="TFrame")
        self.status_frame.pack(fill=tk.X, padx=5, pady=5)

        # Add the overall progress label inside status_frame
        self.overall_progress_label = ttk.Label(
            self.status_frame,
            text="التقدم الكلي: 0.00%",
            foreground="#1E3A8A",
            font=("Segoe UI", 10)
        )
        self.overall_progress_label.pack(anchor="w", padx=5)

        self.status_bar = ttk.Label(
            self.root,
            text=self.translations[self.language]["ready"],
            relief=tk.SUNKEN,
            background=self.primary_color,
            foreground="white",
            font=("Segoe UI", 10),
            padding=5
        )
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)

    def setup_toolbar(self):
        toolbar = ttk.Frame(self.main_frame, style="TFrame")
        toolbar.pack(fill=tk.X, pady=6)

        self.settings_button = ttk.Button(
            toolbar,
            text=self.translations[self.language]["settings"],
            command=self.open_settings,
            style="Accent.TButton"
        )
        self.settings_button.pack(side=tk.RIGHT, padx=5)
        self.add_tooltip(
            self.settings_button,
            self.translations[self.language]["tooltip_settings"]
        )

        self.dark_mode_button = ttk.Button(
            toolbar,
            text=self.translations[self.language]["dark_mode"],
            command=self.toggle_dark_mode,
            style="Accent.TButton"
        )
        self.dark_mode_button.pack(side=tk.RIGHT)
        self.add_tooltip(
            self.dark_mode_button,
            self.translations[self.language]["tooltip_dark_mode"]
        )

    def add_tooltip(self, widget, text):
        tooltip = None

        def show(event):
            nonlocal tooltip
            if tooltip is not None:  # لو التلميح موجود بالفعل، ما ننشئش واحد جديد
                tooltip.deiconify()  # بس نظهّره
                return
            x = event.x_root + 20
            y = event.y_root + 10
            # نربط التلميح بالعنصر نفسه مش بالنافذة الرئيسية
            tooltip = tk.Toplevel(widget)
            tooltip.wm_overrideredirect(True)
            tooltip.wm_geometry(f"+{x}+{y}")
            label = ttk.Label(
                tooltip,
                text=text,
                background="#FFFFE0",
                relief="solid",
                borderwidth=1,
                padding=2
            )
            label.pack()

        def hide(event):
            nonlocal tooltip
            if tooltip is not None:
                try:
                    tooltip.withdraw()  # إخفاء التلميح بس من غير تدميره
                except tk.TclError:
                    pass  # لو النافذة مش موجودة، نتجاهل الخطأ

        def destroy_tooltip(event):
            nonlocal tooltip
            if tooltip is not None:
                try:
                    tooltip.destroy()  # تدمير التلميح لما العنصر يتدمر
                except tk.TclError:
                    pass
                finally:
                    tooltip = None

        widget.bind("<Enter>", show)
        widget.bind("<Leave>", hide)
        widget.bind("<Destroy>", destroy_tooltip)  # ربط حدث تدمير العنصر

    def create_torrent_tab(self):
        """إنشاء تبويب تحميل التورنت."""
        torrent_frame = ttk.Frame(self.notebook, style="TFrame")
        self.notebook.add(torrent_frame, text=self.translations[self.language]['torrent_download'])

        # إطار إدخال رابط Magnet أو ملف تورنت
        input_frame = ttk.Frame(torrent_frame)
        input_frame.pack(fill=tk.X, padx=10, pady=10)

        ttk.Label(input_frame, text=self.translations[self.language]['select_torrent'], font=("Segoe UI", 10)).pack(side=tk.LEFT)
        self.torrent_var = tk.StringVar()
        torrent_entry = ttk.Entry(input_frame, textvariable=self.torrent_var, width=50)
        torrent_entry.pack(side=tk.LEFT, padx=5)

        def browse_torrent_file():
            file_path = filedialog.askopenfilename(filetypes=[("Torrent files", "*.torrent")])
            if file_path:
                self.torrent_var.set(file_path)

        ttk.Button(input_frame, text="...", command=browse_torrent_file, style="Accent.TButton").pack(side=tk.LEFT)

        # إطار اختيار مسار الحفظ
        path_frame = ttk.Frame(torrent_frame)
        path_frame.pack(fill=tk.X, padx=10, pady=5)

        ttk.Label(path_frame, text=self.translations[self.language]['download_path'], font=("Segoe UI", 10)).pack(side=tk.LEFT)
        self.torrent_path_var = tk.StringVar(value=self.save_path)
        path_entry = ttk.Entry(path_frame, textvariable=self.torrent_path_var, width=50)
        path_entry.pack(side=tk.LEFT, padx=5)

        def browse_save_path():
            folder = filedialog.askdirectory()
            if folder:
                self.torrent_path_var.set(folder)

        ttk.Button(path_frame, text="...", command=browse_save_path, style="Accent.TButton").pack(side=tk.LEFT)

        # إطار عرض الملفات
        files_frame = ttk.LabelFrame(torrent_frame, text=self.translations[self.language]['torrent_files'])
        files_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        self.torrent_files_tree = ttk.Treeview(files_frame, columns=("name", "size"), show="headings")
        self.torrent_files_tree.heading("name", text=self.translations[self.language]['filename'])
        self.torrent_files_tree.heading("size", text=self.translations[self.language]['size'])
        self.torrent_files_tree.column("name", width=400)
        self.torrent_files_tree.column("size", width=100)
        self.torrent_files_tree.pack(fill=tk.BOTH, expand=True)

        self.torrent_selected_files = []  # لتخزين الملفات المختارة

        def load_torrent_files():
            """تحميل وعرض ملفات التورنت."""
            torrent_path = self.torrent_var.get()
            if not torrent_path:
                messagebox.showwarning(
                    self.translations[self.language]["warning"],
                    self.translations[self.language]["no_selected_urls"]
                )
                return

            try:
                ses = lt.session({'listen_interfaces': '0.0.0.0:6881'})
                if torrent_path.endswith('.torrent'):
                    torrent_info = lt.torrent_info(torrent_path)
                else:  # Magnet link
                    params = lt.parse_magnet_uri(torrent_path)
                    torrent_info = lt.torrent_info(params)
                    ses.add_torrent(params)

                self.torrent_files_tree.delete(*self.torrent_files_tree.get_children())
                self.torrent_selected_files.clear()
                for i, f in enumerate(torrent_info.files()):
                    size_mb = f.size / (1024 * 1024)
                    self.torrent_files_tree.insert("", "end", values=(f.path, f"{size_mb:.2f} MB"), tags=(str(i),))
                ses.close()
            except Exception as e:
                messagebox.showerror(
                    self.translations[self.language]["error"],
                    f"فشل تحميل ملفات التورنت: {str(e)}"
                )

        ttk.Button(torrent_frame, text=self.translations[self.language]['select_files'], command=load_torrent_files, style="Accent.TButton").pack(pady=10)

        def on_file_select(event):
            """تحديث قائمة الملفات المختارة."""
            self.torrent_selected_files.clear()
            for item in self.torrent_files_tree.selection():
                file_index = int(self.torrent_files_tree.item(item, 'tags')[0])
                self.torrent_selected_files.append(file_index)

        self.torrent_files_tree.bind('<<TreeviewSelect>>', on_file_select)

        # إطار أزرار التحكم
        control_frame = ttk.Frame(torrent_frame)
        control_frame.pack(fill=tk.X, padx=10, pady=10)

        def start_torrent():
            """بدء تحميل التورنت."""
            torrent_path = self.torrent_var.get()
            save_path = self.torrent_path_var.get()
            if not torrent_path:
                messagebox.showerror(
                    self.translations[self.language]["error"],
                    self.translations[self.language]["no_selected_urls"]
                )
                return
            if not os.path.isdir(save_path):
                messagebox.showerror(
                    self.translations[self.language]["error"],
                    self.translations[self.language]["invalid_path"]
                )
                return

            # فحص الفيروسات
            if not self.scan_torrent_for_viruses(torrent_path):
                messagebox.showerror(
                    self.translations[self.language]["error"],
                    self.translations[self.language]["virus_detected"]
                )
                return

            if not self.torrent_selected_files:
                messagebox.showwarning(
                    self.translations[self.language]["warning"],
                    self.translations[self.language]["no_files_selected"]
                )
                return

            url_hash = hashlib.md5(torrent_path.encode('utf-8')).hexdigest()
            task_id = f"torrent_{url_hash}"
            self.download_threads[task_id] = {
                'url': torrent_path,
                'completed': False,
                'cancel': False,
                'pause': False,
                'pause_event': threading.Event(),
                'ratelimit': None,
                'thread': None,
                'downloaded_bytes': 0,
                'start_time': time.time(),
                'filepath': save_path,
                'selected_files': self.torrent_selected_files,
                'is_torrent': True,
                'progress_item': None  # لتتبع العنصر في Treeview
            }
            self.download_threads[task_id]['pause_event'].set()

            # إضافة التحميل إلى Treeview
            self.torrent_progress_tree.insert("", "end", values=(
                task_id,
                os.path.basename(torrent_path),
                "0.00 MB",
                "0.00 MB/s",
                save_path,
                "0.0%"
            ))
            self.download_threads[task_id]['progress_item'] = self.torrent_progress_tree.get_children()[-1]

            # إضافة أزرار التحكم
            self.add_torrent_control_buttons(task_id)

            threading.Thread(target=self.download_torrent, args=(task_id, torrent_path, save_path, self.torrent_selected_files), daemon=True).start()
            messagebox.showinfo(
                self.translations[self.language]["info"],
                self.translations[self.language]["added_to_queue"].format(torrent_path)
            )

        start_button = ttk.Button(
            control_frame,
            text=self.translations[self.language]['start_download'],
            command=start_torrent,
            style="Accent.TButton"
        )
        start_button.pack(side=tk.LEFT, padx=5)
        self.add_tooltip(start_button, self.translations[self.language]["start_download"])

        # إطار تتبع التقدم
        progress_frame = ttk.LabelFrame(torrent_frame, text=self.translations[self.language]['progress'])
        progress_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        self.torrent_progress_tree = ttk.Treeview(
            progress_frame,
            columns=("id", "name", "size", "speed", "path", "progress"),
            show="headings"
        )
        self.torrent_progress_tree.heading("id", text=self.translations[self.language]["url"])
        self.torrent_progress_tree.heading("name", text=self.translations[self.language]["filename"])
        self.torrent_progress_tree.heading("size", text=self.translations[self.language]["size"])
        self.torrent_progress_tree.heading("speed", text=self.translations[self.language]["download_speed"])
        self.torrent_progress_tree.heading("path", text=self.translations[self.language]["download_path"])
        self.torrent_progress_tree.heading("progress", text=self.translations[self.language]["progress"])
        self.torrent_progress_tree.column("id", width=100)
        self.torrent_progress_tree.column("name", width=200)
        self.torrent_progress_tree.column("size", width=100)
        self.torrent_progress_tree.column("speed", width=100)
        self.torrent_progress_tree.column("path", width=200)
        self.torrent_progress_tree.column("progress", width=100)
        self.torrent_progress_tree.pack(fill=tk.BOTH, expand=True)
    def add_torrent_control_buttons(self, task_id):
        """إضافة أزرار التحكم (إيقاف، استئناف، إلغاء) لتحميل التورنت."""
        control_frame = ttk.Frame(self.torrent_progress_tree)
        control_frame_id = self.torrent_progress_tree.insert(
            self.download_threads[task_id]['progress_item'],
            "end",
            values=("", "", "", "", "", "")
        )

        pause_button = ttk.Button(
            control_frame,
            text=self.translations[self.language]['pause_download'],
            command=lambda: self.pause_torrent_download(task_id, pause_button, resume_button),
            style="Accent.TButton"
        )
        pause_button.pack(side=tk.LEFT, padx=2)

        resume_button = ttk.Button(
            control_frame,
            text=self.translations[self.language]['resume_download'],
            command=lambda: self.resume_torrent_download(task_id, pause_button, resume_button),
            style="Accent.TButton",
            state="disabled"
        )
        resume_button.pack(side=tk.LEFT, padx=2)

        cancel_button = ttk.Button(
            control_frame,
            text=self.translations[self.language]['cancel_download'],
            command=lambda: self.cancel_torrent_download(task_id),
            style="Accent.TButton"
        )
        cancel_button.pack(side=tk.LEFT, padx=2)

        self.torrent_progress_tree.window_create(control_frame_id, window=control_frame)

    def update_ui_based_on_url(self, event=None):
        url = self.url_entry.get().strip()
        if self.is_valid_url(url):
            self.quality_button.config(state="normal")
            self.start_download_button.config(state="normal")
            self.extract_links_button.config(state="normal")
        else:
            self.quality_button.config(state="disabled")
            self.start_download_button.config(state="disabled")
            self.extract_links_button.config(state="disabled")

    def create_download_tab(self):
        self.download_tab = ttk.Frame(self.notebook, style="TFrame")
        self.notebook.add(self.download_tab,
                         text=self.translations[self.language]["single_download"])

        # Input Frame (URL Input) - Original Order
        self.input_frame = ttk.LabelFrame(
            self.download_tab,
            text=self.translations[self.language]["url_label"],
            padding=6
        )
        self.input_frame.pack(fill=tk.X, padx=5, pady=6)

        self.url_label = ttk.Label(
            self.input_frame,
            text=self.translations[self.language]["url_label"]
        )
        self.url_label.grid(row=0, column=0, sticky="w", padx=5, pady=6)
        self.url_entry = ttk.Entry(
            self.input_frame,
            width=60,
            font=("Segoe UI", 10)
        )
        self.url_entry.grid(row=0, column=1, padx=5, pady=6, sticky="ew")

        self.extract_links_button = ttk.Button(
            self.input_frame,
            text=self.translations[self.language]["extract_links"],
            command=self.extract_video_links,
            style="Accent.TButton"
        )
        self.extract_links_button.grid(
            row=1, column=0, padx=5, pady=6, sticky="w")

        self.quality_button = ttk.Button(
            self.input_frame,
            text=self.translations[self.language]["quality_button"],
            command=self.fetch_qualities,
            style="Accent.TButton"
        )
        self.quality_button.grid(row=1, column=1, padx=5, pady=6, sticky="e")

        # Filename Frame (Path Selection)
        self.filename_frame = ttk.LabelFrame(
            self.download_tab,
            text=self.translations[self.language]["filename_label"],
            padding=6
        )
        self.filename_frame.pack(fill=tk.X, padx=5, pady=4)

        self.path_label = ttk.Label(
            self.filename_frame,
            text=self.save_path,
            wraplength=500
        )
        self.path_label.pack(side=tk.LEFT, padx=5)
        self.select_folder_button = ttk.Button(
            self.filename_frame,
            text=self.translations[self.language]["select_folder"],
            command=self.select_directory,
            style="Accent.TButton"
        )
        self.select_folder_button.pack(side=tk.LEFT, padx=5)

        # Quality Frame
        self.quality_frame = ttk.LabelFrame(
            self.download_tab,
            text=self.translations[self.language]["quality_label"],
            padding=6
        )
        self.quality_frame.pack(fill=tk.X, padx=5, pady=6)

        self.quality_subframe = ttk.Frame(self.quality_frame, style="TFrame")
        self.quality_subframe.pack(anchor="w", fill=tk.X)

        self.quality_label = ttk.Label(
            self.quality_subframe,
            text=self.translations[self.language]["quality_label"]
        )
        self.quality_label.pack(side=tk.LEFT, padx=5, pady=6)

        self.quality_combo = ttk.Combobox(
            self.quality_subframe,
            state="readonly",
            width=70,
            font=("Segoe UI", 9)
        )
        self.quality_combo.pack(side=tk.LEFT, padx=5, pady=6)

        self.start_download_button = ttk.Button(
            self.quality_subframe,
            text=self.translations[self.language]["start_download"],
            command=self.start_download,
            style="Accent.TButton"
        )
        self.start_download_button.pack(side=tk.RIGHT, padx=5, pady=6)

        self.advanced_frame = ttk.Frame(self.quality_subframe, style="TFrame")
        self.advanced_frame.pack(side=tk.LEFT, padx=5, pady=6)

        self.download_type_label = ttk.Label(
            self.advanced_frame,
            text="نوع التنزيل:"
        )
        self.download_type_label.pack(side=tk.LEFT, padx=5)
        self.download_type_combo = ttk.Combobox(
            self.advanced_frame,
            values=[
                self.translations[self.language]["video_only"],
                self.translations[self.language]["audio_only"],
                self.translations[self.language]["video_with_subtitles"]
            ],
            state="readonly",
            width=20
        )
        self.download_type_combo.pack(side=tk.LEFT, padx=5)
        self.download_type_combo.current(0)

        # General Frame
        self.general_frame = ttk.LabelFrame(
            self.download_tab,
            text=self.translations[self.language]["general_url_label"],
            padding=6
        )
        self.general_frame.pack(fill=tk.X, padx=5, pady=4)

        self.general_url_label = ttk.Label(
            self.general_frame,
            text=self.translations[self.language]["general_url_label"]
        )
        self.general_url_label.grid(
            row=0, column=0, sticky="w", padx=5, pady=6)
        self.general_url_entry = ttk.Entry(
            self.general_frame,
            width=70,
            font=("Segoe UI", 10)
        )
        self.general_url_entry.grid(
            row=0, column=1, padx=5, pady=6, sticky="ew")

        self.start_general_button = ttk.Button(
            self.general_frame,
            text=self.translations[self.language]["start_download"],
            command=self.start_general_download,
            style="Accent.TButton"
        )
        self.start_general_button.grid(row=1, column=1, pady=6, sticky="e")

        self.url_entry.bind("<KeyRelease>", self.update_ui_based_on_url)
        self.input_frame.columnconfigure(1, weight=1)
        self.quality_frame.columnconfigure(1, weight=1)
        self.general_frame.columnconfigure(1, weight=1)
    def start_torrent_download(self):
        """بدء تحميل تورنت مع واجهة لاختيار ملفات وإعدادات."""
        # إنشاء نافذة لتحميل التورنت
        torrent_window = tk.Toplevel(self.root)
        torrent_window.title(self.translations[self.language]['select_torrent'])
        torrent_window.geometry("600x400")
        torrent_window.transient(self.root)
        torrent_window.grab_set()

        # إطار إدخال رابط Magnet أو ملف تورنت
        input_frame = ttk.Frame(torrent_window)
        input_frame.pack(fill=tk.X, padx=5, pady=5)

        ttk.Label(input_frame, text=self.translations[self.language]['select_torrent']).pack(side=tk.LEFT)
        torrent_var = tk.StringVar()
        torrent_entry = ttk.Entry(input_frame, textvariable=torrent_var, width=50)
        torrent_entry.pack(side=tk.LEFT, padx=5)

        def browse_torrent_file():
            file_path = filedialog.askopenfilename(filetypes=[("Torrent files", "*.torrent")])
            if file_path:
                torrent_var.set(file_path)

        ttk.Button(input_frame, text="...", command=browse_torrent_file).pack(side=tk.LEFT)

        # إطار اختيار مسار الحفظ
        path_frame = ttk.Frame(torrent_window)
        path_frame.pack(fill=tk.X, padx=5, pady=5)

        ttk.Label(path_frame, text=self.translations[self.language]['download_path']).pack(side=tk.LEFT)
        path_var = tk.StringVar(value=self.save_path)
        ttk.Entry(path_frame, textvariable=path_var, width=50).pack(side=tk.LEFT, padx=5)

        def browse_save_path():
            folder = filedialog.askdirectory()
            if folder:
                path_var.set(folder)

        ttk.Button(path_frame, text="...", command=browse_save_path).pack(side=tk.LEFT)

        # إطار عرض الملفات
        files_frame = ttk.LabelFrame(torrent_window, text=self.translations[self.language]['torrent_files'])
        files_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        files_tree = ttk.Treeview(files_frame, columns=("name", "size"), show="headings")
        files_tree.heading("name", text=self.translations[self.language]['filename'])
        files_tree.heading("size", text=self.translations[self.language]['size'])
        files_tree.column("name", width=300)
        files_tree.column("size", width=100)
        files_tree.pack(fill=tk.BOTH, expand=True)

        selected_files = []  # لتخزين الملفات المختارة

        def load_torrent_files():
            """تحميل وعرض ملفات التورنت."""
            torrent_path = torrent_var.get()
            if not torrent_path:
                messagebox.showwarning(
                    self.translations[self.language]["warning"],
                    self.translations[self.language]["no_selected_urls"]
                )
                return

            ses = lt.session({'listen_interfaces': '0.0.0.0:6881'})
            if torrent_path.endswith('.torrent'):
                torrent_info = lt.torrent_info(torrent_path)
            else:  # Magnet link
                params = lt.parse_magnet_uri(torrent_path)
                torrent_info = lt.torrent_info(params)
                ses.add_torrent(params)

            files_tree.delete(*files_tree.get_children())
            selected_files.clear()
            for i, f in enumerate(torrent_info.files()):
                size_mb = f.size / (1024 * 1024)
                files_tree.insert("", "end", values=(f.path, f"{size_mb:.2f} MB"), tags=(str(i),))
            ses.close()

        ttk.Button(torrent_window, text=self.translations[self.language]['select_files'], command=load_torrent_files).pack(pady=5)

        def on_file_select(event):
            """تحديث قائمة الملفات المختارة."""
            selected_files.clear()
            for item in files_tree.selection():
                file_index = int(files_tree.item(item, 'tags')[0])
                selected_files.append(file_index)

        files_tree.bind('<<TreeviewSelect>>', on_file_select)

        # إطار أزرار التحكم
        control_frame = ttk.Frame(torrent_window)
        control_frame.pack(fill=tk.X, padx=5, pady=5)

        def start_torrent():
            torrent_path = torrent_var.get()
            save_path = path_var.get()
            if not torrent_path or not os.path.isdir(save_path):
                messagebox.showerror(
                    self.translations[self.language]["error"],
                    self.translations[self.language]["invalid_path"]
                )
                return

            # فحص الفيروسات
            if not self.scan_torrent_for_viruses(torrent_path):
                messagebox.showerror(
                    self.translations[self.language]["error"],
                    self.translations[self.language]["virus_detected"]
                )
                return

            if not selected_files:
                messagebox.showwarning(
                    self.translations[self.language]["warning"],
                    self.translations[self.language]["no_files_selected"]
                )
                return

            url_hash = hashlib.md5(torrent_path.encode('utf-8')).hexdigest()
            task_id = f"torrent_{url_hash}"
            self.download_threads[task_id] = {
                'url': torrent_path,
                'completed': False,
                'cancel': False,
                'pause': False,
                'pause_event': threading.Event(),
                'ratelimit': None,
                'thread': None,
                'downloaded_bytes': 0,
                'start_time': time.time(),
                'filepath': save_path,
                'selected_files': selected_files,
                'is_torrent': True
            }
            self.download_threads[task_id]['pause_event'].set()

            threading.Thread(target=self.download_torrent, args=(task_id, torrent_path, save_path, selected_files), daemon=True).start()
            torrent_window.destroy()

        ttk.Button(control_frame, text=self.translations[self.language]['start_download'], command=start_torrent).pack(side=tk.LEFT, padx=5)

    def download_torrent(self, task_id, torrent_path, save_path, selected_files):
        """تحميل التورنت مع دعم اختيار الملفات ومنع الـ seeding."""
        try:
            ses = lt.session({
                'listen_interfaces': '0.0.0.0:6881',
                'enable_dht': True,
                'enable_lsd': True,
                'enable_natpmp': True,
                'enable_upnp': True,
                'upload_rate_limit': 0  # منع الـ seeding
            })

            if torrent_path.endswith('.torrent'):
                torrent_info = lt.torrent_info(torrent_path)
                params = {'ti': torrent_info, 'save_path': save_path}
            else:  # Magnet link
                params = lt.parse_magnet_uri(torrent_path)
                params.save_path = save_path

            handle = ses.add_torrent(params)
            handle.set_upload_limit(0)  # منع الـ seeding

            # تحديد الملفات المطلوب تحميلها
            priorities = [0] * torrent_info.num_files()  # 0 = لا تحميل
            for idx in selected_files:
                priorities[idx] = 1  # 1 = تحميل
            handle.prioritize_files(priorities)

            # التحقق من الملفات الموجودة واستكمال التحميل
            handle.force_recheck()  # التحقق من الملفات الموجودة

            self.download_threads[task_id]['thread'] = threading.current_thread()

            # إضافة عنصر التحميل إلى torrent_progress_tree
            if 'progress_item' not in self.download_threads[task_id]:
                progress_item = self.torrent_progress_tree.insert("", "end", values=(
                    task_id,
                    os.path.basename(torrent_path),
                    "0.00 MB",
                    "0.00 MB/s",
                    save_path,
                    "0.0%"
                ))
                self.download_threads[task_id]['progress_item'] = progress_item
                # إضافة أزرار التحكم
                self.add_torrent_control_buttons(task_id, progress_item)

            while not self.download_threads[task_id]['completed'] and not self.download_threads[task_id]['cancel']:
                if not self.download_threads[task_id]['pause_event'].is_set():
                    handle.pause()
                else:
                    handle.resume()

                status = handle.status()
                progress = status.progress * 100
                speed = status.download_rate / (1024 * 1024)  # MB/s
                self.download_threads[task_id]['downloaded_bytes'] = status.total_done

                # تحديث واجهة التقدم في torrent_progress_tree
                progress_item = self.download_threads[task_id].get('progress_item')
                if progress_item and progress_item in self.torrent_progress_tree.get_children():
                    self.torrent_progress_tree.item(progress_item, values=(
                        task_id,
                        os.path.basename(torrent_path),
                        f"{status.total_wanted / (1024 * 1024):.2f} MB",
                        f"{speed:.2f} MB/s",
                        save_path,
                        f"{progress:.1f}%"
                    ))

                logging.debug(f"تورنت {task_id}: {progress:.1f}% - {speed:.2f} MB/s")
                time.sleep(1)

                if status.progress >= 1.0:  # التحميل اكتمل
                    self.download_threads[task_id]['completed'] = True
                    handle.pause()
                    ses.remove_torrent(handle)
                    logging.info(f"اكتمل تحميل التورنت {task_id}")
                    break

            if self.download_threads[task_id]['cancel']:
                ses.remove_torrent(handle)
                logging.info(f"تم إلغاء تحميل التورنت {task_id}")

            # إزالة العنصر من torrent_progress_tree عند الإلغاء أو الاكتمال
            if progress_item and progress_item in self.torrent_progress_tree.get_children():
                self.torrent_progress_tree.delete(progress_item)

            ses.close()

        except Exception as e:
            logging.error(f"فشل تحميل التورنت {task_id}: {str(e)}")
            self.download_threads[task_id]['completed'] = True
            # إزالة العنصر من torrent_progress_tree في حالة الخطأ
            progress_item = self.download_threads[task_id].get('progress_item')
            if progress_item and progress_item in self.torrent_progress_tree.get_children():
                self.torrent_progress_tree.delete(progress_item)
    def scan_torrent_for_viruses(self, torrent_path):
        """فحص ملف تورنت أو رابط Magnet باستخدام VirusTotal."""
        if not self.virus_total_api_key:
            logging.warning("مفتاح VirusTotal API غير مُعرف. تخطي الفحص.")
            return True

        try:
            if torrent_path.endswith('.torrent'):
                with open(torrent_path, 'rb') as f:
                    files = {'file': (os.path.basename(torrent_path), f)}
                    response = requests.post(
                        'https://www.virustotal.com/api/v3/files',
                        files=files,
                        headers={'x-apikey': self.virus_total_api_key}
                    )
            else:  # Magnet link
                response = requests.post(
                    'https://www.virustotal.com/api/v3/urls',
                    data={'url': torrent_path},
                    headers={'x-apikey': self.virus_total_api_key}
                )

            result = response.json()
            if response.status_code == 200:
                stats = result['data']['attributes']['last_analysis_stats']
                if stats['malicious'] > 0 or stats['suspicious'] > 0:
                    logging.warning(f"تم اكتشاف تهديد في {torrent_path}: {stats}")
                    return False
                logging.info(f"فحص VirusTotal: {torrent_path} آمن")
                return True
            else:
                logging.error(f"فشل فحص VirusTotal: {result.get('error', 'غير معروف')}")
                return True  # افتراض الأمان لو فشل الفحص
        except Exception as e:
            logging.error(f"خطأ أثناء فحص VirusTotal: {str(e)}")
            return True

    def pause_torrent_download(self, task_id, pause_button, resume_button):
        """إيقاف تحميل التورنت مؤقتًا."""
        if task_id in self.download_threads and self.download_threads[task_id].get('is_torrent'):
            self.download_threads[task_id]['pause'] = True
            self.download_threads[task_id]['pause_event'].clear()
            pause_button.configure(state='disabled')
            resume_button.configure(state='normal')
            logging.debug(f"تم إيقاف تحميل التورنت {task_id} مؤقتًا")

    def resume_torrent_download(self, task_id, pause_button, resume_button):
        """استئناف تحميل التورنت."""
        if task_id in self.download_threads and self.download_threads[task_id].get('is_torrent'):
            self.download_threads[task_id]['pause'] = False
            self.download_threads[task_id]['pause_event'].set()
            pause_button.configure(state='normal')
            resume_button.configure(state='disabled')
            logging.debug(f"تم استئناف تحميل التورنت {task_id}")

    def cancel_torrent_download(self, task_id):
        """إلغاء تحميل التورنت."""
        if task_id in self.download_threads and self.download_threads[task_id].get('is_torrent'):
            self.download_threads[task_id]['cancel'] = True
            self.download_threads[task_id]['pause_event'].set()  # للسماح بالخروج من الحلقة
            logging.debug(f"تم إلغاء تحميل التورنت {task_id}")

    def create_batch_tab(self):
        """Create the batch download tab."""
        style = ttk.Style()
        style.configure("Accent.TButton", font=("Segoe UI", 10), background="#4CAF50", foreground="white")
        style.map("Accent.TButton", background=[("active", "#45a049")])

        batch_frame = ttk.Frame(self.notebook)
        self.notebook.add(batch_frame, text=self.translations[self.language].get("batch_download", "Batch Download"))

        # استخدام grid بدلاً من pack
        batch_frame.grid_columnconfigure(0, weight=1)
        batch_frame.grid_rowconfigure(3, weight=1)  # الصف الخاص بالـ Treeview يتوسع

        # URLs input
        urls_label = ttk.Label(batch_frame, text=self.translations[self.language].get("enter_urls", "Enter URLs (one per line)"))
        urls_label.grid(row=0, column=0, sticky="w", padx=5, pady=5)
        self.batch_urls_text = tk.Text(batch_frame, height=5, width=50)  # الارتفاع 5
        self.batch_urls_text.grid(row=1, column=0, sticky="ew", padx=5, pady=5)

        # Scrollbar لمربع النصوص
        urls_scroll = ttk.Scrollbar(batch_frame, orient="vertical", command=self.batch_urls_text.yview)
        urls_scroll.grid(row=1, column=1, sticky="ns", pady=5)
        self.batch_urls_text.configure(yscrollcommand=urls_scroll.set)

        # إطار الأزرار أسفل مربع النصوص
        buttons_frame = ttk.Frame(batch_frame)
        buttons_frame.grid(row=2, column=0, sticky="ew", padx=5, pady=5)

        # Add URL button
        add_button = ttk.Button(
            buttons_frame,
            text=self.translations[self.language].get("add_url", "Add URL"),
            command=self.add_batch_url_with_quality,
            style="Accent.TButton"
        )
        add_button.pack(side=tk.LEFT, padx=5)

        # Fetch qualities button
        fetch_button = ttk.Button(
            buttons_frame,
            text=self.translations[self.language].get("fetch_quality", "Fetch Qualities"),
            command=self.fetch_batch,
            style="Accent.TButton"
        )
        fetch_button.pack(side=tk.LEFT, padx=5)

        # Retry fetch qualities button
        retry_qualities_button = ttk.Button(
            buttons_frame,
            text=self.translations[self.language].get("retry_fetch_qualities", "Retry Fetch Qualities"),
            command=self.retry_fetch_qualities,
            style="Accent.TButton"
        )
        retry_qualities_button.pack(side=tk.LEFT, padx=5)

        # Clear URLs button
        clear_button = ttk.Button(
            buttons_frame,
            text=self.translations[self.language].get("clear_urls", "Clear URLs"),
            command=self.clear_batch_urls,
            style="Accent.TButton"
        )
        clear_button.pack(side=tk.LEFT, padx=5)

        # Start batch download button
        self.start_batch_button = ttk.Button(
            buttons_frame,
            text=self.translations[self.language].get("start_batch_download", "Start Batch Download"),
            command=self.start_batch_download,
            style="Accent.TButton"
        )
        self.start_batch_button.pack(side=tk.LEFT, padx=5)

        # Progress bar for fetching qualities
        self.batch_progress_bar = ttk.Progressbar(batch_frame, mode="indeterminate")
        self.batch_progress_bar.grid(row=3, column=0, sticky="ew", padx=5, pady=5)

        # Save path
        path_frame = ttk.Frame(batch_frame)
        path_frame.grid(row=4, column=0, sticky="ew", padx=5, pady=5)
        path_label = ttk.Label(path_frame, text=self.translations[self.language].get("save_path", "Save Path"))
        path_label.pack(side=tk.LEFT)
        self.batch_path_var = tk.StringVar(value=self.batch_save_path)
        path_entry = ttk.Entry(path_frame, textvariable=self.batch_path_var)
        path_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
        browse_button = ttk.Button(
            path_frame,
            text=self.translations[self.language].get("browse", "Browse"),
            command=self.select_batch_directory,
            style="Accent.TButton"
        )
        browse_button.pack(side=tk.LEFT)

        # Treeview لعرض روابط التنزيل الجماعي
        tree_frame = ttk.Frame(batch_frame)
        tree_frame.grid(row=5, column=0, sticky="nsew", padx=5, pady=5)
        tree_frame.grid_columnconfigure(0, weight=1)
        tree_frame.grid_rowconfigure(0, weight=1)

        self.batch_tree = ttk.Treeview(
            tree_frame,
            columns=("url", "title", "duration", "quality", "size"),
            show="headings",
            selectmode="extended",
            height=5  # الارتفاع 5
        )
        self.batch_tree.heading("url", text=self.translations[self.language].get("url", "URL"))
        self.batch_tree.heading("title", text=self.translations[self.language].get("title", "Title"))
        self.batch_tree.heading("duration", text=self.translations[self.language].get("duration", "Duration"))
        self.batch_tree.heading("quality", text=self.translations[self.language].get("quality", "Quality"))
        self.batch_tree.heading("size", text=self.translations[self.language].get("size", "Size"))
        self.batch_tree.column("url", width=200)
        self.batch_tree.column("title", width=200)
        self.batch_tree.column("duration", width=80)
        self.batch_tree.column("quality", width=150)
        self.batch_tree.column("size", width=100)
        self.batch_tree.grid(row=0, column=0, sticky="nsew")

        # Scrollbar للـ Treeview
        tree_scroll = ttk.Scrollbar(tree_frame, orient="vertical", command=self.batch_tree.yview)
        tree_scroll.grid(row=0, column=1, sticky="ns")
        self.batch_tree.configure(yscrollcommand=tree_scroll.set)

        # Bind click event for quality selection
        self.batch_tree.bind("<Button-1>", self.handle_tree_click)

        # Download options
        options_frame = ttk.Frame(batch_frame)
        options_frame.grid(row=6, column=0, sticky="ew", padx=5, pady=5)
        self.mp3_var = tk.BooleanVar(value=False)
        mp3_check = ttk.Checkbutton(
            options_frame,
            text=self.translations[self.language].get("convert_to_mp3", "Convert to MP3"),
            variable=self.mp3_var
        )
        mp3_check.pack(side=tk.LEFT, padx=5)
        self.subtitles_var = tk.BooleanVar(value=False)
        subtitles_check = ttk.Checkbutton(
            options_frame,
            text=self.translations[self.language].get("download_subtitles", "Download Subtitles"),
            variable=self.subtitles_var
        )
        subtitles_check.pack(side=tk.LEFT, padx=5)

        # Select all and deselect all buttons
        select_frame = ttk.Frame(batch_frame)
        select_frame.grid(row=7, column=0, sticky="ew", padx=5, pady=5)
        select_all_button = ttk.Button(
            select_frame,
            text=self.translations[self.language].get("select_all", "Select All"),
            command=self.select_all_batch,
            style="Accent.TButton"
        )
        select_all_button.pack(side=tk.LEFT, padx=5)
        deselect_all_button = ttk.Button(
            select_frame,
            text=self.translations[self.language].get("deselect_all", "Deselect All"),
            command=self.deselect_all_batch,
            style="Accent.TButton"
        )
        deselect_all_button.pack(side=tk.LEFT, padx=5)
    def update_tree_status(self, tree_item_id, status):
        """Update the status of a Treeview item in the batch download tab."""
        try:
            item_values = self.batch_tree.item(tree_item_id, 'values')
            new_values = list(item_values)
            new_values[4] = status
            self.batch_tree.item(tree_item_id, values=new_values)
            logging.debug(f"تم تحديث حالة العنصر {tree_item_id} إلى: {status}")
        except Exception as e:
            logging.error(f"فشل تحديث حالة العنصر {tree_item_id}: {e}")

    def select_all_batch(self):
        """Select all items in the batch tree."""
        for item in self.batch_tree.get_children():
            self.batch_tree.selection_add(item)

    def deselect_all_batch(self):
        """Deselect all items in the batch tree."""
        for item in self.batch_tree.get_children():
            self.batch_tree.selection_remove(item)

    def create_history_tab(self):
        self.history_tab = ttk.Frame(self.notebook, style="TFrame")
        self.notebook.add(self.history_tab,
     text=self.translations[self.language]["history"])

        self.history_search_frame = ttk.Frame(self.history_tab, style="TFrame")
        self.history_search_frame.pack(fill=tk.X, padx=5, pady=6)

        self.history_search_label = ttk.Label(
            self.history_search_frame,
            text=self.translations[self.language]["search_history"]
        )
        self.history_search_label.pack(side=tk.LEFT, padx=5)
        self.search_entry = ttk.Entry(
    self.history_search_frame, width=50, font=(
        "Segoe UI", 10))
        self.search_entry.pack(side=tk.LEFT, padx=5)
        self.search_entry.bind("<KeyRelease>", self.search_history)
        self.history_clear_button = ttk.Button(
            self.history_search_frame,
            text=self.translations[self.language]["clear_history"],
            command=self.clear_history,
            style="Accent.TButton"
        )
        self.history_clear_button.pack(side=tk.RIGHT, padx=5)

        self.history_tree_frame = ttk.Frame(self.history_tab, style="TFrame")
        self.history_tree_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=6)

        self.history_columns = (
            self.translations[self.language]["time"],
            self.translations[self.language]["url_label"],
            self.translations[self.language]["type"],
            self.translations[self.language]["status"],
            self.translations[self.language]["details"]
        )
        self.history_tree = ttk.Treeview(
            self.history_tree_frame,
            columns=self.history_columns,
            show="headings",
            selectmode="browse"
        )
        for col in self.history_columns:
            self.history_tree.heading(col, text=col)
            self.history_tree.column(col, width=150, anchor="w")
        self.history_tree.pack(fill=tk.BOTH, expand=True)

        self.history_tree.bind("<Double-1>", self.on_history_double_click)

    def create_incomplete_tab(self):
        self.incomplete_tab = ttk.Frame(self.notebook, style="TFrame")
        self.notebook.add(self.incomplete_tab,
     text=self.translations[self.language]["incomplete"])

        self.incomplete_button_frame = ttk.Frame(
            self.incomplete_tab, style="TFrame")
        self.incomplete_button_frame.pack(fill=tk.X, padx=5, pady=6)

        self.incomplete_resume_button = ttk.Button(
            self.incomplete_button_frame,
            text=self.translations[self.language]["resume"],
            command=self.resume_incomplete,
            style="Accent.TButton"
        )
        self.incomplete_resume_button.pack(side=tk.LEFT, padx=5)
        self.incomplete_clear_button = ttk.Button(
            self.incomplete_button_frame,
            text=self.translations[self.language]["clear"],
            command=self.clear_incomplete,
            style="Accent.TButton"
        )
        self.incomplete_clear_button.pack(side=tk.LEFT, padx=5)

        self.incomplete_tree_frame = ttk.Frame(
            self.incomplete_tab, style="TFrame")
        self.incomplete_tree_frame.pack(
    fill=tk.BOTH, expand=True, padx=5, pady=6)

        self.incomplete_columns = (
            self.translations[self.language]["time"],
            self.translations[self.language]["url_label"],
            self.translations[self.language]["filename"],
            self.translations[self.language]["details"]
        )
        self.incomplete_tree = ttk.Treeview(
            self.incomplete_tree_frame,
            columns=self.incomplete_columns,
            show="headings",
            selectmode="browse"
        )
        for col in self.incomplete_columns:
            self.incomplete_tree.heading(col, text=col)
            self.incomplete_tree.column(col, width=200, anchor="w")
        self.incomplete_tree.pack(fill=tk.BOTH, expand=True)

        self.update_incomplete_list()

    def create_stats_tab(self):
        self.stats_tab = ttk.Frame(self.notebook, style="TFrame")
        self.notebook.add(self.stats_tab,
     text=self.translations[self.language]["stats"])

        self.stats_frame = ttk.Frame(self.stats_tab, style="TFrame")
        self.stats_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=6)

        self.stats_label = ttk.Label(
            self.stats_frame,
            text=self.get_stats_text(),
            font=("Segoe UI", 12),
            foreground="#1E3A8A"
        )
        self.stats_label.pack(anchor="w", padx=10, pady=10)

    def create_playlist_tab(self):
        """Create the playlist download tab."""
        playlist_frame = ttk.Frame(self.notebook)
        self.notebook.add(playlist_frame, text=self.translations[self.language]["playlist_download"])
        self.playlist_tab = playlist_frame

        # استخدام grid بدلاً من pack
        playlist_frame.grid_columnconfigure(0, weight=1)
        playlist_frame.grid_rowconfigure(4, weight=1)  # الصف الخاص بالـ Treeview يتوسع

        # Playlist URL input
        ttk.Label(
            playlist_frame,
            text=self.translations[self.language]["playlist_url_label"],
            style="TLabel"
        ).grid(row=0, column=0, sticky="w", padx=10, pady=5)
        ttk.Entry(
            playlist_frame,
            textvariable=self.playlist_url_var,
            width=80,
            font=("Segoe UI", 10)
        ).grid(row=1, column=0, sticky="ew", padx=10, pady=5)

        # Quality selection
        quality_frame = ttk.Frame(playlist_frame)
        quality_frame.grid(row=2, column=0, sticky="ew", padx=10, pady=5)
        self.use_single_quality_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(
            quality_frame,
            text=self.translations[self.language]["use_single_quality"],
            variable=self.use_single_quality_var,
            command=self.toggle_quality_selection,
            style="TCheckbutton"
        ).pack(side=tk.LEFT, padx=5)
        self.single_quality_button = ttk.Button(
            quality_frame,
            text=self.translations[self.language]["select_quality"],
            command=self.select_single_quality,
            style="Accent.TButton"
        )
        self.single_quality_button.pack(side=tk.LEFT, padx=5)
        self.quality_combo_playlist = ttk.Combobox(
            quality_frame,
            state="readonly",
            width=50
        )
        self.quality_combo_playlist.pack(side=tk.LEFT, padx=5)
        self.quality_combo_playlist.bind(
            "<<ComboboxSelected>>",
            lambda e: self._update_single_quality_value()
        )
        self.single_quality_label = ttk.Label(
            quality_frame,
            text="",
            style="TLabel"
        )
        self.single_quality_label.pack(side=tk.LEFT, padx=5)
        ttk.Button(
            quality_frame,
            text=self.translations[self.language]["fetch_videos"],
            command=self.extract_playlist,
            style="Accent.TButton"
        ).pack(side=tk.LEFT, padx=5)

        # Save path
        ttk.Label(
            playlist_frame,
            text=self.translations[self.language]["playlist_path_label"],
            style="TLabel"
        ).grid(row=3, column=0, sticky="w", padx=10, pady=5)
        self.playlist_path_entry = ttk.Entry(
            playlist_frame,
            width=80,
            font=("Segoe UI", 10)
        )
        self.playlist_path_entry.insert(0, self.playlist_save_path)
        self.playlist_path_entry.grid(row=4, column=0, sticky="ew", padx=10, pady=5)
        ttk.Button(
            playlist_frame,
            text=self.translations[self.language]["select_folder"],
            command=lambda: self.select_directory(self.playlist_tab),
            style="Accent.TButton"
        ).grid(row=5, column=0, sticky="w", padx=10, pady=5)

        # Treeview لعرض قائمة التشغيل
        tree_frame = ttk.Frame(playlist_frame)
        tree_frame.grid(row=6, column=0, sticky="nsew", padx=10, pady=5)
        tree_frame.grid_columnconfigure(0, weight=1)
        tree_frame.grid_rowconfigure(0, weight=1)

        self.playlist_tree = ttk.Treeview(
            tree_frame,
            columns=("Index", "Title", "Duration", "Quality", "Filename", "PublishDate"),
            show="headings",
            height=5  # الارتفاع 5
        )
        self.playlist_tree.heading("Index", text="#")
        self.playlist_tree.heading("Title", text=self.translations[self.language]["title"])
        self.playlist_tree.heading("Duration", text=self.translations[self.language]["duration"])
        self.playlist_tree.heading("Quality", text=self.translations[self.language]["quality"])
        self.playlist_tree.heading("Filename", text=self.translations[self.language]["filename"])
        self.playlist_tree.heading("PublishDate", text=self.translations[self.language]["publish_date"])
        self.playlist_tree.column("Index", width=50)
        self.playlist_tree.column("Title", width=300)
        self.playlist_tree.column("Duration", width=100)
        self.playlist_tree.column("Quality", width=150)
        self.playlist_tree.column("Filename", width=200)
        self.playlist_tree.column("PublishDate", width=100)
        self.playlist_tree.grid(row=0, column=0, sticky="nsew")

        # Scrollbar للـ Treeview
        tree_scroll = ttk.Scrollbar(tree_frame, orient="vertical", command=self.playlist_tree.yview)
        tree_scroll.grid(row=0, column=1, sticky="ns")
        self.playlist_tree.configure(
            yscrollcommand=lambda *args: [tree_scroll.set(*args), self.update_combobox_position(*args)]
        )

        # ربط النقر على الجدول بدالة on_tree_click
        self.playlist_tree.bind("<Button-1>", self.on_tree_click)

        # إطار الأزرار في الأسفل
        button_frame = ttk.Frame(playlist_frame)
        button_frame.grid(row=7, column=0, sticky="ew", padx=10, pady=5)

        ttk.Button(
            button_frame,
            text=self.translations[self.language]["select_all"],
            command=self.select_all_videos,
            style="Accent.TButton"
        ).pack(side=tk.LEFT, padx=5)
        ttk.Button(
            button_frame,
            text=self.translations[self.language]["deselect_all"],
            command=self.deselect_all_videos,
            style="Accent.TButton"
        ).pack(side=tk.LEFT, padx=5)
        ttk.Button(
            button_frame,
            text=self.translations[self.language]["download_selected"],
            command=self.download_selected_videos,
            style="Accent.TButton"
        ).pack(side=tk.LEFT, padx=5)
        self.extract_audio_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(
            button_frame,
            text=self.translations[self.language]["audio_only"],
            variable=self.extract_audio_var,
            style="TCheckbutton"
        ).pack(side=tk.LEFT, padx=5)
        ttk.Button(
            button_frame,
            text=self.translations[self.language]["audio_only"],
            command=self.extract_audio_from_playlist,
            style="Accent.TButton"
        ).pack(side=tk.LEFT, padx=5)
        self.export_format_var = tk.StringVar(value="JSON")
        export_format_combo = ttk.Combobox(
            button_frame,
            textvariable=self.export_format_var,
            values=["JSON", "CSV"],
            state="readonly",
            width=10
        )
        export_format_combo.pack(side=tk.LEFT, padx=5)
        ttk.Button(
            button_frame,
            text=self.translations[self.language]["export_playlist_data"],
            command=self.export_playlist_data,
            style="Accent.TButton"
        ).pack(side=tk.LEFT, padx=5)
        ttk.Button(
            button_frame,
            text=self.translations[self.language]["export_subtitles"],
            command=self.export_subtitles,
            style="Accent.TButton"
        ).pack(side=tk.LEFT, padx=5)
    def toggle_quality_selection(self):
        import logging
        logging.basicConfig(level=logging.DEBUG)

        use_single_quality = self.use_single_quality_var.get()
        logging.debug(
    f"تبديل اختيار الجودة: {
        'موحدة' if use_single_quality else 'فردية'}")

        if not hasattr(
            self, 'single_quality_button') or self.single_quality_button is None:
            logging.error("self.single_quality_button غير معرف أو None")
            messagebox.showerror("خطأ", "فشل في تهيئة زر اختيار الجودة")
            return

        if use_single_quality:
            self.single_quality_button.config(state="normal")
            logging.debug("تم تفعيل زر اختيار الجودة الموحدة")
            # جلب الجودات الموحدة إذا لم تكن موجودة بالفعل
            if not self.playlist_available_qualities:
                self.fetch_qualities_for_playlist()
        else:
            self.single_quality_button.config(state="disabled")
            logging.debug("تم تعطيل زر اختيار الجودة الموحدة")
            # جلب الجودات المنفردة لكل فيديو
            self.fetch_individual_qualities()

    def show_quality_dialog_for_video(self, event=None, item=None, url=None):
        """Handle click on quality column or create Combobox automatically; prevent duplicate Combobox creation."""
        if self.use_single_quality_var.get():
            logging.debug("Single quality mode is enabled, skipping individual quality selection")
            return

        # إذا كان الاستدعاء بحدث (نقر)
        if event:
            region = self.batch_tree.identify_region(event.x, event.y)
            if region != "cell":
                logging.debug(f"Clicked region is not a cell: {region}")
                return

            column = self.batch_tree.identify_column(event.x)
            if column != "#4":
                logging.debug(f"Clicked column is not quality column: {column}")
                return

            item = self.batch_tree.identify_row(event.y)
            if not item:
                logging.debug("No item identified for click")
                return
        # إذا كان الاستدعاء بدون حدث (تلقائي)
        elif not item or not url:
            logging.debug("Missing item or URL for automatic Combobox creation")
            return

        # التحقق مما إذا كان هناك Combobox موجود بالفعل
        if item in self.batch_quality_comboboxes:
            logging.debug(f"Combobox already exists for item {item}, focusing it")
            self.batch_quality_comboboxes[item].focus_set()
            return

        # إذا كان الاستدعاء بحدث، جلب الـ URL من الـ Treeview
        if event:
            values = self.batch_tree.item(item, "values")
            url = values[0]
            if len(url) > 50:
                url = next((u for u in self.batch_urls if u.startswith(url[:50])), None)
                if not url:
                    logging.error("Full URL not found for abbreviated URL")
                    return

        qualities = self.batch_available_qualities.get(url, [])
        if not qualities:
            logging.warning(f"No qualities available for URL: {url}")
            self.root.after(
                0,
                lambda: messagebox.showwarning(
                    self.translations[self.language]["warning"],
                    self.translations[self.language]["no_qualities"]
                )
            )
            return

        # إجبار تحديث الـ Treeview لضمان إن الـ bbox صحيح
        self.batch_tree.update_idletasks()
        x, y, width, height = self.batch_tree.bbox(item, "#4")
        if not all([x, y, width, height]):
            logging.debug(f"Invalid bbox for item {item}: {x}, {y}, {width}, {height}")
            return
        logging.debug(f"Combobox position: x={x}, y={y}, width={width}, height={height}")

        combo = ttk.Combobox(self.batch_tree, values=qualities, state="readonly", width=40)
        combo.set(self.batch_quality_selections.get(url, qualities[-1]))
        combo.place(x=x, y=y, width=width, height=height)
        self.batch_quality_comboboxes[item] = combo

        def on_select(event):
            new_quality = combo.get()
            if new_quality:
                self.batch_quality_selections[url] = new_quality
                format_id, ext, filesize, format_note, is_combined = self.batch_formats_cache[url][new_quality]
                filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"
                self.batch_tree.item(item, values=(
                    values[0],
                    values[1],
                    values[2],
                    new_quality,
                    f"{filesize_mb:.2f} ميجا" if isinstance(filesize_mb, float) else filesize_mb
                ))
                for item_data in self.batch_download_items:
                    if item_data['url'] == url:
                        item_data.update({
                            'quality': new_quality,
                            'format_id': format_id,
                            'ext': ext,
                            'filesize_mb': filesize_mb,
                            'is_combined': is_combined
                        })
                        break

        combo.bind("<<ComboboxSelected>>", on_select)
        combo.focus_set()
    def handle_tree_click(self, event):
        self.show_quality_dialog_for_video(event)

    def on_tree_click(self, event):
        """معالجة النقر على الجدول لتحرير الجودة"""
        import logging
        logging.basicConfig(level=logging.DEBUG)

        # تحقق من وجود self.playlist_available_qualities
        if not hasattr(self, 'playlist_available_qualities'):
            logging.error("self.playlist_available_qualities غير معرف")
            messagebox.showerror(
                "خطأ", "فشل تهيئة قائمة الجودات لقائمة التشغيل")
            return

        # تحديد الجدول الذي تم النقر عليه
        tree = event.widget
        if tree not in [self.batch_tree, self.playlist_tree]:
            logging.debug("النقر ليس على جدول صالح")
            return

        # تحديد المنطقة التي تم النقر عليها
        region = tree.identify("region", event.x, event.y)
        if region != "cell":
            logging.debug("النقر ليس على خلية")
            return

        # تحديد العمود والصف
        column = tree.identify_column(event.x)
        row = tree.identify_row(event.y)
        if not row:
            logging.debug(f"لم يتم تحديد صف (الصف: {row})")
            return

        # تحديد ما إذا كان النقر على عمود الجودة
        quality_column = "#4" if tree == self.batch_tree else "#4"
        if column != quality_column:
            logging.debug(f"النقر ليس على عمود الجودة (العمود: {column})")
            return

        # جلب معرف الصف
        item = tree.item(row)
        values = item['values']
        url = values[0]

        # إخفاء أي Combobox موجودة مسبقًا (للتنزيل الجماعي فقط)
        if tree == self.batch_tree:
            if hasattr(self, 'current_combobox') and self.current_combobox:
                self.current_combobox.destroy()
                self.current_combobox = None

        # لجدول التنزيل الجماعي
        if tree == self.batch_tree:
            try:
                if len(url) > 50:
                    url = next(
                        u for u in self.batch_urls if u.startswith(url[:50]))
                logging.debug(f"تم استرجاع الرابط: {url}")
            except StopIteration:
                logging.error(f"فشل استرجاع الرابط من {url[:50]}")
                return

            # التحقق من وجود جودات متاحة، وإعادة الجلب إذا لزم الأمر
            if url not in self.batch_available_qualities or not self.batch_available_qualities[
                url]:
                logging.warning(
                    f"لا توجد جودات متاحة لـ {url}، جاري إعادة الجلب...")
                ydl_opts = {
                    'quiet': True,
                    'no_warnings': True,
                    'http_headers': {
                        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
                    }
                }
                try:
                    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                        info = ydl.extract_info(url, download=False)
                        formats = info.get('formats', [])
                        quality_list = []
                        self.batch_formats_cache[url] = {}
                        self.batch_available_qualities[url] = []

                        for f in formats:
                            resolution = f.get('height', None)
                            ext = f.get('ext', 'N/A')
                            if ext.lower() == 'webm' or not resolution:
                                logging.debug(
                                    f"تم استبعاد التنسيق: ext={ext}, resolution={resolution}")
                                continue
                            format_id = f.get('format_id')
                            format_note = f.get('format_note', '')
                            fps = f.get('fps', '')
                            filesize = f.get(
                                'filesize', 0) or f.get(
                                'filesize_approx', 0)
                            filesize_mb = filesize / \
                                (1024 * 1024) if filesize else "غير معروف"
                            quality_key = f"{resolution}p {ext}"
                            if format_note and format_note != str(resolution) + 'p':
                                quality_key += f" ({format_note})"
                            if fps:
                                quality_key += f" {fps}fps"
                            quality_display = f"{quality_key} - {filesize_mb:.2f} ميجا" if isinstance(
                                filesize_mb, float) else f"{quality_key} - {filesize_mb}"
                            has_video = f.get('vcodec', 'none') != 'none'
                            has_audio = f.get('acodec', 'none') != 'none'
                            is_combined = has_video and has_audio
                            quality_list.append(quality_display)
                            self.batch_formats_cache[url][quality_key] = (
                                format_id, ext, filesize, format_note, is_combined
                            )
                            self.batch_available_qualities[url].append(
                                quality_display)

                        quality_list.sort(
                            key=lambda x: int(
                                x.split('p')[0]) if 'p' in x and x.split('p')[0].isdigit() else 0)
                        self.batch_available_qualities[url].sort(key=lambda x: int(
                            x.split('p')[0]) if 'p' in x and x.split('p')[0].isdigit() else 0)
                        logging.debug(
                            f"الجودات بعد إعادة الجلب لـ {url}: {self.batch_available_qualities[url]}")

                        if not quality_list:
                            messagebox.showwarning(
                                "تحذير", f"لم يتم العثور على جودات متاحة لـ {url} بعد إعادة المحاولة")
                            return

                except Exception as e:
                    logging.error(f"فشل إعادة جلب الجودات لـ {url}: {e}")
                    messagebox.showerror(
                        "خطأ", f"فشل جلب الجودات لـ {url}: {e}")
                    return

            # إنشاء Combobox
            x, y, width, height = tree.bbox(row, column)
            combobox = ttk.Combobox(
                tree,
                values=self.batch_available_qualities[url],
                state="readonly",
                width=20
            )
            combobox.place(x=x, y=y, width=width, height=height)
            combobox.set(self.batch_quality_selections.get(url, ""))
            logging.debug(
                f"تم إنشاء Combobox لـ {url} مع الجودات: {self.batch_available_qualities[url]}")

            # تخزين الـ Combobox الحالية ومعلومات الصف/العمود
            self.current_combobox = combobox
            self.current_combobox_row = row
            self.current_combobox_column = column
            self.current_combobox_tree = tree

            def on_combobox_select(event):
                selected_quality = combobox.get()
                clean_quality = selected_quality.split(' - ')[0].strip()
                if clean_quality and clean_quality != self.batch_quality_selections.get(
                    url):
                    # تحديث الجودة المختارة
                    self.batch_quality_selections[url] = clean_quality

                    # تحديث حجم الملف
                    format_id, ext, filesize, format_note, is_combined = self.batch_formats_cache[
                        url][clean_quality]
                    filesize_mb = filesize / \
                        (1024 * 1024) if filesize else "غير معروف"

                    # تحديث الجدول
                    tree.item(row, values=(
                        values[0],
                        values[1],
                        values[2],
                        clean_quality,
                        f"{filesize_mb:.2f} ميجا" if isinstance(
                            filesize_mb, float) else filesize_mb
                    ))

                    # تحديث batch_download_items
                    for item in self.batch_download_items:
                        if item['url'] == url:
                            item.update({
                                'quality': clean_quality,
                                'format_id': format_id,
                                'ext': ext,
                                'is_combined': is_combined,
                                'filesize_mb': filesize_mb
                            })
                            break
                    logging.debug(
                        f"تم تحديث الجودة لـ {url} إلى {clean_quality}")

            # ربط حدث اختيار الجودة
            combobox.bind("<<ComboboxSelected>>", on_combobox_select)

            # إغلاق الـ Combobox عند فقدان التركيز
            def close_combobox(event):
                combobox.destroy()
                self.current_combobox = None
                logging.debug(f"تم إغلاق Combobox لـ {url}")

            combobox.bind("<FocusOut>", close_combobox)

        # لجدول قائمة التشغيل
        elif tree == self.playlist_tree:
            index = int(values[0]) - 1  # العمود الأول (Index)
            video = self.playlist_videos[index]
            url = video['url']

            # التحقق من استخدام الجودة الموحدة
            if self.use_single_quality_var.get():
                logging.debug("الجودة الموحدة مفعلة، لا حاجة لـ Combobox")
                return

            # التحقق من وجود جودات متاحة
            if url not in self.playlist_available_qualities or not self.playlist_available_qualities[
                url]:
                logging.warning(f"لا توجد جودات متاحة لـ {url}")
                return

            # التحقق مما إذا كان هناك Combobox موجود بالفعل لهذا العنصر
            if row in self.combobox_widgets:
                self.combobox_widgets[row].focus_set()
                logging.debug(f"Combobox موجود بالفعل للصف {row}")
                return

            # إنشاء Combobox
            tree.update_idletasks()
            x, y, width, height = tree.bbox(row, column)
            if not all([x, y, width, height]):
                logging.debug(f"فشل الحصول على bbox للصف {row}")
                return

            combobox = ttk.Combobox(
                tree,
                values=self.playlist_available_qualities[url],
                state="readonly",
                width=40
            )
            combobox.set(video.get('selected_quality', self.playlist_available_qualities[url][0]))
            combobox.place(x=x, y=y, width=width, height=height)
            combobox.lift()
            self.combobox_widgets[row] = combobox
            logging.debug(
                f"تم إنشاء Combobox لـ {url} مع الجودات: {self.playlist_available_qualities[url]}")

            def on_combobox_select(event):
                selected_quality = combobox.get()
                clean_quality = selected_quality.split(' - ')[0].strip()
                if clean_quality and clean_quality != video.get('selected_quality'):
                    # تحديث الجودة المختارة
                    video['selected_quality'] = clean_quality

                    # تحديث حجم الملف
                    format_id, ext, filesize, format_note, is_combined = self.playlist_formats_cache[
                        url][clean_quality]
                    filesize_mb = filesize / \
                        (1024 * 1024) if filesize else "غير معروف"

                    # تحديث الجدول
                    tree.item(row, values=(
                        values[0],
                        values[1],
                        values[2],
                        clean_quality,
                        values[4],
                        values[5]
                    ))
                    logging.debug(
                        f"تم تحديث الجودة لـ {url} إلى {clean_quality}")

            # ربط حدث اختيار الجودة
            combobox.bind("<<ComboboxSelected>>", on_combobox_select)

            # إغلاق الـ Combobox عند فقدان التركيز
            def close_combobox(event):
                if row in self.combobox_widgets:
                    self.combobox_widgets[row].destroy()
                    del self.combobox_widgets[row]
                logging.debug(f"تم إغلاق Combobox لـ {url}")

            combobox.bind("<FocusOut>", close_combobox)
            combobox.focus_set()
    def add_combobox(self, item_id, url, qualities, default_quality):
        """Add a Combobox to the quality column for the given Treeview item."""
        QUALITY_COLUMN_WIDTH = 150  # نفس العرض المستخدم في create_batch_tab
        max_attempts = 10
        attempt = 0

        def try_add_combobox():
            nonlocal attempt
            try:
                bbox = self.batch_tree.bbox(item_id, column="#4")  # Quality column
                logging.debug(f"Creating Combobox for item {item_id}, bbox: {bbox}")
                if not bbox:
                    if attempt < max_attempts:
                        attempt += 1
                        self.root.after(1000, try_add_combobox)
                        logging.debug(f"Attempt {attempt}/{max_attempts} to get bbox for item {item_id}")
                    else:
                        logging.error(f"Failed to get valid bbox for item {item_id} after {max_attempts} attempts")
                    return

                x, y, width, height = bbox
                if width == 0 or height == 0:
                    if attempt < max_attempts:
                        attempt += 1
                        self.root.after(1000, try_add_combobox)
                        logging.debug(f"Invalid bbox dimensions for item {item_id}, attempt {attempt}/{max_attempts}")
                    else:
                        logging.error(f"Invalid bbox dimensions for item {item_id} after {max_attempts} attempts")
                    return

                # إذا كان هناك Combobox قديم، قم بإزالته
                if item_id in self.batch_comboboxes:
                    self.batch_comboboxes[item_id].destroy()
                    del self.batch_comboboxes[item_id]

                # إنشاء Combobox جديد
                combo = ttk.Combobox(self.batch_tree, values=qualities, state="readonly", width=QUALITY_COLUMN_WIDTH // 10)
                combo.set(default_quality)
                combo.place(x=x, y=y, width=QUALITY_COLUMN_WIDTH, height=height)

                # ربط حدث الاختيار
                def on_select(event):
                    selected_quality = combo.get()
                    clean_quality = selected_quality.split(' - ')[0].strip()
                    if clean_quality:
                        self.batch_quality_selections[url] = clean_quality
                        format_id, ext, filesize, format_note, is_combined = self.batch_formats_cache[url][clean_quality]
                        filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"
                        values = self.batch_tree.item(item_id, "values")
                        self.batch_tree.item(item_id, values=(
                            values[0],
                            values[1],
                            values[2],
                            clean_quality,
                            f"{filesize_mb:.2f} ميجا" if isinstance(filesize_mb, float) else filesize_mb
                        ))

                        # تحديث batch_download_items
                        for item_data in self.batch_download_items:
                            if item_data['url'] == url:
                                item_data.update({
                                    'quality': clean_quality,
                                    'format_id': format_id,
                                    'ext': ext,
                                    'filesize_mb': filesize_mb,
                                    'is_combined': is_combined
                                })
                                break

                combo.bind("<<ComboboxSelected>>", on_select)
                self.batch_comboboxes[item_id] = combo
                logging.debug(f"Successfully added Combobox for item {item_id}")

            except Exception as e:
                logging.error(f"Error adding Combobox for item {item_id}: {e}")
                if attempt < max_attempts:
                    attempt += 1
                    self.root.after(1000, try_add_combobox)
                    logging.debug(f"Retrying Combobox creation for item {item_id}, attempt {attempt}/{max_attempts}")
                else:
                    logging.error(f"Failed to add Combobox for item {item_id} after {max_attempts} attempts: {e}")

        # تحديث الواجهة قبل محاولة إضافة الـ Combobox
        self.root.update()
        self.root.update_idletasks()
        try_add_combobox()
    def update_combobox_position(self, *args):
        """تحديث موقع Combobox أثناء التمرير"""
        import logging
        logging.basicConfig(level=logging.DEBUG)
        
        if not hasattr(self, 'current_combobox') or not self.current_combobox:
            return
        
        tree = self.current_combobox_tree
        row = self.current_combobox_row
        column = self.current_combobox_column
        
        # التحقق مما إذا كان الصف لا يزال موجودًا في الجدول
        if not tree.exists(row):
            self.current_combobox.destroy()
            self.current_combobox = None
            logging.debug("تم إغلاق Combobox لأن الصف لم يعد موجودًا")
            return
        
        # التحقق مما إذا كان الصف مرئيًا
        visible_items = tree.get_children()
        if row not in visible_items:
            self.current_combobox.place_forget()
            logging.debug(f"تم إخفاء Combobox لأن الصف {row} غير مرئي")
            return
        
        # تحديث موقع Combobox
        try:
            x, y, width, height = tree.bbox(row, column)
            self.current_combobox.place(x=x, y=y, width=width, height=height)
            logging.debug(f"تم تحديث موقع Combobox إلى x={x}, y={y}")
        except Exception as e:
            logging.error(f"خطأ في تحديث موقع Combobox: {e}")
            self.current_combobox.destroy()
            self.current_combobox = None


    def open_settings(self):
        settings_window = tk.Toplevel(self.root)
        settings_window.title(self.translations[self.language]["settings"])
        settings_window.geometry("500x400")
        settings_window.configure(bg=self.secondary_color)

        # إطار اللغة
        language_frame = ttk.Frame(settings_window, style="TFrame")
        language_frame.pack(fill=tk.X, padx=10, pady=5)
        ttk.Label(language_frame, text="اللغة:").pack(side=tk.LEFT, padx=5)
        language_var = tk.StringVar(value=self.language)
        language_combo = ttk.Combobox(
            language_frame,
            textvariable=language_var,
            values=["ar", "en"],
            state="readonly"
        )
        language_combo.pack(side=tk.LEFT, padx=5)

        # إطار مسار الحفظ
        path_frame = ttk.Frame(settings_window, style="TFrame")
        path_frame.pack(fill=tk.X, padx=10, pady=5)
        ttk.Label(path_frame,
    text=self.translations[self.language]["save_path"] + ":").pack(side=tk.LEFT,
     padx=5)
        path_entry = ttk.Entry(path_frame, width=50)
        path_entry.insert(0, self.save_path)
        path_entry.pack(side=tk.LEFT, padx=5)
        ttk.Button(
            path_frame,
            text=self.translations[self.language]["select_folder"],
            command=lambda: self.select_directory_for_settings(path_entry),
            style="Accent.TButton"
        ).pack(side=tk.LEFT, padx=5)

        # إطار الحد الأقصى للعمال
        workers_frame = ttk.Frame(settings_window, style="TFrame")
        workers_frame.pack(fill=tk.X, padx=10, pady=5)
        ttk.Label(
    workers_frame,
    text="الحد الأقصى للعمال:").pack(
        side=tk.LEFT,
         padx=5)
        workers_entry = ttk.Entry(workers_frame, width=10)
        workers_entry.insert(0, str(self.max_workers))
        workers_entry.pack(side=tk.LEFT, padx=5)

        # إطار الحد الأقصى للسرعة
        speed_frame = ttk.Frame(settings_window, style="TFrame")
        speed_frame.pack(fill=tk.X, padx=10, pady=5)
        ttk.Label(speed_frame,
    text="الحد الأقصى للسرعة (ميجا/ث):").pack(side=tk.LEFT,
     padx=5)
        speed_entry = ttk.Entry(speed_frame, width=10)
        speed_entry.insert(0, str(self.max_speed))
        speed_entry.pack(side=tk.LEFT, padx=5)

        # إطار مسار FFmpeg
        ffmpeg_frame = ttk.Frame(settings_window, style="TFrame")
        ffmpeg_frame.pack(fill=tk.X, padx=10, pady=5)
        ttk.Label(ffmpeg_frame, text="مسار FFmpeg:").pack(side=tk.LEFT, padx=5)
        ffmpeg_entry = ttk.Entry(ffmpeg_frame, width=50)
        ffmpeg_entry.insert(0, self.ffmpeg_path)
        ffmpeg_entry.pack(side=tk.LEFT, padx=5)

        # إطار التخزين السحابي
        cloud_frame = ttk.Frame(settings_window, style="TFrame")
        cloud_frame.pack(fill=tk.X, padx=10, pady=5)
        cloud_var = tk.BooleanVar(value=self.cloud_enabled)
        ttk.Checkbutton(
            cloud_frame,
            text="تفعيل التخزين السحابي",
            variable=cloud_var
        ).pack(side=tk.LEFT, padx=5)
        ttk.Label(cloud_frame, text="رمز Dropbox:").pack(side=tk.LEFT, padx=5)
        cloud_entry = ttk.Entry(cloud_frame, width=50)
        cloud_entry.insert(0, self.cloud_token)
        cloud_entry.pack(side=tk.LEFT, padx=5)

        # زر الحفظ
        ttk.Button(
            settings_window,
            text="حفظ",
            command=lambda: self.save_new_settings(
                language_var.get(),
                path_entry.get(),
                workers_entry.get(),
                speed_entry.get(),
                ffmpeg_entry.get(),
                cloud_var.get(),
                cloud_entry.get(),
                settings_window
            ),
            style="Accent.TButton"
        ).pack(pady=10)

    def select_directory_for_settings(self, entry):
        directory = filedialog.askdirectory(initialdir=self.save_path)
        if directory and os.path.isdir(directory):
            entry.delete(0, tk.END)
            entry.insert(0, directory)

    def save_new_settings(self, language, save_path, max_workers, max_speed, ffmpeg_path, cloud_enabled, cloud_token, window):
        try:
            self.language = language
            self.save_path = save_path if os.path.isdir(
                save_path) else self.save_path
            self.max_workers = int(
                max_workers) if max_workers.isdigit() else self.max_workers
            self.max_speed = float(max_speed) if max_speed.replace(
                '.', '', 1).isdigit() else self.max_speed
            self.ffmpeg_path = ffmpeg_path
            self.cloud_enabled = cloud_enabled
            self.cloud_token = cloud_token
            self.update_ui_language()
            self.save_settings()
            self.check_ffmpeg()
            # Update batch and playlist paths
            self.batch_path_var.set(save_path)
            self.playlist_path_entry.delete(0, tk.END)
            self.playlist_path_entry.insert(0, save_path)
            self.playlist_save_path = save_path
            window.destroy()
        except Exception as e:
            messagebox.showerror("خطأ", f"فشل حفظ الإعدادات: {e}")

    def extract_playlist(self):
        url = self.playlist_url_var.get().strip()
        print(f"جاري جلب قائمة التشغيل: {url}")
        if not url:
            messagebox.showerror("خطأ",
     self.translations[self.language]["no_url"])
            print("مافيش رابط مدخل")
            return

        if not self.is_valid_url(url):
            messagebox.showerror("خطأ", "الرابط غير صالح")
            print("الرابط مش صحيح")
            return

        def fetch_playlist_thread():
            try:
                ydl_opts = {
                    'quiet': True,
                    'no_warnings': True,
                    'extract_flat': True,
                    'http_headers': {
                        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
                    }
                }
                with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                    info = ydl.extract_info(url, download=False)
                    if 'entries' not in info:
                        self.root.after(0, lambda: messagebox.showerror(
                            "خطأ", "الرابط ليس قائمة تشغيل صالحة"
                        ))
                        return

                    # تنظيف الجدول والقوائم
                    for item in self.playlist_tree.get_children():
                        self.playlist_tree.delete(item)
                    self.playlist_videos = []

                    # جلب تفاصيل الفيديوهات
                    for index, entry in enumerate(info['entries'], 1):
                        video_url = entry.get(
                            'url') or entry.get('webpage_url')
                        if not video_url:
                            continue

                        title = entry.get('title', 'غير معروف')
                        duration = entry.get('duration', 'غير معروف')
                        if isinstance(duration, (int, float)):
                            duration = f"{int(duration //
    60)}:{int(duration %
     60):02d}"
                        filename = f"{title}.mp4".replace(
                            '/', '_').replace('\\', '_')
                        upload_date = entry.get('upload_date', 'غير معروف')
                        if upload_date and upload_date != 'غير معروف':
                            upload_date = f"{upload_date[:4]}-{upload_date[4:6]}-{upload_date[6:8]}"

                        self.playlist_videos.append({
                            'url': video_url,
                            'title': title,
                            'duration': duration,
                            'filename': filename,
                            'upload_date': upload_date,
                            'selected_quality': 'غير محدد'
                        })

                        # إضافة إلى الجدول
                        self.playlist_tree.insert("", "end", values=(
                            index,
                            title,
                            duration,
                            'غير محدد',
                            filename,
                            upload_date
                        ))

                    if not self.playlist_videos:
                        self.root.after(0, lambda: messagebox.showwarning(
                            "تحذير", self.translations[self.language]["no_videos"]
                        ))
                        return

                    # جلب الجودات الموحدة فقط إذا كان الخيار مفعلًا
                    if self.use_single_quality_var.get():
                        self.root.after(0, self.fetch_qualities_for_playlist)
                    else:
                        print("تم تخطي جلب الجودات لأن الجودة الموحدة غير مفعلة")

            except Exception as e:
                print(f"خطأ في جلب قائمة التشغيل: {e}")
                self.root.after(0, lambda: messagebox.showerror(
                    "خطأ", f"فشل جلب قائمة التشغيل: {e}"
                ))

        threading.Thread(target=fetch_playlist_thread, daemon=True).start()

    def load_stats(self):
        """Load download statistics from file or return default stats."""
        default_stats = {
            'total_files': 0,
            'total_size_mb': 0.0,
            'avg_speed_mbps': 0.0,
            'total_downloads': 0
        }

        if os.path.exists(self.stats_file):
            try:
                with open(self.stats_file, 'r', encoding='utf-8') as f:
                    loaded_stats = json.load(f)
                    # Ensure all required keys are present
                    for key in default_stats:
                        if key not in loaded_stats:
                            loaded_stats[key] = default_stats[key]
                    return loaded_stats
            except (json.JSONDecodeError, IOError) as e:
                logging.error(
    f"Error loading stats file {
        self.stats_file}: {e}")
                # Save default stats to file if it exists but is corrupted
                try:
                    with open(self.stats_file, 'w', encoding='utf-8') as f:
                        json.dump(
    default_stats, f, ensure_ascii=False, indent=4)
                except IOError as e:
                    logging.error(
    f"Error writing default stats to {
        self.stats_file}: {e}")
        else:
            # Create new stats file with default values
            try:
                os.makedirs(os.path.dirname(self.stats_file), exist_ok=True)
                with open(self.stats_file, 'w', encoding='utf-8') as f:
                    json.dump(default_stats, f, ensure_ascii=False, indent=4)
            except IOError as e:
                logging.error(
    f"Error creating stats file {
        self.stats_file}: {e}")

        return default_stats

    def load_incomplete_downloads(self):
        """Load incomplete downloads from incomplete_downloads.json."""
        try:
            with open(self.incomplete_file, 'r', encoding='utf-8') as f:
                return json.load(f)
        except (FileNotFoundError, json.JSONDecodeError):
            return {}

    def load_icons(self):
        icon_size = (20, 20)
        self.icons = {}
        icon_files = {
            'play': "play_icon.png",
            'pause': "pause_icon.png",
            'cancel': "cancel_icon.png",
            'success': "success_icon.png",
            'failed': "failed_icon.png",
            'retry': "retry_icon.png"
        }
        for key, filename in icon_files.items():
            if os.path.isfile(filename):
                try:
                    self.icons[key] = ImageTk.PhotoImage(
                        Image.open(filename).resize(icon_size)
                    )
                except Exception as e:
                    print(f"فشل تحميل الأيقونة {filename}: {e}")
            else:
                print(f"ملف الأيقونة {filename} غير موجود")

    def setup_styles(self):
        self.style = ttk.Style()
        self.style.theme_use('clam')
        self.style.configure(
            ".",
            font=("Segoe UI", 11, "bold"),
            background=self.secondary_color
        )
        self.style.configure("TFrame", background=self.secondary_color)
        self.style.configure("Header.TFrame", background=self.primary_color)
        self.style.configure(
            "TLabel",
            background=self.secondary_color,
            foreground=self.primary_color,
            font=("Segoe UI", 11, "bold")
        )
        self.style.configure(
            "Accent.TButton",
            background=self.accent_color,
            foreground="white",
            font=("Segoe UI", 11, "bold"),
            padding=5,
            borderwidth=0
        )
        self.style.map("Accent.TButton", background=[('active', '#D97706')])
        self.style.configure(
            "TProgressbar",
            thickness=25,
            troughcolor=self.secondary_color,
            background=self.accent_color
        )
        self.style.configure(
    "Treeview",
    font=(
        "Segoe UI",
        10,
        "bold"),
         rowheight=30)
        self.style.configure(
            "Treeview.Heading",
            font=("Segoe UI", 11, "bold"),
            background=self.primary_color,
            foreground="white"
        )
        self.style.configure(
            "TCheckbutton",
            font=("Segoe UI", 10, "bold"),
            indicatorsize=12
        )
        self.style.map(
            "TCheckbutton",
            indicator=[
                ('selected', '!disabled', '✓'),
                ('!selected', '!disabled', '✗')
            ]
        )

    def update_ui_language(self):
        """تحديث واجهة المستخدم بناءً على اللغة المحددة"""
        # تحديث التسميات
        if hasattr(self, 'welcome_label'):
            self.welcome_label.config(
                text=self.translations[self.language].get('welcome', 'مرحبًا')
            )
        if hasattr(self, 'hello_label'):
            self.hello_label.config(
                text=self.translations[self.language].get(
                    'hello_mr_saleh', 'مرحبًا السيد صالح')
            )

        # تحديث الأزرار
        if hasattr(self, 'settings_button'):
            self.settings_button.config(
                text=self.translations[self.language].get(
                    'settings', 'الإعدادات')
            )
        if hasattr(self, 'dark_mode_button'):
            self.dark_mode_button.config(
                text=self.translations[self.language].get(
                    'dark_mode', 'الوضع الداكن')
            )

        # تحديث عناوين التبويبات
        if hasattr(self, 'download_tab'):
            self.notebook.tab(
                self.download_tab,
                text=self.translations[self.language].get(
                    'single_download', 'تنزيل فردي')
            )
        if hasattr(self, 'batch_tab'):
            self.notebook.tab(
                self.batch_tab,
                text=self.translations[self.language].get(
                    'batch_download', 'التنزيل الجماعي')
            )
        if hasattr(self, 'history_tab'):
            self.notebook.tab(
                self.history_tab,
                text=self.translations[self.language].get('history', 'السجل')
            )
        if hasattr(self, 'incomplete_tab'):
            self.notebook.tab(
                self.incomplete_tab,
                text=self.translations[self.language].get(
                    'incomplete', 'غير مكتمل')
            )
        if hasattr(self, 'stats_tab'):
            self.notebook.tab(
                self.stats_tab,
                text=self.translations[self.language].get(
                    'stats', 'الإحصائيات')
            )
        if hasattr(self, 'playlist_tab'):
            self.notebook.tab(
                self.playlist_tab,
                text=self.translations[self.language].get(
                    'playlist_download', 'تنزيل قائمة تشغيل')
            )

        # تحديث تسميات وأزرار تبويب التنزيل الفردي
        if hasattr(self, 'url_label'):
            self.url_label.config(
                text=self.translations[self.language].get(
                    'url_label', 'الرابط:')
            )
        if hasattr(self, 'extract_links_button'):
            self.extract_links_button.config(
                text=self.translations[self.language].get(
                    'extract_links', 'استخراج الروابط')
            )
        if hasattr(self, 'quality_button'):
            self.quality_button.config(
                text=self.translations[self.language].get(
                    'quality_button', 'اختيار الجودة')
            )
        if hasattr(self, 'quality_label'):
            self.quality_label.config(
                text=self.translations[self.language].get(
                    'quality_label', 'الجودة:')
            )
        if hasattr(self, 'start_download_button'):
            self.start_download_button.config(
                text=self.translations[self.language].get(
                    'start_download', 'بدء التنزيل')
            )
        if hasattr(self, 'download_type_label'):
            self.download_type_label.config(
                text=self.translations[self.language].get(
                    'download_type_label', 'نوع التنزيل:')
            )
        if hasattr(self, 'download_type_combo'):
            self.download_type_combo['values'] = [
                self.translations[self.language].get(
                    'video_only', 'فيديو فقط'),
                self.translations[self.language].get('audio_only', 'صوت فقط'),
                self.translations[self.language].get(
                    'video_with_subtitles', 'فيديو مع ترجمة')
            ]

        # تحديث تسميات وأزرار التنزيل العام
        if hasattr(self, 'general_url_label'):
            self.general_url_label.config(
                text=self.translations[self.language].get(
                    'general_url_label', 'الرابط العام:')
            )
        if hasattr(self, 'start_general_button'):
            self.start_general_button.config(
                text=self.translations[self.language].get(
                    'start_download', 'بدء التنزيل')
            )
        if hasattr(self, 'select_folder_button'):
            self.select_folder_button.config(
                text=self.translations[self.language].get(
                    'select_folder', 'اختيار المجلد')
            )

        # تحديث تسميات وأزرار تبويب التنزيل الجماعي
        if hasattr(self, 'batch_path_label'):
            self.batch_path_label.config(
                text=self.translations[self.language].get(
                    'download_path', 'مسار التنزيل') + ':'
            )
        if hasattr(self, 'batch_select_folder_button'):
            self.batch_select_folder_button.config(
                text=self.translations[self.language].get(
                    'select_folder', 'اختيار المجلد')
            )
        if hasattr(self, 'batch_url_label'):
            self.batch_url_label.config(
                text=self.translations[self.language].get(
                    'batch_url', 'الروابط')
            )
        if hasattr(self, 'batch_fetch_button'):
            self.batch_fetch_button.config(
                text=self.translations[self.language].get(
                    'fetch_quality', 'جلب الجودات')
            )
        if hasattr(self, 'batch_start_button'):
            self.batch_start_button.config(
                text=self.translations[self.language].get(
                    'start_batch', 'بدء التنزيل الجماعي')
            )
        if hasattr(self, 'batch_clear_button'):
            self.batch_clear_button.config(
                text=self.translations[self.language].get(
                    'clear_batch', 'مسح الروابط')
            )

        # تحديث رؤوس جدول التنزيل الجماعي
        if hasattr(self, 'batch_tree'):
            self.batch_tree.heading(
                'url', text=self.translations[self.language].get('url', 'الرابط'))
            self.batch_tree.heading(
                'title', text=self.translations[self.language].get('title', 'العنوان'))
            self.batch_tree.heading(
                'duration', text=self.translations[self.language].get('duration', 'المدة'))
            self.batch_tree.heading(
                'quality', text=self.translations[self.language].get('quality', 'الجودة'))
            self.batch_tree.heading(
                'size', text=self.translations[self.language].get('size', 'الحجم'))

        # تحديث تسميات وأزرار تبويب السجل
        if hasattr(self, 'history_search_label'):
            self.history_search_label.config(
                text=self.translations[self.language].get(
                    'search_history', 'بحث في السجل')
            )
        if hasattr(self, 'history_clear_button'):
            self.history_clear_button.config(
                text=self.translations[self.language].get(
                    'clear_history', 'مسح السجل')
            )

        # تحديث تسميات وأزرار تبويب التنزيلات غير المكتملة
        if hasattr(self, 'incomplete_resume_button'):
            self.incomplete_resume_button.config(
                text=self.translations[self.language].get('resume', 'استئناف')
            )
        if hasattr(self, 'incomplete_clear_button'):
            self.incomplete_clear_button.config(
                text=self.translations[self.language].get('clear', 'مسح')
            )

        # تحديث شريط الحالة
        if hasattr(self, 'status_bar'):
            self.status_bar.config(
                text=self.translations[self.language].get('ready', 'جاهز')
            )

    def extract_playlist_video_url(self, url):
        """استخراج رابط فيديو فردي من رابط يحتوي على معلمات قائمة تشغيل"""
        try:
            if "youtube.com/watch?v=" in url and "&list=" in url:
                # استخراج معرف الفيديو فقط وإهمال باقي المعلمات
                video_id = url.split("v=")[1].split("&")[0]
                return f"https://www.youtube.com/watch?v={video_id}"
            return url
        except Exception as e:
            print(f"خطأ في استخراج رابط الفيديو: {e}")
            return url

    def normalize_url(self, url):
        try:
            if not url.startswith(('http://', 'https://')):
                url = 'https://' + url
            return url if 'youtube.com' in url or 'youtu.be' in url else None
        except Exception as e:
            logging.error(f"Error normalizing URL: {e}")
            return None

    def is_valid_url(self, url):
        """Check if the URL is valid."""
        return bool(self.normalize_url(url))

    def get_video_title(self, url):
        """Get the video title from the URL."""
        try:
            with yt_dlp.YoutubeDL({'quiet': True}) as ydl:
                info = ydl.extract_info(url, download=False)
                return info.get('title', 'downloaded_file')
        except:
            return 'downloaded_file'

    def update_quality_combo(self, quality_list, url):
        """Update the quality combo box with available qualities."""
        self.quality_combo.config(values=quality_list)
        if quality_list:
            self.quality_combo.current(0)  # Select the first quality
            self.status_bar.config(
                text=f"تم العثور على {len(quality_list)} جودة متاحة"
            )
            self.start_download_button.config(state="normal")
        else:
            self.quality_combo.set("")
            self.status_bar.config(
                text="لم يتم العثور على جودات متاحة"
            )
            self.start_download_button.config(state="disabled")


    def _sanitize_filename(self, filename):
        """Clean a string to make it safe for use as a filename."""
        # إزالة الأحرف غير الصالحة لأسماء الملفات في Windows
        invalid_chars = r'[<>:"/\\|?*]'
        filename = re.sub(invalid_chars, '_', filename)
        # إزالة المسافات في بداية أو نهاية السلسلة
        filename = filename.strip()
        # استبدال المسافات المتعددة بمسافة واحدة
        filename = re.sub(r'\s+', '_', filename)
        # التأكد من أن الاسم ليس فارغًا
        if not filename:
            filename = "unnamed"
        return filename[:255]


    def create_download_window(self, url, total_bytes, filename):
        """Create a compact IDM-style download progress window with visible widgets."""
        import tkinter as tk
        from tkinter import ttk
        import logging
        import hashlib

        logging.basicConfig(level=logging.DEBUG)

        try:
            # Create a unique task_id for the download
            url_hash = hashlib.md5(url.encode('utf-8')).hexdigest()
            task_id = f"download_{url_hash}"

            # Check if window already exists
            if task_id in self.download_windows and self.download_windows[task_id]['window'].winfo_exists():
                logging.debug(f"Download window for {url} (task_id: {task_id}) already exists")
                self.download_windows[task_id]['window'].lift()
                return self.download_windows[task_id]

            # Initialize window
            window = tk.Toplevel(self.root)
            window.title(self.translations[self.language].get("downloading", "Downloading"))
            window.geometry("600x400")
            window.transient(self.root)
            window.grab_set()
            window.configure(bg=self.secondary_color)
            window.resizable(False, False)

            # Main frame
            main_frame = ttk.Frame(window, padding="10")
            main_frame.pack(fill=tk.BOTH, expand=True)
            main_frame.grid_columnconfigure(0, weight=1)
            main_frame.grid_columnconfigure(1, weight=1)
            main_frame.grid_rowconfigure(0, weight=1)
            main_frame.grid_rowconfigure(1, weight=0)
            main_frame.grid_rowconfigure(2, weight=0)
            main_frame.grid_rowconfigure(3, weight=0)
            main_frame.grid_rowconfigure(4, weight=0)
            main_frame.grid_rowconfigure(5, weight=0)
            main_frame.grid_rowconfigure(6, weight=1)

            # Progress bar
            progress_bar = ttk.Progressbar(main_frame, mode="determinate", maximum=100, length=550)
            progress_bar.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 10))

            # Status label for download stage
            status_label = ttk.Label(
                main_frame,
                text=self.translations[self.language].get("starting_download", "Starting download..."),
                style="TLabel"
            )
            status_label.grid(row=1, column=0, columnspan=2, sticky="w")

            # Labels for file info
            filename_label = ttk.Label(
                main_frame,
                text=f"{self.translations[self.language].get('file_name', 'File')}: {filename or 'غير معروف'}",
                wraplength=550,
                style="TLabel"
            )
            filename_label.grid(row=2, column=0, columnspan=2, sticky="w")

            save_path_label = ttk.Label(
                main_frame,
                text=f"{self.translations[self.language].get('save_path', 'Path')}: {self.save_path}",
                wraplength=550,
                style="TLabel"
            )
            save_path_label.grid(row=3, column=0, columnspan=2, sticky="w")

            # File size label
            file_size_text = "-- MB"
            try:
                total_bytes = int(total_bytes) if total_bytes else 0
                if total_bytes > 0:
                    file_size_text = f"{total_bytes / (1024 * 1024):.2f} MB"
            except (ValueError, TypeError):
                logging.warning(f"Invalid total_bytes value for {url}: {total_bytes}")
            file_size_label = ttk.Label(
                main_frame,
                text=f"{self.translations[self.language].get('file_size', 'File Size')}: {file_size_text}",
                style="TLabel"
            )
            file_size_label.grid(row=4, column=0, columnspan=2, sticky="w")

            # Labels for dynamic info
            speed_label = ttk.Label(
                main_frame,
                text=f"{self.translations[self.language].get('speed', 'Speed')}: 0.00 MB/s",
                style="TLabel"
            )
            speed_label.grid(row=5, column=0, sticky="w")

            eta_label = ttk.Label(
                main_frame,
                text=f"{self.translations[self.language].get('eta', 'Time remaining')}: --",
                style="TLabel"
            )
            eta_label.grid(row=5, column=1, sticky="e")

            # Buttons frame
            button_frame = ttk.Frame(main_frame)
            button_frame.grid(row=6, column=0, columnspan=2, pady=10)

            def pause_download_wrapper():
                if task_id in self.download_threads:
                    pause_event = self.download_threads[task_id].get('pause_event')
                    if pause_event and pause_event.is_set():
                        self.pause_download(task_id, pause_button, resume_button)
                        status_label.config(
                            text=self.translations[self.language].get("paused", "Paused (Low Speed)")
                        )
                        logging.debug(f"Paused download for {url}")

            def resume_download_wrapper():
                if task_id in self.download_threads:
                    pause_event = self.download_threads[task_id].get('pause_event')
                    if pause_event and not pause_event.is_set():
                        self.resume_download(task_id, pause_button, resume_button)
                        status_label.config(
                            text=self.translations[self.language].get("starting_download", "Starting download...")
                        )
                        logging.debug(f"Resumed download for {url}")

            def cancel_download_wrapper():
                if task_id in self.download_threads:
                    self.cancel_download(url, window, task_id)
                    logging.debug(f"Cancelled download for {url}")

            pause_button = ttk.Button(
                button_frame,
                text=self.translations[self.language].get("pause", "Pause"),
                command=pause_download_wrapper,
                style="Accent.TButton"
            )
            pause_button.pack(side=tk.LEFT, padx=5)

            resume_button = ttk.Button(
                button_frame,
                text=self.translations[self.language].get("resume", "Resume"),
                command=resume_download_wrapper,
                style="Accent.TButton",
                state="disabled"
            )
            resume_button.pack(side=tk.LEFT, padx=5)

            cancel_button = ttk.Button(
                button_frame,
                text=self.translations[self.language].get("cancel", "Cancel"),
                command=cancel_download_wrapper,
                style="Accent.TButton"
            )
            cancel_button.pack(side=tk.LEFT, padx=5)

            # Store window and widgets in download_windows
            self.download_windows[task_id] = {
                'window': window,
                'progress_bar': progress_bar,
                'status_label': status_label,
                'filename_label': filename_label,
                'save_path_label': save_path_label,
                'file_size_label': file_size_label,
                'speed_label': speed_label,
                'eta_label': eta_label,
                'pause_button': pause_button,
                'resume_button': resume_button,
                'cancel_button': cancel_button,
                'stage': 'initial'  # Track download stage: initial, downloading, completed
            }

            # Handle window close
            window.protocol("WM_DELETE_WINDOW", cancel_download_wrapper)

            logging.debug(f"Created download window for {url} with task_id {task_id}")
            return self.download_windows[task_id]

        except Exception as e:
            logging.error(f"Error creating download window for {url}: {str(e)}")
            return None
    def update_download_window(self, window, progress, speed, eta, size):
        """Update the progress window with current download stats."""
        try:
            tree = window['tree']
            url = tree.item(tree.get_children()[0])['values'][0]
            tree.item(tree.get_children()[0], values=(
                url,
                f"{progress:.1f}%",
                f"{speed:.2f} KB/s",
                f"{int(eta // 60)} دقيقة {int(eta % 60)} ثانية" if eta > 0 else "غير معروف",
                size
            ))
            self.root.update_idletasks()
        except Exception as e:
            logging.error(f"Error updating download window: {str(e)}")

    def update_tree_status(self, tree_item_id, status):
        """Update the status of a tree item."""
        if hasattr(self, 'batch_tree') and tree_item_id:
            try:
                self.batch_tree.item(tree_item_id, values=(
                    self.batch_tree.item(tree_item_id)['values'][0],
                    self.batch_tree.item(tree_item_id)['values'][1],
                    self.batch_tree.item(tree_item_id)['values'][2],
                    status,
                    self.batch_tree.item(tree_item_id)['values'][4]
                ))
            except Exception as e:
                logging.error(f"Error updating tree status for {tree_item_id}: {str(e)}")


    def fetch_qualities(self):
        """Fetch available video qualities for the provided URL and populate the quality combobox."""
        logging.debug("fetch_qualities called")
        url = self.url_entry.get().strip()
        if not url:
            logging.warning("URL is empty")
            self.root.after(0, lambda: messagebox.showerror(
                "خطأ", self.translations[self.language]["no_url"]))
            return

        clean_url = self.normalize_url(url)
        if not clean_url:
            logging.error("Failed to normalize URL")
            self.root.after(0, lambda: messagebox.showerror(
                "خطأ", "فشل في معالجة الرابط"))
            return

        # فحص لمنع التحليل المكرر
        if hasattr(self, 'last_fetched_url') and self.last_fetched_url == clean_url:
            logging.debug("URL already fetched, skipping re-fetch")
            return
        self.last_fetched_url = clean_url

        self.status_bar.config(text=self.translations[self.language]["fetching_qualities"])
        self.quality_button.config(state="disabled")
        self.start_download_button.config(state="disabled")

        def fetch_thread():
            max_retries = 5
            retry_delay = 3
            for attempt in range(1, max_retries + 1):
                try:
                    logging.debug(f"Attempt {attempt}/{max_retries} to fetch video info for URL: {clean_url}")
                    ydl_opts = {
                        'quiet': True,
                        'no_warnings': True,
                        'noplaylist': True,
                        'extract_flat': False,
                        'http_headers': {
                            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
                        },
                        'ignore_no_formats_error': True,
                        'socket_timeout': 60,
                        'retries': 5,
                        'fragment_retries': 5,
                        'ffmpeg_location': self.ffmpeg_path if hasattr(self, 'ffmpeg_path') else None,
                        'ignoreerrors': True,
                        'sleep_interval': 0,
                        'max_sleep_interval': 0,
                        'no_cache_dir': True,
                    }

                    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                        logging.debug(f"Extracting info for URL: {clean_url}")
                        info = ydl.extract_info(clean_url, download=False)

                        if not info:
                            logging.error("No video info returned")
                            self.root.after(0, lambda: messagebox.showerror(
                                "خطأ", "فشل في جلب معلومات الفيديو"))
                            return

                        formats = info.get('formats', [])
                        if not formats:
                            logging.warning("No formats found")
                            self.root.after(0, lambda: messagebox.showerror(
                                "خطأ", "لم يتم العثور على تنسيقات متاحة"))
                            return

                        quality_list = []
                        self.formats_cache = {}
                        video_formats = []
                        audio_formats = []

                        for f in formats:
                            try:
                                if not f.get('url') and not f.get('fragments'):
                                    logging.debug(f"Skipping format: {f.get('format_id')} (no url/fragments)")
                                    continue

                                resolution = f.get('height', 0) or 0
                                ext = f.get('ext', 'mp4')
                                if resolution > 1080:
                                    ext = 'mkv'
                                fps = f.get('fps', 0) or 0
                                filesize = f.get('filesize', 0) or f.get('filesize_approx', 0) or 0
                                format_note = f.get('format_note', '')
                                format_id = f.get('format_id', '')
                                has_video = f.get('vcodec', 'none') != 'none'
                                has_audio = f.get('acodec', 'none') != 'none'

                                if has_video:
                                    video_formats.append(f)
                                if has_audio and not has_video:
                                    audio_formats.append(f)
                                    continue

                                if not has_video:
                                    logging.debug(f"Skipping format for Combobox: {format_id} (no video)")
                                    continue

                                quality_desc = f"{resolution}p" if resolution > 0 else "غير معروف"
                                if fps > 0:
                                    quality_desc += f" {int(fps)}fps"
                                if format_note:
                                    quality_desc += f" ({format_note})"
                                if filesize:
                                    size_mb = filesize / (1024 * 1024)
                                    quality_desc += f" - {size_mb:.2f}MB"

                                quality_list.append(quality_desc)
                                self.formats_cache[quality_desc] = {
                                    'format_id': format_id,
                                    'ext': ext,
                                    'filesize': filesize,
                                    'format_note': format_note,
                                    'is_combined': has_video and has_audio,
                                    'resolution': resolution,
                                    'video_format': f,
                                    'audio_format': None
                                }
                                logging.debug(f"Added quality: {quality_desc}")
                            except Exception as e:
                                logging.error(f"Error processing format {f.get('format_id', 'unknown')}: {str(e)}")
                                continue

                        for quality_desc in quality_list:
                            format_data = self.formats_cache[quality_desc]
                            if format_data['is_combined']:
                                continue
                            best_audio = None
                            for audio_format in audio_formats:
                                if audio_format.get('ext') in ['m4a', 'mp3']:
                                    best_audio = audio_format
                                    break
                            if best_audio:
                                format_data['audio_format'] = best_audio
                                format_data['format_id'] = f"{format_data['video_format']['format_id']}+{best_audio['format_id']}"
                                format_data['ext'] = 'mkv' if format_data['resolution'] > 1080 else 'mp4'
                                format_data['filesize'] += (
                                    best_audio.get('filesize', 0) or best_audio.get('filesize_approx', 0) or 0
                                )
                                format_data['is_combined'] = False
                                logging.debug(f"Prepared manual merge for {quality_desc}")
                            else:
                                logging.warning(f"No compatible audio format found for {quality_desc}")

                        if not quality_list:
                            logging.warning("No valid qualities found")
                            self.root.after(0, lambda: messagebox.showerror(
                                "خطأ", "لا توجد تنسيقات متاحة للتنزيل (حاول اختيار جودة أخرى أو تحقق من الرابط)"))
                            return

                        def sort_key(x):
                            try:
                                res_str = x.split('p')[0].strip()
                                res = int(res_str) if res_str.isdigit() else 0
                                ext_priority = 0 if 'mp4' in x.lower() or 'mkv' in x.lower() else 1
                                fps_priority = 1 if '60fps' in x.lower() or '50fps' in x.lower() else 0
                                return (ext_priority, -res, fps_priority)
                            except Exception as e:
                                logging.error(f"Sorting error for quality string '{x}': {str(e)}")
                                return (1, 0, 0)

                        quality_list.sort(key=sort_key)
                        logging.debug(f"Quality list: {quality_list}")

                        def update_ui():
                            self.quality_combo.config(values=quality_list, state="readonly")
                            if quality_list:
                                self.quality_combo.current(0)
                                self.start_download_button.config(state="normal")
                                self.status_bar.config(text=self.translations[self.language]["found_formats"].format(len(quality_list)))
                            else:
                                self.quality_combo.config(values=["غير متاح"], state="disabled")
                                self.start_download_button.config(state="disabled")
                                self.status_bar.config(text=self.translations[self.language]["no_qualities"])

                        self.root.after(0, update_ui)
                        return

                except yt_dlp.utils.DownloadError as e:
                    error_msg = f"خطأ في جلب الجودات (محاولة {attempt}/{max_retries}): {str(e)}"
                    logging.error(error_msg)
                    if attempt == max_retries:
                        self.root.after(0, lambda: messagebox.showerror("خطأ", error_msg))
                    time.sleep(retry_delay)
                except requests.exceptions.RequestException as e:
                    error_msg = f"خطأ في الاتصال (محاولة {attempt}/{max_retries}): {str(e)}"
                    logging.error(error_msg)
                    if attempt == max_retries:
                        self.root.after(0, lambda: messagebox.showerror(
                            "خطأ", "فشل الاتصال بالخادم. تحقق من الإنترنت وحاول مجددًا."))
                    time.sleep(retry_delay)
                except Exception as e:
                    error_msg = f"خطأ غير متوقع (محاولة {attempt}/{max_retries}): {str(e)}"
                    logging.error(error_msg)
                    if attempt == max_retries:
                        self.root.after(0, lambda: messagebox.showerror("خطأ", error_msg))
                    time.sleep(retry_delay)
                finally:
                    self.root.after(0, lambda: self.quality_button.config(state="normal"))
                    self.root.after(0, lambda: self.status_bar.config(text=self.translations[self.language]["ready"]))

        threading.Thread(target=fetch_thread, daemon=True).start()



    def fetch_batch(self):
        """جلب جودات الفيديوهات للتنزيل الجماعي مع دعم قوائم التشغيل"""
        try:
            # تنظيف الكاش القديم
            self.batch_formats_cache = {}
            self.batch_urls = []
            self.batch_videos = []

            # استخراج الروابط من مربع النص
            urls_text = self.batch_urls_text.get("1.0", tk.END).strip()
            if not urls_text:
                messagebox.showerror(
                    self.translations[self.language]["error"],
                    self.translations[self.language]["no_batch_urls"]
                )
                return

            urls = [url.strip()
                              for url in urls_text.splitlines() if url.strip()]
            if not urls:
                messagebox.showerror(
                    self.translations[self.language]["error"],
                    "لم يتم العثور على روابط صالحة"
                )
                return

            # إعداد خيارات yt-dlp
            ydl_opts = {
                'quiet': True,
                'no_warnings': True,
                'extract_flat': False,  # تغيير لاستخراج معلومات كاملة للقوائم
                'http_headers': {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
                }
            }

            # جلب معلومات كل فيديو أو قائمة تشغيل
            video_info_list = []
            skipped_urls = []
            lock = threading.Lock()

            def process_url(url):
                try:
                    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                        info = ydl.extract_info(url, download=False)

                        # إذا كان الرابط لقائمة تشغيل
                        if 'entries' in info:
                            for entry in info.get('entries', []):
                                if not entry:
                                    continue
                                video_url = entry.get(
                                    'url') or entry.get('webpage_url')
                                if not video_url or not self.is_valid_url(
                                    video_url):
                                    continue

                                # جلب معلومات الفيديو الفردي
                                with yt_dlp.YoutubeDL(ydl_opts) as ydl_video:
                                    video_info = ydl_video.extract_info(
                                        video_url, download=False)
                                    formats = video_info.get('formats', [])
                                    quality_list = self._process_formats(
                                        formats)

                                    if quality_list:
                                        with lock:
                                            video_info_list.append({
                                                'url': video_url,
                                                'title': video_info.get('title', video_url),
                                                'duration': self._format_duration(video_info.get('duration', 0)),
                                                'formats': quality_list
                                            })
                                            self.batch_urls.append(video_url)
                        else:
                            # إذا كان الرابط لفيديو فردي
                            formats = info.get('formats', [])
                            quality_list = self._process_formats(formats)

                            if quality_list:
                                with lock:
                                    video_info_list.append({
                                        'url': url,
                                        'title': info.get('title', url),
                                        'duration': self._format_duration(info.get('duration', 0)),
                                        'formats': quality_list
                                    })
                                    self.batch_urls.append(url)
                except Exception as e:
                    print(f"خطأ في معالجة الرابط {url}: {e}")
                    with lock:
                        skipped_urls.append(url)

            # معالجة الروابط في خيوط متعددة
            threads = []
            for url in urls:
                thread = threading.Thread(target=process_url, args=(url,))
                threads.append(thread)
                thread.start()

            for thread in threads:
                thread.join()

            if not video_info_list:
                messagebox.showerror(
                    self.translations[self.language]["error"],
                    "لم يتم العثور على فيديوهات صالحة في الروابط المقدمة"
                )
                return

            # تخزين الفيديوهات للاستخدام لاحقاً
            self.batch_videos = video_info_list

            # عرض نافذة اختيار الجودة
            self.show_batch_quality_selection(video_info_list)

            if skipped_urls:
                messagebox.showwarning(
                    self.translations[self.language]["warning"],
                    f"تم تخطي {len(skipped_urls)} رابط بسبب أخطاء في المعالجة"
                )

        except Exception as e:
            print(f"خطأ في fetch_batch: {e}")
            messagebox.showerror(
                self.translations[self.language]["error"],
                f"فشل جلب الجودات: {e}"
            )

    def _process_formats(self, formats):
        """معالجة تنسيقات الفيديو وإرجاع قائمة الجودات"""
        quality_list = []
        for f in formats:
            resolution = f.get('height')
            ext = f.get('ext', 'N/A')
            if ext.lower() == 'webm' or not resolution:
                continue

            format_id = f.get('format_id')
            format_note = f.get('format_note', '')
            fps = f.get('fps', '')
            filesize = f.get('filesize', 0) or f.get('filesize_approx', 0)
            filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"

            description = f"{resolution}p {ext} ({format_note})" if format_note else f"{resolution}p {ext}"
            if fps:
                description += f" {fps}fps"

            quality_display = f"{description} - {filesize_mb:.2f} ميجا" if isinstance(
                filesize_mb, float) else f"{description} - {filesize_mb}"

            has_video = f.get('vcodec', 'none') != 'none'
            has_audio = f.get('acodec', 'none') != 'none'
            is_combined = has_video and has_audio

            quality_list.append(quality_display)
            self.formats_cache[quality_display] = (
                format_id, ext, filesize, format_note, is_combined
            )

        quality_list.sort(
            key=lambda x: int(x.split('p')[0]) if 'p' in x and x.split('p')[
                              0].isdigit() else 0,
            reverse=True
        )
        return quality_list

    def _format_duration(self, seconds):
        """تنسيق المدة من الثواني إلى صيغة دقائق:ثواني"""
        if not seconds:
            return "غير معروف"
        minutes = int(seconds // 60)
        seconds = int(seconds % 60)
        return f"{minutes}:{seconds:02d}"

    def show_batch_quality_selection(self, video_info_list):
        """عرض نافذة اختيار الجودة للتنزيل الجماعي مع Combobox لكل رابط"""
        quality_window = tk.Toplevel(self.root)
        quality_window.title(
            self.translations[self.language]["select_quality"])
        quality_window.geometry("900x600")
        quality_window.resizable(True, True)
        quality_window.configure(bg=self.secondary_color)

        # إطار الجدول
        tree_frame = ttk.Frame(quality_window)
        tree_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        columns = (
            self.translations[self.language]["batch_url"],
            self.translations[self.language]["title"],
            self.translations[self.language]["duration"],
            self.translations[self.language]["batch_quality"]
        )

        tree = ttk.Treeview(tree_frame, columns=columns, show="headings")
        for col in columns:
            tree.heading(col, text=col)
            tree.column(col, width=200, anchor="w")
        tree.pack(fill=tk.BOTH, expand=True)

        # Scrollbar
        tree_scroll = ttk.Scrollbar(
    tree_frame,
    orient="vertical",
     command=tree.yview)
        tree.configure(yscrollcommand=tree_scroll.set)
        tree_scroll.pack(side="right", fill="y")

        # تعبئة الجدول
        for video in video_info_list:
            url = video['url']
            title = video['title']
            duration = video['duration']
            formats = video['formats']

            item = tree.insert("", "end", values=(
                url[:50] + "..." if len(url) > 50 else url,
                title[:50] + "..." if len(title) > 50 else title,
                duration,
                formats[0] if formats else "غير متاح"
            ))

        # إطار الأزرار
        button_frame = ttk.Frame(quality_window)
        button_frame.pack(fill=tk.X, pady=5)

        ttk.Button(
            button_frame,
            text=self.translations[self.language]["start_batch"],
            command=lambda: self._start_batch_from_selection(
                tree, video_info_list, quality_window),
            style="Accent.TButton"
        ).pack(side=tk.LEFT, padx=5)

        ttk.Button(
            button_frame,
            text=self.translations[self.language]["close"],
            command=quality_window.destroy,
            style="Accent.TButton"
        ).pack(side=tk.LEFT, padx=5)

        # إعداد حدث النقر لاختيار الجودة
        tree.bind(
    "<Button-1>",
    lambda e: self._on_quality_click(
        e,
        tree,
         video_info_list))

    def _start_batch_from_selection(self, tree, video_info_list, window):
        """بدء التنزيل الجماعي بعد اختيار الجودة"""
        self.batch_download_items = []

        for item in tree.get_children():
            values = tree.item(item, 'values')
            url = next(
    (v['url'] for v in video_info_list if v['url'] in values[0]),
     None)
            quality = values[3] if len(values) > 3 else None

            if url and quality and quality != "غير متاح":
                video_info = next(
    (v for v in video_info_list if v['url'] == url), None)
                if video_info and quality in video_info['formats']:
                    format_id, ext, filesize, format_note, is_combined = self.formats_cache[
                        quality]
                    self.batch_download_items.append({
                        'url': url,
                        'title': video_info['title'],
                        'quality': quality,
                        'format_id': format_id,
                        'ext': ext,
                        'is_combined': is_combined,
                        'filesize': filesize,
                        'filesize_mb': filesize / (1024 * 1024) if filesize else 0
                    })

        if self.batch_download_items:
            window.destroy()
            self.start_batch_download()
        else:
            messagebox.showerror(
                self.translations[self.language]["error"],
                "لم يتم اختيار أي جودة صالحة للتنزيل"
            )

    def _on_quality_click(self, event, tree, video_info_list):
        """معالجة حدث النقر لاختيار الجودة مع منع التكرار"""
        # تجاهل النقرات خارج الخلايا
        region = tree.identify_region(event.x, event.y)
        if region != "cell":
            return

        # التأكد من النقر على عمود الجودة فقط
        column = tree.identify_column(event.x)
        if column != "#4":
            return

        item = tree.identify_row(event.y)
        if not item:
            return

        # التحقق من عدم وجود Combobox مفتوح بالفعل
        for child in tree.winfo_children():
            if isinstance(child, ttk.Combobox):
                child.destroy()

        values = tree.item(item, 'values')
        index = int(values[0]) - 1
        video = self.playlist_videos[index]

        # جلب الجودات إذا لم تكن محملة مسبقاً
        if video['url'] not in self.video_qualities:
            try:
                ydl_opts = {
                    'quiet': True,
                    'no_warnings': True,
                    'http_headers': {
                        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
                    }
                }
                with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                    video_info = ydl.extract_info(video['url'], download=False)
                    formats = video_info.get('formats', [])
                    quality_list = []

                    for f in formats:
                        resolution = f.get('height')
                        ext = f.get('ext', 'N/A')
                        if ext.lower() == 'webm' or not resolution:
                            continue

                        format_id = f.get('format_id')
                        format_note = f.get('format_note', '')
                        fps = f.get('fps', '')
                        filesize = f.get(
    'filesize', 0) or f.get(
        'filesize_approx', 0)
                        filesize_mb = filesize / \
                            (1024 * 1024) if filesize else "غير معروف"

                        description = f"{resolution}p {ext} ({format_note})" if format_note else f"{resolution}p {ext}"
                        if fps:
                            description += f" {fps}fps"

                        quality_display = f"{description} - {filesize_mb:.2f} ميجا" if isinstance(
                            filesize_mb, float) else f"{description} - {filesize_mb}"
                        has_video = f.get('vcodec', 'none') != 'none'
                        has_audio = f.get('acodec', 'none') != 'none'
                        is_combined = has_video and has_audio

                        quality_list.append(quality_display)
                        self.formats_cache[quality_display] = (
    format_id, ext, filesize, format_note, is_combined)

                    quality_list.sort(
    key=lambda x: int(
        x.split('p')[0]) if 'p' in x and x.split('p')[0].isdigit() else 0,
         reverse=True)
                    self.video_qualities[video['url']] = quality_list
            except Exception as e:
                messagebox.showerror("خطأ", f"فشل جلب الجودات: {e}")
                return

        # عرض Combobox لاختيار الجودة
        bbox = tree.bbox(item, column)
        if not bbox:
            return

        x, y, width, height = bbox
        quality_combo = ttk.Combobox(
            tree,
            values=self.video_qualities[video['url']],
            state="readonly",
            width=20
        )
        quality_combo.place(x=x, y=y, width=width, height=height)

        def on_quality_select(event):
            selected_quality = quality_combo.get()
            self.playlist_videos[index]['selected_quality'] = selected_quality
            tree.item(item, values=(
                index + 1,
                video['title'],
                video['duration'],
                selected_quality,
                video['filename'],
                video.get('upload_date', "غير معروف")
            ))
            quality_combo.destroy()

        quality_combo.bind("<<ComboboxSelected>>", on_quality_select)
        quality_combo.focus_set()

        def start_batch():
            self.batch_download_items = []
            added_count = 0

            for item in tree.get_children():
                url = format_selections[item]['url']
                quality = format_selections[item]['quality']

                if not quality or quality == "غير متوفر":
                    continue

                # البحث عن معلومات الفيديو
                video_info = next(
    (v for v in video_info_list if v['url'] == url), None)
                if not video_info:
                    continue

                # البحث عن معلومات الجودة
                format_key = url + quality
                if format_key in self.batch_formats_cache:
                    format_id, ext, filesize, format_note, is_combined = self.batch_formats_cache[
                        format_key]
                else:
                    continue

                # إضافة للتنزيل
                self.batch_download_items.append({
                    'url': url,
                    'title': video_info['title'],
                    'quality': quality,
                    'format_id': format_id,
                    'ext': ext,
                    'is_combined': is_combined,
                    'filesize': filesize,
                    'filesize_mb': filesize / (1024 * 1024) if filesize else 0
                })
                added_count += 1

            if added_count > 0:
                quality_window.destroy()
                self.start_batch_download()
            else:
                messagebox.showerror(
                    self.translations[self.language]["error"],
                    "لم يتم اختيار أي جودة صالحة للتنزيل"
                )

        ttk.Button(
            button_frame,
            text=self.translations[self.language]["start_batch"],
            command=start_batch,
            style="Accent.TButton"
        ).pack(side=tk.LEFT, padx=5)

        ttk.Button(
            button_frame,
            text=self.translations[self.language]["close"],
            command=quality_window.destroy,
            style="Accent.TButton"
        ).pack(side=tk.LEFT, padx=5)

    def extract_videos_from_url(self, url):
        """استخراج روابط الفيديوهات من رابط معين (يدعم القوائم)"""
        ydl_opts = {
            'quiet': True,
            'extract_flat': True,
            'force_generic_extractor': True,
        }

        try:
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(url, download=False)
                if 'entries' in info:  # إذا كان رابط قائمة تشغيل
                    return [entry['url'] for entry in info['entries']
                        if entry and entry.get('url')]
                else:  # إذا كان رابط فيديو فردي
                    return [info['url']] if info and info.get('url') else []
        except Exception as e:
            print(f"خطأ في استخراج الفيديوهات من {url}: {e}")
            return []

    def get_video_formats(self, url):
        """جلب جودات الفيديو المتاحة"""
        ydl_opts = {
            'quiet': True,
            'no_warnings': True,
        }

        try:
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(url, download=False)
                formats = info.get('formats', [])

                quality_list = []
                for f in formats:
                    if f.get('vcodec') == 'none':  # تخطي التنسيقات بدون فيديو
                        continue

                    resolution = f.get('height', 0)
                    ext = f.get('ext', 'mp4')
                    fps = f.get('fps', 0)
                    filesize = f.get('filesize') or f.get('filesize_approx', 0)
                    filesize_mb = filesize / (1024 * 1024) if filesize else 0

                    quality_str = f"{resolution}p"
                    if fps and fps > 30:
                        quality_str += f" {int(fps)}fps"
                    quality_str += f" {ext.upper()}"

                    if filesize_mb:
                        quality_str += f" ({filesize_mb:.2f}MB)"

                    # تخزين معلومات الجودة في الكاش
                    self.batch_formats_cache[quality_str] = {
                        'format_id': f['format_id'],
                        'ext': ext,
                        'filesize': filesize,
                        'filesize_mb': filesize_mb,
                        'is_combined': f.get('acodec') != 'none'
                    }

                    quality_list.append(quality_str)

                return sorted(quality_list, key=lambda x: int(
                    x.split('p')[0]), reverse=True)
        except Exception as e:
            print(f"خطأ في جلب جودات الفيديو {url}: {e}")
            return []

    def get_video_title(self, url):
        """الحصول على عنوان الفيديو"""
        ydl_opts = {'quiet': True}
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=False)
            return info.get('title', url[:30])[
                            :50] + ("..." if len(info.get('title', '')) > 50 else "")

    def get_video_duration(self, url):
        """جلب مدة الفيديو"""
        try:
            ydl_opts = {
                'quiet': True,
                'no_warnings': True,
                'http_headers': {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
                }
            }
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(url, download=False)
                duration = info.get('duration', 0)
                if duration:
                    minutes = int(duration // 60)
                    seconds = int(duration % 60)
                    return f"{minutes}:{seconds:02d}"
                return "غير معروف"
        except Exception as e:
            print(f"خطأ في جلب المدة لـ {url}: {e}")
            return "غير معروف"

    def show_quality_dialog(self, url, available_formats):
        import tkinter as tk
        from tkinter import ttk, messagebox

        dialog = tk.Toplevel(self.root)
        dialog.title(
    self.translations.get(
        self.language,
        self.translations["ar"]).get(
            "select_quality",
             "اختر الجودة"))
        dialog.geometry("400x200")
        dialog.transient(self.root)
        dialog.grab_set()

        ttk.Label(dialog,
    text=f"{self.translations.get(self.language,
    self.translations['ar']).get('batch_url',
     'الرابط')}: {url[:30]}...").pack(pady=10)
        quality_var = tk.StringVar(
    value=available_formats[0] if available_formats else 'default')
        quality_combo = ttk.Combobox(
    dialog,
    textvariable=quality_var,
    values=available_formats,
     state="readonly")
        quality_combo.pack(pady=10)

        def confirm():
            self.batch_quality_selections[url] = quality_var.get()
            dialog.destroy()

        ttk.Button(
    dialog,
    text=self.translations.get(
        self.language,
        self.translations["ar"]).get(
            "confirm",
            "تأكيد"),
            command=confirm).pack(
                pady=10)
        dialog.wait_window()

    def add_to_batch_tree(self, url, title, quality, duration):
        """إضافة فيديو إلى جدول التنزيل الجماعي"""
        format_info = self.batch_formats_cache.get(quality, {})

        self.batch_tree.insert("", "end", values=(
            url[:50] + "..." if len(url) > 50 else url,
            title,
            duration,
            quality,
            f"{format_info.get('filesize_mb', 0):.2f} MB" if format_info.get(
                'filesize_mb') else "غير معروف"
        ))

        if not hasattr(self, 'batch_download_items'):
            self.batch_download_items = []

        self.batch_download_items.append({
            'url': url,
            'title': title,
            'quality': quality,
            'format_id': format_info.get('format_id', 'best'),
            'ext': format_info.get('ext', 'mp4'),
            'is_combined': format_info.get('is_combined', False),
            'filesize': format_info.get('filesize', 0),
            'filesize_mb': format_info.get('filesize_mb', 0)
        })

    def _update_batch_treeview(self):
        for item in self.batch_tree.get_children():
            self.batch_tree.delete(item)

        for video in self.batch_videos:
            url = video['url']
            title = video['title']
            duration = video['duration']
            formats = video['formats']
            selected_quality = self.batch_quality_selections.get(
                url, formats[0] if formats else 'غير متاح')

            self.batch_tree.insert("", "end", values=(
                url[:30] + "..." if len(url) > 30 else url,
                title[:30] + "..." if len(title) > 30 else title,
                duration,
                selected_quality,
                selected_quality.split(
                    '(')[-1].replace(')', '') if formats else 'غير معروف'
            ))

        print(
    self.translations.get(
        self.language,
        self.translations["ar"]).get(
            "update_stats",
             "تم تحديث جدول التنزيل الجماعي"))

    def _update_batch_quality(self, url, quality):
        # تحديث الجودة المختارة للرابط في القاموس
        if not hasattr(self, 'batch_quality_selections'):
            self.batch_quality_selections = {}
        self.batch_quality_selections[url] = quality
        print(f"تم تحديث الجودة للرابط {url}: {quality}")

    def normalize_url(self, url):
        if not url:
            print("الرابط فارغ!")
            return None

        print(f"الرابط الأصلي: {url}")

        try:
            # معالجة روابط YouTube بجميع أشكالها
            if "youtube.com" in url or "youtu.be" in url:
                # استخراج معرف الفيديو من الروابط المختلفة
                if "youtube.com/watch?v=" in url:
                    video_id = url.split("v=")[1].split("&")[0]
                elif "youtu.be/" in url:
                    video_id = url.split("youtu.be/")[1].split("?")[0]
                elif "youtube.com/embed/" in url:
                    video_id = url.split("embed/")[1].split("?")[0]
                else:
                    return None

                if not video_id:
                    return None

                # إنشاء رابط نظيف بدون معلمات إضافية
                normalized_url = f"https://www.youtube.com/watch?v={video_id}"
                print(f"الرابط المحوّل: {normalized_url}")
                return normalized_url

            # معالجة روابط Vimeo
            elif "vimeo.com" in url:
                video_id = url.split("vimeo.com/")[1].split("?")[0]
                return f"https://vimeo.com/{video_id}"

            # إذا كان الرابط ليس من YouTube أو Vimeo، إرجاعه كما هو
            return url

        except Exception as e:
            print(f"خطأ في تحويل الرابط: {e}")
            return None

    def fetch_formats(self, url):
        normalized_url = self.normalize_url(url)
        if not normalized_url:
            print("فشل في تحويل الرابط!")
            messagebox.showerror(
                self.translations[self.language].get("error", "خطأ"),
                "فشل في تحويل الرابط!"
            )
            return None

        url = normalized_url
        print(f"جاري جلب الجودات للرابط المحوّل: {url}")

        ydl_opts = {
            'quiet': True,
            'no_warnings': True,
            'noplaylist': True,
            'format_sort': ['+res', '+fps'],
            'http_headers': {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
            },
            'simulate': True,
        }

        try:
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                print("جلب معلومات الفيديو...")
                info = ydl.extract_info(url, download=False)
                if not info:
                    print("فشل في جلب معلومات الفيديو")
                    messagebox.showerror(
                        self.translations[self.language].get("error", "خطأ"),
                        "فشل في جلب معلومات الفيديو!"
                    )
                    return None

                formats = info.get('formats', [])
                if not formats:
                    print("لم يتم العثور على جودات")
                    messagebox.showwarning(
                        self.translations[self.language].get(
                            "warning", "تحذير"),
                        "لم يتم العثور على جودات متاحة لهذا الفيديو!"
                    )
                    return None

                available_formats = []
                for fmt in formats:
                    fmt_id = fmt.get('format_id', '')
                    fmt_note = fmt.get('format_note', '')
                    fmt_ext = fmt.get('ext', 'mp4')
                    fmt_size = fmt.get('filesize', 0)
                    fmt_acodec = fmt.get('acodec', 'none')
                    fmt_vcodec = fmt.get('vcodec', 'none')

                    if fmt_ext == 'webm' or fmt_vcodec == 'none':
                        continue

                    is_combined = fmt_acodec != 'none' and fmt_vcodec != 'none'
                    resolution = fmt.get('height', 0)
                    fps = fmt.get('fps', 0)

                    quality_desc = f"{resolution}p"
                    if fps > 0:
                        quality_desc += f" {int(fps)}fps"
                    if fmt_note:
                        quality_desc += f" ({fmt_note})"

                    if fmt_size:
                        size_mb = fmt_size / (1024 * 1024)
                        quality_desc += f" - {size_mb:.2f} MB"

                    available_formats.append({
                        'format_id': fmt_id,
                        'description': quality_desc,
                        'ext': fmt_ext,
                        'is_combined': is_combined,
                        'filesize': fmt_size
                    })

                available_formats.sort(
                    key=lambda x: (x.get('height', 0)),
                    reverse=True
                )

                self.formats_cache.clear()
                quality_list = []
                for fmt in available_formats:
                    self.formats_cache[fmt['description']] = (
                        fmt['format_id'],
                        fmt['ext'],
                        fmt['filesize'],
                        fmt.get('format_note', ''),
                        fmt['is_combined']
                    )
                    quality_list.append(fmt['description'])

                print(f"تم العثور على {len(quality_list)} جودة")
                return quality_list

        except Exception as e:
            print(f"خطأ في جلب الجودات: {str(e)}")
            messagebox.showerror(
                self.translations[self.language].get("error", "خطأ"),
                f"فشل في جلب الجودات: {str(e)}"
            )
            return None

    def on_fetch_formats(self):
        url = self.url_entry.get().strip()
        if not url:
            messagebox.showwarning(
                self.translations[self.language].get("warning", "تحذير"),
                self.translations[self.language].get(
                    "no_url", "الرجاء إدخال رابط!")
            )
            return

        print(f"بدء جلب الجودات لرابط: {url}")
        formats = self.fetch_formats(url)
        if formats:
            quality_list = [
    f"{
        fmt['format_note']} ({
            fmt['filesize'] /
            (
                1024 *
                 1024):.2f} MB)" if fmt['filesize'] else fmt['format_note'] for fmt in formats]
            print(
    f"تم جلب الجودات بنجاح، تحديث القايمة المنسدلة: {quality_list}")
            self.quality_combo['values'] = quality_list
            self.quality_combo.set(
    quality_list[0] if quality_list else "اختر الجودة")
        else:
            print("فشل في جلب الجودات، إعادة القايمة للحالة الافتراضية")
            self.quality_combo['values'] = ["اختر الجودة"]
            self.quality_combo.set("اختر الجودة")

    def on_download(self):
        url = self.url_entry.get().strip()
        if not url:
            messagebox.showwarning(
                self.translations[self.language]["warning"],
                "الرجاء إدخال رابط الفيديو!"
            )
            return

        quality = self.quality_combo.get()
        if not quality or quality == "اختر الجودة":
            messagebox.showwarning(
                self.translations[self.language]["warning"],
                "الرجاء اختيار جودة للتحميل!"
            )
            return

        # بدء التحميل
        self.download(url, quality=quality)

    def download(self, url, is_batch=False, quality=None, filename=None, custom_save_path=None, is_audio=False,
                 format_id=None, ext='mp4', is_combined=False, is_general_download=False, subtitles=False, tree_item_id=None):
        """تنفيذ عملية التنزيل مع تحسين معالجة الأخطاء والتنظيف."""
        import logging
        import hashlib
        import shutil
        import threading
        import time
        import tkinter as tk
        from tkinter import ttk, messagebox
        import yt_dlp
        from datetime import datetime
        import os

        logging.basicConfig(level=logging.DEBUG)

        def safe_rename(src, dst, max_retries=5, delay=1):
            """إعادة تسمية ملف مع عدة محاولات وتأخير."""
            retries = 0
            last_error = None

            while retries < max_retries:
                try:
                    os.rename(src, dst)
                    logging.debug(f"تمت إعادة تسمية {src} إلى {dst}")
                    return True
                except (OSError, PermissionError) as e:
                    last_error = e
                    retries += 1
                    logging.warning(f"محاولة {retries}/{max_retries} لإعادة تسمية {src} إلى {dst}: {e}")
                    if retries >= max_retries:
                        break
                    time.sleep(delay * retries)

            try:
                shutil.copyfile(src, dst)
                os.remove(src)
                logging.debug(f"تم نسخ {src} إلى {dst} وحذف الأصلي")
                return True
            except Exception as e:
                logging.error(f"فشل النسخ والحذف لـ {src}: {e}")
                raise last_error

        def postprocessor_hook(d):
            """معالجة إعادة التسمية وحالة الدمج بعد اكتمال التنزيل."""
            if d['status'] == 'finished':
                temp_file = d.get('filename', '')
                final_file = temp_file.replace('.part', '') if temp_file.endswith('.part') else temp_file
                if not self.download_threads[task_id].get('merged', True) and 'Merging' in d.get('postprocessor', ''):
                    self.download_threads[task_id]['merge_completed'] = True
                    self.download_threads[task_id]['merged'] = True
                    logging.debug(f"اكتمل الدمج لـ {url}")
                    # تحديث مسار الملف إلى الملف النهائي
                    final_ext = self.download_threads[task_id]['ext']
                    final_file = os.path.splitext(final_file)[0] + f".{final_ext}"
                    if os.path.exists(temp_file) and temp_file != final_file:
                        try:
                            safe_rename(temp_file, final_file)
                            self.download_threads[task_id]['filepath'] = final_file
                        except Exception as e:
                            logging.error(f"فشل إعادة تسمية الملف المدعوم {temp_file} إلى {final_file}: {e}")

        # توحيد الرابط
        normalized_url = self.normalize_url(url)
        if not normalized_url:
            logging.error(f"رابط غير صالح: {url}")
            if is_batch and tree_item_id:
                self.update_tree_status(tree_item_id, "فشل")
            raise ValueError("Invalid URL")
        url = normalized_url
        start_time = time.time()
        file_type = "video" if not is_audio else "audio"

        # إنشاء task_id آمن باستخدام هاش الرابط
        url_hash = hashlib.md5(url.encode('utf-8')).hexdigest()
        task_id = f"download_{url_hash}"

        # تحديد نوع التنزيل للطابور
        download_type = "audio" if is_audio else ("general" if is_general_download else "video")

        # تحديد مسار الحفظ بناءً على نوع الملف
        final_save_path = custom_save_path if custom_save_path else self.save_path
        if is_audio:
            final_save_path = os.path.join(final_save_path, "Audio")
        elif is_general_download:
            final_save_path = os.path.join(final_save_path, "General")
        else:
            final_save_path = os.path.join(final_save_path, "Videos")
        os.makedirs(final_save_path, exist_ok=True)
        logging.debug(f"تم اختيار مسار الحفظ: {final_save_path} لـ {url} (نوع الملف: {file_type})")

        try:
            # إضافة المهمة إلى طابور التنزيل
            self.download_queue.append((
                url, is_batch, quality, filename, format_id, ext, is_combined, download_type
            ))
            logging.debug(f"تمت الإضافة إلى الطابور: url={url}, is_batch={is_batch}, quality={quality}, "
                          f"filename={filename}, format_id={format_id}, ext={ext}, "
                          f"is_combined={is_combined}, download_type={download_type}, tree_item_id={tree_item_id}")

            self.status_bar.config(
                text=self.translations[self.language]["added_to_queue"].format(url)
            )

            # إنشاء نافذة التنزيل فقط للتنزيلات غير الجماعية
            if not is_batch:
                self.download_windows[task_id] = self.create_download_window(url, 0, filename or "غير متوفر")
                if not self.download_windows[task_id]:
                    logging.error(f"فشل إنشاء نافذة التنزيل لـ {url}")
                    raise Exception("Failed to create download window")

            # ضبط امتداد الملف
            ext = 'mp3' if is_audio else ext

            # معالجة الجودة وformat_id
            filesize = 0
            format_note = ''
            resolution = 0
            if quality and quality in self.formats_cache:
                format_info = self.formats_cache[quality]
                format_id = format_info['format_id']
                ext = format_info['ext']
                filesize = format_info['filesize']
                format_note = format_info['format_note']
                is_combined = format_info['is_combined']
                resolution = format_info['resolution']
                logging.debug(
                    f"تم جلب الجودة من formats_cache: format_id={format_id}, ext={ext}, filesize={filesize}, is_combined={is_combined}")
            elif quality and is_batch and quality in self.batch_formats_cache.get(url, {}):
                format_info = self.batch_formats_cache[url][quality]
                format_id = format_info[0]
                ext = format_info[1]
                filesize = format_info[2] if format_info[2] else 0
                format_note = format_info[3]
                is_combined = format_info[4]
                try:
                    resolution = int(quality.split('p')[0]) if 'p' in quality else 0
                except ValueError:
                    resolution = 0
                logging.debug(
                    f"تم جلب الجودة من batch_formats_cache: format_id={format_id}, ext={ext}, filesize={filesize}, is_combined={is_combined}, resolution={resolution}")
                if is_batch and tree_item_id and filesize:
                    filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"
                    self.root.after(0, lambda: self.batch_tree.item(tree_item_id, values=(
                        self.batch_tree.item(tree_item_id)['values'][0],
                        self.batch_tree.item(tree_item_id)['values'][1],
                        self.batch_tree.item(tree_item_id)['values'][2],
                        self.batch_tree.item(tree_item_id)['values'][3],
                        f"{filesize_mb:.2f} ميجا" if isinstance(filesize_mb, float) else filesize_mb
                    )))

            # تحديد تنسيق الإخراج بناءً على الدقة مع توافق FFmpeg
            merge_output_format = 'mkv' if resolution > 1080 else 'mp4'
            if not is_audio and not self.ffmpeg_available and not is_combined:
                logging.warning("FFmpeg غير متاح، يتم فرض التنسيق المدمج")
                format_id = 'bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]'
                is_combined = True
                merge_output_format = 'mp4'

            # اختيار سلسلة التنسيق المحسن
            if is_audio:
                format_string = 'bestaudio[ext=m4a]/best'
            elif format_id:
                format_string = format_id
                if not is_combined and not is_audio and self.ffmpeg_available:
                    format_string += '+bestaudio[ext=m4a]'
            elif quality and quality in self.formats_cache:
                format_string = self.formats_cache[quality]['format_id']
                if not is_combined and not is_audio and self.ffmpeg_available:
                    format_string += '+bestaudio[ext=m4a]'
            else:
                format_string = 'bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]'

            # ضمان تنسيق الفيديو للتنزيلات غير الصوتية
            if not is_audio and '+bestaudio' not in format_string and 'bestaudio' not in format_string:
                format_string = 'bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]'
                logging.debug(f"تم فرض تنسيق الفيديو للتنزيل غير الصوتي: {format_string}")

            # إنشاء مجلد مؤقت باستخدام task_id آمن
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
            safe_task_id = self._sanitize_filename(task_id)
            temp_dir = os.path.join(final_save_path, f"temp_{safe_task_id}_{timestamp}")
            os.makedirs(temp_dir, exist_ok=True)
            logging.debug(f"تم إنشاء مجلد مؤقت: {temp_dir}")

            # خيارات yt-dlp
            ydl_opts = {
                'outtmpl': os.path.join(final_save_path, f"{filename if filename else '%(title)s'}.%(ext)s"),
                'format': format_string,
                'merge_output_format': merge_output_format if not is_audio else None,
                'ffmpeg_location': self.ffmpeg_path if self.ffmpeg_available else None,
                'writesubtitles': subtitles,
                'subtitleslangs': ['en', 'ar'],
                'noplaylist': True,
                'progress_hooks': [self.create_progress_hook()],
                'postprocessor_hooks': [postprocessor_hook],
                'http_headers': {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
                },
                'retries': 20,
                'fragment_retries': 20,
                'extractor_retries': 20,
                'file_access_retries': 10,
                'continuedl': True,
                'nooverwrites': True,
                'format_sort': ['ext:mp4', 'res'],
                'format_fallback': 'bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]',
                'keepvideo': False,
                'no_resize_buffer': True,
                'http_chunk_size': 1048576,
                'sleep_interval': 0,
                'max_sleep_interval': 0,
                'skip_unavailable_fragments': True,
                'keep_fragments': False,
                'cachedir': temp_dir,
                'socket_timeout': 60,
                'ignoreerrors': True,
                'force_generic_extractor': False,
                'prefer_ffmpeg': True,
                'no_check_certificate': True,
                'no_part': True,
            }

            if is_audio:
                ydl_opts['postprocessors'] = [{
                    'key': 'FFmpegExtractAudio',
                    'preferredcodec': 'mp3',
                    'preferredquality': '192',
                }]

            # تهيئة تتبع خيط التنزيل
            pause_event = threading.Event()
            pause_event.set()  # غير متوقف في البداية
            self.download_threads[task_id] = {
                'completed': False,
                'merge_completed': False,
                'cancel': False,
                'pause': False,
                'pause_event': pause_event,
                'ratelimit': None,
                'thread': None,
                'temp_filepath': None,
                'downloaded_bytes': 0,
                'ydl': None,
                'start_time': start_time,
                'duration': 0,
                'file_size': 0,
                'filepath': '',
                'merged': is_combined,
                'notified': False,
                'tree_item_id': tree_item_id,
                'last_update_time': start_time,
                'last_downloaded_bytes': 0,
                'url': url,
                'is_batch': is_batch,
                'quality': quality,
                'format_id': format_id,
                'ext': ext,
                'is_audio': is_audio,
                'subtitles': subtitles
            }

            # مهمة التنزيل
            def download_task():
                filepath = None
                title = "downloaded_file"
                local_filename = filename
                max_retries = 3

                try:
                    if self.download_threads[task_id]['cancel']:
                        logging.debug(f"تم إلغاء مهمة التنزيل لـ {url}")
                        return

                    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                        self.download_threads[task_id]['ydl'] = ydl
                        # استخراج المعلومات مرة واحدة
                        info = ydl.extract_info(url, download=False)
                        title = info.get('title', 'downloaded_file')
                        if not local_filename:
                            local_filename = f"{self._sanitize_filename(title)}.{ext}"
                        filepath = os.path.join(final_save_path, local_filename)

                        if os.path.exists(filepath):
                            choice = messagebox.askyesnocancel(
                                "مكرر",
                                self.translations[self.language]["duplicate_found"].format(local_filename)
                            )
                            if choice is None:
                                self.cancel_download(url, None, task_id)
                                if tree_item_id:
                                    self.update_tree_status(tree_item_id, "ملغى")
                                return
                            elif choice:
                                os.remove(filepath)
                                logging.debug(f"تم إزالة الملف الموجود: {filepath}")
                            else:
                                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                                local_filename = f"{self._sanitize_filename(title)}_{timestamp}.{ext}"
                                ydl_opts['outtmpl'] = os.path.join(final_save_path, f"{self._sanitize_filename(title)}_{timestamp}.%(ext)s")
                                filepath = os.path.join(final_save_path, local_filename)
                                logging.debug(f"استخدام اسم ملف بطابع زمني: {local_filename}")

                        # تحديث filename_label إذا كانت النافذة موجودة
                        if not is_batch and task_id in self.download_windows:
                            if ('filename_label' in self.download_windows[task_id] and
                                    self.download_windows[task_id]['filename_label'].winfo_exists()):
                                self.download_windows[task_id]['filename_label'].config(
                                    text=f"{self.translations[self.language].get('file_name', 'File')}: {local_filename}"
                                )
                            else:
                                logging.warning(f"filename_label مفقود أو تم تدميره لـ task_id {task_id}")

                        self.download_states[url] = {
                            'filename': local_filename,
                            'filepath': filepath,
                            'progress': 0,
                            'speed': 0,
                            'eta': 0,
                            'temp_filepath': None,
                            'downloaded_bytes': 0,
                            'quality': quality,
                            'is_batch': is_batch
                        }

                        self.download_threads[task_id]['filepath'] = filepath
                        self.total_tasks += 1
                        self.update_overall_progress()

                        # التنزيل مع المحاولات ومعالجة الحد الأقصى للسرعة
                        for attempt in range(max_retries):
                            while not pause_event.is_set() and not self.download_threads[task_id]['cancel']:
                                pause_event.wait()  # الانتظار إذا كان متوقفًا
                            if self.download_threads[task_id]['cancel']:
                                logging.debug(f"تم إلغاء التنزيل لـ {url}")
                                return
                            try:
                                ydl_opts['ratelimit'] = self.download_threads[task_id].get('ratelimit', None)
                                with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                                    self.download_threads[task_id]['ydl'] = ydl
                                    if 'entries' in info:  # معالجة قوائم التشغيل
                                        for entry in info['entries']:
                                            if not entry:
                                                continue
                                            video_url = entry.get('webpage_url', entry.get('url'))
                                            video_task_id = f"download_{hashlib.md5(video_url.encode('utf-8')).hexdigest()}"
                                            if video_task_id not in self.download_threads:
                                                self.download_threads[video_task_id] = self.download_threads[task_id].copy()
                                                self.download_threads[video_task_id]['url'] = video_url
                                                self.download_threads[video_task_id]['pause_event'] = threading.Event()
                                                self.download_threads[video_task_id]['pause_event'].set()
                                            ydl_opts['ratelimit'] = self.download_threads[video_task_id].get('ratelimit', None)
                                            ydl.download([video_url])
                                    else:
                                        ydl.download([url])
                                break
                            except yt_dlp.utils.DownloadError as e:
                                logging.warning(f"فشلت محاولة التنزيل {attempt + 1}/{max_retries} لـ {url}: {e}")
                                if attempt == max_retries - 1:
                                    if 'Requested format is not available' in str(e):
                                        logging.info(f"الرجوع إلى التنسيق المدمج لـ {url}")
                                        ydl_opts['format'] = 'bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]'
                                        ydl_opts.pop('allow_unplayable_formats', None)
                                        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                                            ydl.download([url])
                                        break
                                    else:
                                        raise

                        if not self.download_threads[task_id]['cancel']:
                            self.download_threads[task_id]['completed'] = True
                            if not is_audio:
                                self.download_threads[task_id]['merged'] = True
                                self.download_threads[task_id]['merge_completed'] = True
                                logging.debug(f"تم دمج الفيديو والصوت لـ {url}")

                            self.download_threads[task_id]['duration'] = time.time() - start_time
                            self.download_threads[task_id]['file_size'] = os.path.getsize(filepath) / (1024 * 1024) if os.path.exists(filepath) else 0

                            if is_batch and tree_item_id:
                                self.root.after(0, lambda: self.update_tree_status(tree_item_id, "مكتمل"))

                            try:
                                if os.path.exists(temp_dir):
                                    shutil.rmtree(temp_dir)
                                    logging.debug(f"تم حذف المجلد المؤقت: {temp_dir}")
                            except Exception as e:
                                logging.error(f"فشل حذف المجلد المؤقت {temp_dir}: {e}")

                            if (is_audio or self.download_threads[task_id]['merge_completed']) and not self.download_threads[task_id]['notified']:
                                if not is_batch:
                                    self.root.after(0, lambda: self.notify_download(url, True))
                                self.log_history(url, file_type, "نجاح", f"تم التنزيل إلى {filepath}")
                                if self.cloud_enabled:
                                    self.upload_to_cloud(filepath, url)
                                self.download_threads[task_id]['notified'] = True

                except yt_dlp.utils.DownloadError as e:
                    logging.error(f"خطأ في التنزيل لـ {url}: {e}")
                    self.log_history(url, file_type, "فشل", str(e))
                    if not is_batch and task_id in self.download_windows:
                        self.root.after(0, lambda: self.notify_download(url, False))
                    if is_batch and tree_item_id:
                        self.root.after(0, lambda: self.update_tree_status(tree_item_id, "فشل"))
                    self.download_threads[task_id]['notified'] = True
                    if is_batch:
                        raise

                except Exception as e:
                    logging.error(f"خطأ غير متوقع أثناء تنزيل {url}: {e}")
                    self.log_history(url, file_type, "فشل", str(e))
                    if not is_batch and task_id in self.download_windows:
                        self.root.after(0, lambda: self.notify_download(url, False))
                    if is_batch and tree_item_id:
                        self.root.after(0, lambda: self.update_tree_status(tree_item_id, "فشل"))
                    self.download_threads[task_id]['notified'] = True
                    if is_batch:
                        raise

                finally:
                    end_time = time.time()
                    duration = end_time - start_time
                    file_size = os.path.getsize(filepath) / (1024 * 1024) if filepath and os.path.exists(filepath) else 0
                    self.download_threads[task_id]['duration'] = duration
                    self.download_threads[task_id]['file_size'] = file_size
                    if not self.download_threads[task_id]['notified']:
                        if not is_batch:
                            self.root.after(0, lambda: self.show_custom_notification(
                                title, duration, file_size, "نجح" if filepath and os.path.exists(filepath) else "فشل"
                            ))
                        self.download_threads[task_id]['notified'] = True
                    if not is_batch and task_id in self.download_windows:
                        if ('window' in self.download_windows[task_id] and
                                self.download_windows[task_id]['window'].winfo_exists()):
                            self.download_windows[task_id]['window'].destroy()
                        del self.download_windows[task_id]
                    try:
                        temp_files = [f for f in os.listdir(final_save_path) if f and f.endswith(('.part', '.ytdl', '.temp', '.webm'))]
                        for temp_file in temp_files:
                            if temp_file:
                                os.remove(os.path.join(final_save_path, temp_file))
                                logging.debug(f"تم حذف الملف المؤقت: {temp_file}")
                        if os.path.exists(temp_dir):
                            shutil.rmtree(temp_dir)
                            logging.debug(f"تم حذف المجلد المؤقت: {temp_dir}")
                    except Exception as e:
                        logging.error(f"فشل تنظيف الملفات المؤقتة: {e}")

            self.download_threads[task_id]['thread'] = threading.Thread(target=download_task, daemon=True)
            self.download_threads[task_id]['thread'].start()
            self.log_history(url, file_type, "بدأ", f"بدأ تنزيل {filename or 'downloaded_file'}")

        except Exception as e:
            logging.error(f"خطأ غير متوقع في التنزيل {url}: {e}")
            self.log_history(url, file_type, "فشل", str(e))
            if task_id in self.download_threads:
                self.download_threads[task_id]['completed'] = True
                self.download_threads[task_id]['merge_completed'] = True
                if not self.download_threads[task_id]['notified']:
                    self.notify_download(url, False)
                    self.download_threads[task_id]['notified'] = True
            if not is_batch and task_id in self.download_windows:
                if ('window' in self.download_windows[task_id] and
                        self.download_windows[task_id]['window'].winfo_exists()):
                    self.download_windows[task_id]['window'].destroy()
                del self.download_windows[task_id]
            if is_batch and tree_item_id:
                self.update_tree_status(tree_item_id, "فشل")
            if is_batch:
                raise
    def show_batch_completion_window(self, detail):
        window = tk.Toplevel(self.root)
        window.title("اكتمل التنزيل")
        window.geometry("400x300")
        window.transient(self.root)
        window.grab_set()

        ttk.Label(
            window,
            text="تم التنزيل بنجاح!",
            style="TLabel",
            font=("Segoe UI", 14, "bold")
        ).pack(pady=10)

        info_frame = ttk.Frame(window)
        info_frame.pack(pady=5, padx=10, fill="x")

        details = [
            ("العنوان", detail.get('title', 'غير معروف')),
            ("المدة", f"{int(detail['duration']) //
    60}:{int(detail['duration']) %
     60:02d}" if detail.get('duration') else "غير معروف"),
            ("المسار", detail.get('filepath', 'غير معروف')),
            ("الحجم", f"{detail.get('filesize_mb', 0):.2f} ميجا" if detail.get(
                'filesize_mb') else "غير معروف"),
            ("التاريخ", detail.get('upload_date', 'غير معروف'))
        ]

        for label, value in details:
            row_frame = ttk.Frame(info_frame)
            row_frame.pack(fill="x", pady=2)
            ttk.Label(
    row_frame,
    text=f"{label}:",
    style="TLabel",
    width=15).pack(
        side="left")
            ttk.Label(
    row_frame,
    text=value,
    style="TLabel",
    wraplength=300).pack(
        side="left")

        button_frame = ttk.Frame(window)
        button_frame.pack(pady=10)

        ttk.Button(
            button_frame,
            text="فتح الملف",
            command=lambda: self.open_file(detail.get('filepath')),
            style="Accent.TButton"
        ).pack(side="left", padx=5)

        ttk.Button(
            button_frame,
            text="فتح المجلد",
            command=lambda: self.open_folder(
                os.path.dirname(detail.get('filepath'))),
            style="Accent.TButton"
        ).pack(side="left", padx=5)

        ttk.Button(
            button_frame,
            text="إغلاق",
            command=window.destroy,
            style="TButton"
        ).pack(side="left", padx=5)

        window.protocol("WM_DELETE_WINDOW", window.destroy)

    def update_progress(self, d, url, progress_tree, tree_item):
        """تحديث تقدم التنزيل"""
        try:
            status = d.get('status')
            if status == 'downloading':
                total_bytes = d.get('total_bytes') or d.get(
                    'total_bytes_estimate', 0)
                downloaded_bytes = d.get('downloaded_bytes', 0)
                if total_bytes > 0:
                    progress = (downloaded_bytes / total_bytes) * 100
                    progress_tree.item(tree_item, values=(
                        url[:50] + "..." if len(url) > 50 else url,
                        self.translations[self.language]["downloading"],
                        f"{progress:.1f}%"
                    ))
            elif status in ('finished', 'merge_completed'):
                progress_tree.item(tree_item, values=(
                    url[:50] + "..." if len(url) > 50 else url,
                    self.translations[self.language]["completed"],
                    "100%"
                ))
            elif status == 'error':
                progress_tree.item(tree_item, values=(
                    url[:50] + "..." if len(url) > 50 else url,
                    self.translations[self.language]["failed"],
                    "0%"
                ))
        except Exception as e:
            print(f"خطأ في update_progress لـ {url}: {e}")

    def update_progress(self, d, url, progress_bar, status_label, speed_label,
                        eta_label, filename_label, size_label, window, start_time):
        try:
            if url not in self.download_threads:
                return

            if d['status'] == 'downloading':
                filename = d.get('filename', 'Unknown')
                if window.winfo_exists():
                    filename_label.config(text=filename)

                # Ensure downloaded_bytes and total_bytes are integers, default
                # to 0 if None
                downloaded_bytes = d.get('downloaded_bytes', 0) or 0
                total_bytes = d.get(
    'total_bytes', d.get(
        'total_bytes_estimate', 0)) or 0
                self.download_threads[url]['downloaded_bytes'] = downloaded_bytes

                # Log the values for debugging
                logging.debug(
    f"update_progress for {url}: downloaded_bytes={downloaded_bytes}, total_bytes={total_bytes}")

                if total_bytes > 0 and window.winfo_exists():
                    progress = (downloaded_bytes / total_bytes) * 100
                    progress_bar['value'] = progress
                    size_label.config(
                        text=f"{total_bytes / (1024 * 1024):.2f} MB")
                else:
                    if window.winfo_exists():
                        progress_bar['value'] = 0
                        size_label.config(text="غير معروف")

                elapsed_time = time.time() - start_time
                speed = downloaded_bytes / \
                    (1024 * 1024 * elapsed_time) if elapsed_time > 0 else 0
                if window.winfo_exists():
                    speed_label.config(text=f"{speed:.2f} MB/s")

                # Calculate remaining bytes and ETA only if values are valid
                remaining_bytes = total_bytes - downloaded_bytes if total_bytes > 0 else 0
                eta = remaining_bytes / \
                    (downloaded_bytes /
     elapsed_time) if downloaded_bytes > 0 and elapsed_time > 0 else 0
                if window.winfo_exists():
                    eta_label.config(
                        text=f"{int(eta // 60)} min" if eta > 0 else "غير معروف")
                    status_label.config(text="جاري التنزيل...")

            elif d['status'] == 'finished':
                if window.winfo_exists():
                    progress_bar['value'] = 100
                    status_text = "جاري الدمج..." if not self.download_threads[url].get(
                        'merge_completed', True) else "تم التنزيل بنجاح!"
                    status_label.config(text=status_text)
                    speed_label.config(text="0.00 MB/s")
                    eta_label.config(text="0 min")

                # Ensure downloaded_bytes is an integer
                downloaded_bytes = d.get('downloaded_bytes', 0) or 0
                elapsed_time = time.time() - start_time
                self.download_threads[url]['duration'] = elapsed_time
                self.download_threads[url]['file_size'] = downloaded_bytes / \
                    (1024 * 1024)

                # تأكيد وجود merge_completed في القاموس
                if 'merge_completed' not in self.download_threads[url]:
                    self.download_threads[url]['merge_completed'] = True

                self.update_stats(downloaded_bytes, elapsed_time)

                filepath = self.download_states.get(
                    url, {}).get('filepath', None)
                if filepath and self.cloud_enabled:
                    self.upload_to_cloud(filepath)

                self.notify_download(url, True)
                title = d.get('info_dict', {}).get('title', 'Unknown')
                self.show_custom_notification(
                    title, elapsed_time, downloaded_bytes / (1024 * 1024), "Completed")

                self.total_tasks -= 1
                self.update_overall_progress()

                # التحقق من اكتمال الدمج قبل استدعاء النافذة
                def check_merge_completion():
                    if self.download_threads[url].get('merge_completed', True):
                        if window.winfo_exists():
                            self.show_post_download_window(
                                url, filepath, downloaded_bytes / (1024 * 1024), elapsed_time)
                            self.root.after(
    100, lambda: window.destroy() if window.winfo_exists() else None)
                    else:
                        self.root.after(1000, check_merge_completion)

                check_merge_completion()

            elif d['status'] == 'error':
                if window.winfo_exists():
                    status_label.config(
    text=f"خطأ: {
        d.get(
            'error',
             'خطأ غير معروف')}")
                self.download_threads[url]['completed'] = True
                self.download_threads[url]['merge_completed'] = True
                self.total_tasks -= 1
                self.update_overall_progress()

        except Exception as e:
            print(f"خطأ في update_progress لـ {url}: {str(e)}")
            if 'merge_completed' in str(e):
                self.download_threads[url]['merge_completed'] = True

    def cleanup_temp_files(self, filepath):
        """Clean up temporary files after download."""
        import logging
        import glob

        try:
            if not filepath or not isinstance(filepath, str):
                logging.warning("No valid filepath provided for cleanup, skipping")
                return

            # Get directory and filename pattern
            directory = os.path.dirname(filepath)
            filename_base = os.path.splitext(os.path.basename(filepath))[0]
            temp_patterns = [
                os.path.join(directory, f"{filename_base}*.part"),
                os.path.join(directory, f"{filename_base}*.ytdl"),
                os.path.join(directory, f"{filename_base}*.temp")
            ]

            for pattern in temp_patterns:
                for temp_file in glob.glob(pattern):
                    try:
                        if os.path.exists(temp_file):
                            os.remove(temp_file)
                            logging.info(f"Removed temporary file: {temp_file}")
                    except Exception as e:
                        logging.error(f"Error removing temporary file {temp_file}: {str(e)}")

        except Exception as e:
            logging.error(f"Unexpected error in cleanup_temp_files for {filepath}: {str(e)}")
    def pause_download(self, url, pause_button, resume_button):
        try:
            if url in self.download_threads:
                self.download_threads[url]['pause'] = True
                pause_button.config(state="disabled")
                resume_button.config(state="normal")
                if url in self.download_windows:
                    window = self.download_windows[url]
                    details_frame = window.winfo_children()[0]
                    labels = details_frame.winfo_children()
                    status_label = labels[3]
                    status_label.config(
                        text=self.translations[self.language]["paused"])
        except Exception as e:
            print(f"Error pausing download for {url}: {str(e)}")

    def start_download(self, url, save_path, file_type='videos',
                       format_id=None, ext='mp4', is_combined=False):
        try:
            if url not in self.download_threads:
                self.download_threads[url] = {'pause': False, 'thread': None}
            ydl_opts = {
                'format': format_id if format_id else 'bestvideo+bestaudio/best',
                'outtmpl': os.path.join(save_path, file_type, '%(title)s.%(ext)s'),
                'merge_output_format': ext,
                'noplaylist': True,
                'progress_hooks': [self.create_progress_hook()],
                'quiet': False,
                'no_warnings': False,
                'retries': 10,
                'continuedl': True,
            }

            # إضافة postprocessor_hooks للتحقق من اكتمال الدمج
            def postprocessor_hook(d):
                if d['status'] == 'finished':
                    if 'entries' in info:
                        for entry in info['entries']:
                            if not entry:
                                continue
                            video_url = entry.get(
                                'webpage_url', entry.get('url'))
                            if video_url in self.download_threads:
                                self.download_threads[video_url]['merge_completed'] = True
                    else:
                        self.download_threads[url]['merge_completed'] = True

            ydl_opts['postprocessor_hooks'] = [postprocessor_hook]

            if file_type == 'audios':
                ydl_opts.update({
                    'format': 'bestaudio',
                    'postprocessors': [{
                        'key': 'FFmpegExtractAudio',
                        'preferredcodec': 'mp3',
                        'preferredquality': '192',
                    }],
                    'outtmpl': os.path.join(save_path, file_type, '%(title)s.mp3'),
                })
            elif not is_combined and self.ffmpeg_available:
                ydl_opts['format'] = f"{format_id}+bestaudio[ext=m4a]" if format_id else 'bestvideo+bestaudio'
            if self.subtitles_var.get():
                ydl_opts.update({
                    'writesubtitles': True,
                    'subtitleslangs': ['all'],
                    'subtitlesformat': 'srt',
                    'outtmpl': os.path.join(save_path, file_type, '%(title)s.%(ext)s'),
                })

            batch_files = []

            def download_task():
                try:
                    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                        info = ydl.extract_info(url, download=False)
                        if 'entries' in info:
                            for entry in info['entries']:
                                if not entry:
                                    continue
                                video_url = entry.get(
                                    'webpage_url', entry.get('url'))
                                if video_url in self.download_threads and (
                                    self.download_threads[video_url]['pause'] or self.download_threads[video_url]['cancel']):
                                    continue
                                self.download_threads[video_url] = {
                                    'completed': False,
                                    'merge_completed': False,
                                    'cancel': False,
                                    'pause': False,
                                    'thread': None,
                                    'temp_filepath': None,
                                    'downloaded_bytes': 0,
                                    'ydl': None,
                                    'start_time': time.time()
                                }
                                ydl.download([video_url])
                        else:
                            ydl.download([url])

                    def check_completion():
                        all_completed = True
                        if 'entries' in info:
                            for entry in info['entries']:
                                if not entry:
                                    continue
                                video_url = entry.get(
                                    'webpage_url', entry.get('url'))
                                if video_url not in self.download_threads or not self.download_threads[video_url][
                                    'completed'] or not self.download_threads[video_url]['merge_completed']:
                                    all_completed = False
                                    break
                        else:
                            if url not in self.download_threads or not self.download_threads[url][
                                'completed'] or not self.download_threads[url]['merge_completed']:
                                all_completed = False

                        if all_completed:
                            if 'entries' in info:
                                for entry in info['entries']:
                                    if not entry:
                                        continue
                                    video_url = entry.get(
                                        'webpage_url', entry.get('url'))
                                    if video_url in self.download_threads and self.download_threads[
                                        video_url]['completed']:
                                        filepath = self.download_states.get(
                                            video_url, {}).get('filepath', None)
                                        if filepath and os.path.exists(
                                            filepath):
                                            file_size = self.download_threads[video_url].get(
                                                'file_size', 0)
                                            batch_files.append({
                                                'filename': os.path.basename(filepath),
                                                'size': file_size,
                                                'filepath': filepath
                                            })
                            else:
                                if url in self.download_threads and self.download_threads[
                                    url]['completed']:
                                    filepath = self.download_states.get(
                                        url, {}).get('filepath', None)
                                    if filepath and os.path.exists(filepath):
                                        file_size = self.download_threads[url].get(
                                            'file_size', 0)
                                        batch_files.append({
                                            'filename': os.path.basename(filepath),
                                            'size': file_size,
                                            'filepath': filepath
                                        })

                            self.log_history(
    url, "Download", "Success", "Completed")
                            if batch_files:
                                self.show_post_download_window(
    None, None, None, None, is_playlist=True, batch_files=batch_files)
                        else:
                            self.root.after(1000, check_completion)

                    check_completion()

                except Exception as e:
                    error_msg = f"Error downloading {url}: {str(e)}"
                    self.log_history(url, "Download", "Failed", error_msg)
                    print(error_msg)

            self.download_threads[url]['thread'] = threading.Thread(
                target=download_task, daemon=True)
            self.download_threads[url]['thread'].start()
            if url in self.download_windows:
                window = self.download_windows[url]
                details_frame = window.winfo_children()[0]
                labels = details_frame.winfo_children()
                status_label = labels[3]
                status_label.config(
                    text=self.translations[self.language]["downloading"])

        except Exception as e:
            print(f"Error starting download for {url}: {str(e)}")

    def cancel_download(self, url, window):
        if url in self.download_threads:
            self.download_threads[url]['cancel'] = True
            self.download_threads[url]['completed'] = True

            # إغلاق أي مقابض ydl نشطة
            if 'ydl' in self.download_threads[url] and self.download_threads[url]['ydl']:
                try:
                    self.download_threads[url]['ydl'].close()
                except:
                    pass

            # حذف الملفات المؤقتة
            temp_filepath = self.download_threads[url].get('temp_filepath')
            if temp_filepath and os.path.exists(temp_filepath):
                try:
                    os.remove(temp_filepath)
                except Exception as e:
                    print(f"فشل حذف الملف المؤقت: {e}")

            # تنظيف الذاكرة
            import gc
            gc.collect()

            self.log_history(url, "Download", "Canceled",
                             "Download canceled by user")
            self.notify_download(url, False)
            self.total_tasks -= 1
            self.update_overall_progress()

            if window and window.winfo_exists():
                window.destroy()

            if url in self.download_windows:
                del self.download_windows[url]
            if url in self.download_states:
                del self.download_states[url]

    def retry_download(self, url, file_type="Video", max_retries=3):
        retry_count = 0
        while retry_count < max_retries:
            try:
                self.download(url, file_type=file_type)
                self.log_history(
    url, file_type, "Success", "Completed after retry")
                return True
            except Exception as e:
                retry_count += 1
                error_msg = f"Retry {retry_count}/{max_retries} failed for {url}: {
    str(e)}"
                self.log_history(url, file_type, "Retrying", error_msg)
                print(error_msg)
                if retry_count == max_retries:
                    self.log_history(
    url,
    file_type,
    "Failed",
    f"Failed after {max_retries} retries: {
        str(e)}")
                    self.notify_download(url, False)
                    return False
                time.sleep(5)  # الانتظار 5 ثواني قبل المحاولة التالية

    def show_completion_window(self, completed_downloads):
        """Show a simple completion window with file details and actions."""
        import tkinter as tk
        from tkinter import ttk, messagebox
        import logging
        import os
        import subprocess

        logging.basicConfig(level=logging.DEBUG)

        try:
            # Validate input
            if not completed_downloads or not isinstance(completed_downloads, list) or not completed_downloads[0]:
                logging.error(f"Invalid completed_downloads: {completed_downloads}")
                messagebox.showerror(
                    self.translations[self.language]["error"],
                    "لا توجد تنزيلات مكتملة لعرضها" if self.language == "ar" else "No completed downloads to display"
                )
                return

            # Get the first download (for single download)
            download = completed_downloads[0]
            if not isinstance(download, dict):
                logging.error(f"Invalid download format: {download}")
                return

            # Extract details
            title = download.get('title', 'غير معروف')
            filesize_mb = download.get('filesize_mb', 0.0)
            save_path = download.get('save_path', 'غير معروف')
            duration = download.get('download_time', 0)
            speed = download.get('speed', 'غير معروف')
            quality = download.get('quality', 'N/A')
            ext = download.get('ext', 'mp4')

            # Ensure save_path points to the final file
            if not save_path.endswith(f".{ext}"):
                save_path = os.path.splitext(save_path)[0] + f".{ext}"

            window = tk.Toplevel(self.root)
            window.title(self.translations[self.language].get("download_complete", "Download Complete"))
            window.geometry("600x400")
            window.transient(self.root)
            window.grab_set()
            window.configure(bg=self.secondary_color)
            window.resizable(False, False)

            # Main frame
            main_frame = ttk.Frame(window, padding="10")
            main_frame.pack(fill=tk.BOTH, expand=True)

            # File name
            file_label = ttk.Label(
                main_frame,
                text=f"{self.translations[self.language].get('file_name', 'File Name')}: {os.path.basename(save_path)}",
                wraplength=550,
                style="TLabel"
            )
            file_label.pack(pady=10, anchor="w")

            # Details frame
            details_frame = ttk.Frame(main_frame)
            details_frame.pack(fill=tk.X, pady=5)

            # Download details
            details = [
                (self.translations[self.language].get("size", "Size"), f"{filesize_mb:.2f} MB"),
                (self.translations[self.language].get("speed", "Speed"), speed),
                (self.translations[self.language].get("duration", "Duration"), f"{duration / 60:.2f} دقيقة" if self.language == "ar" else f"{duration / 60:.2f} minutes"),
                (self.translations[self.language].get("quality", "Quality"), quality)
            ]
            for label_text, value in details:
                ttk.Label(details_frame, text=f"{label_text}: {value}", style="TLabel").pack(anchor="w", pady=2)

            # Buttons frame
            buttons_frame = ttk.Frame(main_frame)
            buttons_frame.pack(pady=20, fill=tk.X)

            # Open file button
            open_file_button = ttk.Button(
                buttons_frame,
                text=self.translations[self.language].get("open_file", "Open File"),
                command=lambda: subprocess.run(["start", "", save_path], shell=True) if os.path.exists(save_path) else messagebox.showerror(
                    self.translations[self.language]["error"],
                    f"الملف {save_path} غير موجود" if self.language == "ar" else f"File {save_path} not found"
                ),
                style="Accent.TButton"
            )
            open_file_button.pack(side=tk.LEFT, padx=5)

            # Open folder button
            open_folder_button = ttk.Button(
                buttons_frame,
                text=self.translations[self.language].get("open_folder", "Open Folder"),
                command=lambda: subprocess.run(["explorer", os.path.dirname(save_path)]) if os.path.exists(os.path.dirname(save_path)) else messagebox.showerror(
                    self.translations[self.language]["error"],
                    f"المجلد {os.path.dirname(save_path)} غير موجود" if self.language == "ar" else f"Folder {os.path.dirname(save_path)} not found"
                ),
                style="Accent.TButton"
            )
            open_folder_button.pack(side=tk.LEFT, padx=5)

            # Details button (toggle details visibility)
            details_visible = tk.BooleanVar(value=True)
            def toggle_details():
                if details_visible.get():
                    details_frame.pack_forget()
                    details_button.config(text=self.translations[self.language].get("show_details", "Show Details"))
                else:
                    details_frame.pack(fill=tk.X, pady=5, before=buttons_frame)
                    details_button.config(text=self.translations[self.language].get("hide_details", "Hide Details"))
                details_visible.set(not details_visible.get())

            details_button = ttk.Button(
                buttons_frame,
                text=self.translations[self.language].get("hide_details", "Hide Details"),
                command=toggle_details,
                style="Accent.TButton"
            )
            details_button.pack(side=tk.LEFT, padx=5)

            # Close button
            close_button = ttk.Button(
                buttons_frame,
                text=self.translations[self.language].get("close", "Close"),
                command=window.destroy,
                style="Accent.TButton"
            )
            close_button.pack(side=tk.LEFT, padx=5)

            logging.debug(f"Completion window displayed for {title}")

        except Exception as e:
            logging.error(f"Error in show_completion_window: {str(e)}")
            messagebox.showerror(
                self.translations[self.language]["error"],
                f"خطأ في عرض نافذة التنزيلات المكتملة: {e}" if self.language == "ar" else f"Error displaying completion window: {e}"
            )
    def pause_download(self, task_id, pause_button=None, resume_button=None):
        """إيقاف التنزيل مؤقتًا بتقليل السرعة لـ 1 بايت/ثانية وتحديث حالة الأزرار."""
        import os
        import json
        import logging
        import tkinter as tk
        from tkinter import ttk

        logging.basicConfig(level=logging.DEBUG)

        try:
            if task_id in self.download_threads:
                pause_event = self.download_threads[task_id].get('pause_event')
                if pause_event:
                    pause_event.clear()  # إشارة الإيقاف للواجهة
                    self.download_threads[task_id]['pause'] = True
                    self.download_threads[task_id]['ratelimit'] = 1  # ضبط السرعة لـ 1 بايت/ثانية
                    self.download_threads[task_id]['status'] = 'paused'  # وضع علامة الإيقاف
                    ydl = self.download_threads[task_id].get('ydl')
                    if ydl and hasattr(ydl, 'params'):
                        ydl.params['ratelimit'] = 1
                    if pause_button and hasattr(pause_button, 'winfo_exists') and pause_button.winfo_exists():
                        pause_button.config(state="disabled")
                    if resume_button and hasattr(resume_button, 'winfo_exists') and resume_button.winfo_exists():
                        resume_button.config(state="normal")
                    # حفظ الحالة في ملف JSON
                    temp_dir = getattr(self, 'temp_parts_dir', os.path.join(self.save_path, "temp_parts"))
                    os.makedirs(temp_dir, exist_ok=True)
                    state_file = os.path.join(temp_dir, f"{task_id}.json")
                    state = {
                        'task_id': task_id,
                        'url': self.download_threads[task_id].get('url'),
                        'save_path': self.download_threads[task_id].get('filepath') or
                                     os.path.join(self.save_path, f"{self.download_threads[task_id].get('filename')}.{self.download_threads[task_id].get('ext', 'mp4')}"),
                        'downloaded': self.download_threads[task_id].get('downloaded_bytes', 0),
                        'status': 'paused'
                    }
                    with open(state_file, 'w') as f:
                        json.dump(state, f)
                    # تحديث تبويب التنزيلات غير المكتملة
                    if hasattr(self, 'incomplete_downloads') and isinstance(self.incomplete_downloads, (tk.Widget, ttk.Widget)):
                        self.root.after(0, lambda: self.update_incomplete_downloads())
                    logging.debug(f"أوقفت التنزيل لـ task_id {task_id} بسرعة 1 بايت/ثانية، الحالة محفوظة في {state_file}")
            else:
                logging.warning(f"المهمة {task_id} غير موجودة للإيقاف")
        except Exception as e:
            logging.error(f"خطأ أثناء إيقاف التنزيل لـ task_id {task_id}: {str(e)}")

    def resume_download(self, task_id, pause_button=None, resume_button=None):
        """استئناف التنزيل بإعادة السرعة الطبيعية وتحديث حالة الأزرار."""
        import os
        import json
        import logging
        import tkinter as tk
        from tkinter import ttk

        logging.basicConfig(level=logging.DEBUG)

        try:
            if task_id in self.download_threads:
                pause_event = self.download_threads[task_id].get('pause_event')
                if pause_event:
                    pause_event.set()  # إشارة الاستئناف للواجهة
                    self.download_threads[task_id]['pause'] = False
                    self.download_threads[task_id]['ratelimit'] = None  # إعادة السرعة الطبيعية
                    self.download_threads[task_id]['status'] = 'downloading'  # وضع علامة التنزيل
                    ydl = self.download_threads[task_id].get('ydl')
                    if ydl and hasattr(ydl, 'params'):
                        ydl.params['ratelimit'] = None
                    if pause_button and hasattr(pause_button, 'winfo_exists') and pause_button.winfo_exists():
                        pause_button.config(state="normal")
                    if resume_button and hasattr(resume_button, 'winfo_exists') and resume_button.winfo_exists():
                        resume_button.config(state="disabled")
                    # تحديث الحالة في ملف JSON
                    temp_dir = getattr(self, 'temp_parts_dir', os.path.join(self.save_path, "temp_parts"))
                    state_file = os.path.join(temp_dir, f"{task_id}.json")
                    if os.path.exists(state_file):
                        with open(state_file, 'r') as f:
                            state = json.load(f)
                        state['status'] = 'downloading'
                        with open(state_file, 'w') as f:
                            json.dump(state, f)
                    # تحديث تبويب التنزيلات غير المكتملة
                    if hasattr(self, 'incomplete_downloads') and isinstance(self.incomplete_downloads, (tk.Widget, ttk.Widget)):
                        self.root.after(0, lambda: self.update_incomplete_downloads())
                    logging.debug(f"استأنفت التنزيل لـ task_id {task_id} بسرعة طبيعية، الحالة محدثة في {state_file}")
            else:
                # محاولة إعادة بدء التنزيل إذا لم يكن task_id موجودًا
                temp_dir = getattr(self, 'temp_parts_dir', os.path.join(self.save_path, "temp_parts"))
                state_file = os.path.join(temp_dir, f"{task_id}.json")
                if os.path.exists(state_file):
                    with open(state_file, 'r') as f:
                        state = json.load(f)
                    url = state.get('url')
                    save_path = state.get('save_path')
                    filename = os.path.basename(save_path)
                    ext = os.path.splitext(save_path)[1][1:] or 'mp4'
                    self.download(
                        url=url,
                        filename=filename,
                        custom_save_path=os.path.dirname(save_path),
                        ext=ext,
                        is_batch=False,
                        is_general_download=False
                    )
                    # تحديث تبويب التنزيلات غير المكتملة
                    if hasattr(self, 'incomplete_downloads') and isinstance(self.incomplete_downloads, (tk.Widget, ttk.Widget)):
                        self.root.after(0, lambda: self.update_incomplete_downloads())
                    logging.debug(f"أعدت بدء التنزيل لـ task_id {task_id} من ملف الحالة {state_file}")
                else:
                    logging.warning(f"المهمة {task_id} غير موجودة للاستئناف ولا يوجد ملف حالة")
        except Exception as e:
            logging.error(f"خطأ أثناء استئناف التنزيل لـ task_id {task_id}: {str(e)}")

    def cancel_download(self, url, temp_dir=None, task_id=None, progress_window=None):
        """إلغاء التنزيل وتنظيف الموارد"""
        import os
        import logging
        import tkinter as tk
        from tkinter import ttk

        logging.basicConfig(level=logging.DEBUG)

        try:
            self.cancelled = True
            # Find task_id if not provided
            if not task_id:
                url_hash = hashlib.md5(url.encode('utf-8')).hexdigest()
                task_id = f"download_{url_hash}"

            # Cancel download in download_threads
            if task_id in self.download_threads:
                self.download_threads[task_id]['cancel'] = True
                if 'ydl' in self.download_threads[task_id] and self.download_threads[task_id]['ydl']:
                    self.download_threads[task_id]['ydl'].params['cancel'] = True
                self.download_threads[task_id]['completed'] = True  # Mark as completed to remove from incomplete
                logging.debug(f"Cancelled download for task_id {task_id}")

            # Clean up download window
            if url in self.download_windows:
                if self.download_windows[url]['window'].winfo_exists():
                    self.download_windows[url]['window'].destroy()
                del self.download_windows[url]

            # Clean up progress window
            if progress_window and progress_window.winfo_exists():
                progress_window.destroy()

            # Clean up temp files
            if temp_dir and os.path.exists(temp_dir):
                state_file = os.path.join(temp_dir, f"{task_id}.json")
                if os.path.exists(state_file):
                    os.remove(state_file)
                    logging.debug(f"Removed state file {state_file}")

            # Update the Incomplete Downloads tab
            if hasattr(self, 'incomplete_downloads') and isinstance(self.incomplete_downloads, (tk.Widget, ttk.Widget)):
                self.root.after(0, lambda: self.update_incomplete_downloads())
            logging.info(f"Download cancelled for URL {url}")
        except Exception as e:
            logging.error(f"Error cancelling download for URL {url}: {str(e)}")

    def start_batch_download(self):
        """بدء تنزيل الروابط المختارة مع نافذة تقدم."""
        import tkinter
        from tkinter import ttk, messagebox
        import yt_dlp
        import threading
        import os
        import time
        import logging
        import hashlib
        import json

        logging.basicConfig(level=logging.DEBUG)

        # التحقق مما إذا كان هناك عناصر مختارة
        selected_items = self.batch_tree.selection()
        if not selected_items:
            messagebox.showwarning(
                self.translations[self.language]["warning"],
                self.translations[self.language]["no_selected_urls"]
            )
            logging.warning("لم يتم اختيار روابط للتنزيل الجماعي")
            return

        # التحقق من مسار الحفظ، استخدام self.save_path إذا كان فارغًا
        save_path = self.batch_path_var.get().strip() or self.save_path
        if not os.path.isdir(save_path):
            messagebox.showerror(
                self.translations[self.language]["error"],
                self.translations[self.language]["invalid_path"]
            )
            logging.error(f"مسار حفظ غير صالح: {save_path}")
            return

        # تهيئة حدث إيقاف التنزيل الجماعي
        batch_pause_event = threading.Event()
        batch_pause_event.set()  # السماح بالتنزيلات في البداية
        completed_downloads = []

        # إعداد النمط المخصص
        style = ttk.Style()
        style.configure("Custom.Treeview", font=("Segoe UI", 10))
        style.configure("Accent.TButton", font=("Segoe UI", 10), background="#4CAF50", foreground="white")
        style.map("Accent.TButton", background=[("active", "#45a049")])

        # إنشاء نافذة التقدم
        progress_window = tkinter.Toplevel(self.root)
        progress_window.title(self.translations[self.language]["download_details"])
        progress_window.geometry("700x500")
        progress_window.transient(self.root)
        progress_window.grab_set()

        # إطار التفاصيل
        details_frame = ttk.LabelFrame(progress_window, text=self.translations[self.language]["progress"])
        details_frame.pack(fill=tkinter.BOTH, expand=True, padx=5, pady=5)

        # تسمية الحالة
        status_label = ttk.Label(
            details_frame,
            text=self.translations[self.language].get("starting_download", "Starting batch download..."),
            style="TLabel"
        )
        status_label.pack(anchor="w", pady=5)

        # Treeview لتفاصيل التنزيل
        tree = ttk.Treeview(
            details_frame,
            columns=("filename", "size", "quality", "speed", "eta", "path", "progress"),
            show="headings",
            style="Custom.Treeview"
        )
        tree.heading("filename", text=self.translations[self.language]["filename"])
        tree.heading("size", text=self.translations[self.language]["size"])
        tree.heading("quality", text=self.translations[self.language]["quality"])
        tree.heading("speed", text=self.translations[self.language]["download_speed"])
        tree.heading("eta", text=self.translations[self.language]["remaining_time"])
        tree.heading("path", text=self.translations[self.language]["save_path"])
        tree.heading("progress", text=self.translations[self.language]["progress"])
        tree.column("filename", width=150)
        tree.column("size", width=80)
        tree.column("quality", width=100)
        tree.column("speed", width=100)
        tree.column("eta", width=100)
        tree.column("path", width=150)
        tree.column("progress", width=100)
        tree.pack(fill=tkinter.BOTH, expand=True)

        # إطار أشرطة التقدم
        progress_bars_frame = ttk.Frame(details_frame)
        progress_bars_frame.pack(fill=tkinter.X, padx=5, pady=5)
        progress_bars = {}
        task_ids = {}

        # إضافة الروابط إلى Treeview وتهيئة أشرطة التقدم
        for item in selected_items:
            values = self.batch_tree.item(item)["values"]
            url = values[0] if len(values[0]) <= 53 else next((u for u in self.batch_urls if u.startswith(values[0][:-3])), values[0])
            title = values[1]
            sanitized_title = self._sanitize_filename(title)
            duration = values[2]
            quality = self.batch_quality_selections.get(url, values[3])
            size = values[4]
            url_hash = hashlib.md5(url.encode('utf-8')).hexdigest()
            task_id = f"download_{url_hash}"
            task_ids[sanitized_title] = task_id
            tree.insert("", "end", values=(sanitized_title, size, quality, "0.00 MB/s", "--", save_path, "0%"))
            pb = ttk.Progressbar(progress_bars_frame, mode="determinate", length=200)
            pb.pack(fill=tkinter.X, pady=2)
            progress_bars[sanitized_title] = pb
            logging.debug(f"تمت إضافة {sanitized_title} إلى نافذة التقدم بجودة {quality}, task_id: {task_id}")

        # إطار أزرار التحكم
        control_frame = ttk.Frame(progress_window)
        control_frame.pack(fill=tk.X, padx=5, pady=5)

        def pause_downloads():
            batch_pause_event.clear()
            status_label.configure(text=self.translations[self.language].get("paused", "Paused (Low Speed)"))
            for item in selected_items:
                values = self.batch_tree.item(item)["values"]
                title = self._sanitize_filename(values[1])
                task_id = task_ids.get(title)
                if task_id in self.download_threads:
                    self.pause_download(task_id, pause_button, resume_button)
            logging.debug("تم إيقاف جميع التنزيلات الجماعية")

        def resume_downloads():
            batch_pause_event.set()
            status_label.configure(text=self.translations[self.language].get("starting_download", "Starting batch download..."))
            for item in selected_items:
                values = self.batch_tree.item(item)["values"]
                title = self._sanitize_filename(values[1])
                task_id = task_ids.get(title)
                if task_id in self.download_threads:
                    self.resume_download(task_id, pause_button, resume_button)
            logging.debug("تم استئناف جميع التنزيلات الجماعية")

        pause_button = ttk.Button(
            control_frame,
            text=self.translations[self.language]["pause_download"],
            command=pause_downloads,
            style="Accent.TButton"
        )
        pause_button.pack(side=tkinter.LEFT, padx=5)

        resume_button = ttk.Button(
            control_frame,
            text=self.translations[self.language]["resume_download"],
            command=resume_downloads,
            state="disabled",
            style="Accent.TButton"
        )
        resume_button.pack(side=tkinter.LEFT, padx=5)

        def cancel_downloads():
            batch_pause_event.set()  # التأكد من خروج الحلقة
            for item in selected_items:
                values = self.batch_tree.item(item)["values"]
                url = values[0] if len(values[0]) <= 53 else next((u for u in self.batch_urls if u.startswith(values[0][:-3])), values[0])
                self.cancel_download(url, temp_dir=os.path.join(save_path, "temp_parts"), progress_window=progress_window)
            self.start_batch_button.configure(state="normal")
            self.status_bar.configure(text=self.translations[self.language]["canceled"])
            logging.info("تم إلغاء التنزيل الجماعي")
            progress_window.destroy()

        cancel_button = ttk.Button(
            control_frame,
            text=self.translations[self.language]["cancel_download"],
            command=cancel_downloads,
            style="Accent.TButton"
        )
        cancel_button.pack(side=tkinter.LEFT, padx=5)

        def progress_hook(d):
            if not batch_pause_event.is_set():
                return

            url = d.get('info_dict', {}).get('webpage_url', 'unknown')
            url_hash = hashlib.md5(url.encode('utf-8')).hexdigest()
            task_id = f"download_{url_hash}"

            if task_id not in self.download_threads or not self.download_threads[task_id].get('pause_event', threading.Event()).is_set():
                return

            title = self._sanitize_filename(d.get('info_dict', {}).get('title', 'Unknown'))
            if d['status'] == 'downloading':
                speed = d.get('speed', 0) / (1024 * 1024)  # ميجابايت/ثانية
                eta = d.get('eta', 0)
                eta_text = f"{int(eta // 60)} دقيقة" if self.language == "ar" else f"{int(eta // 60)} minutes" if eta >= 60 else \
                           f"{int(eta)} ثانية" if self.language == "ar" else f"{int(eta)} seconds"
                total_bytes = d.get('total_bytes') or d.get('total_bytes_estimated') or 0
                downloaded_bytes = d.get('downloaded_bytes', 0)
                progress = (downloaded_bytes / total_bytes * 100) if total_bytes > 0 else 0
                # تحديث download_threads
                self.download_threads[task_id]['downloaded_bytes'] = downloaded_bytes
                filesize_mb = total_bytes / (1024 * 1024) if total_bytes > 0 else 0
                quality = self.download_threads[task_id].get('quality', 'Unknown')
                filepath = self.download_threads[task_id].get('filepath', save_path)
                # تحديث Treeview وشريط التقدم
                for item in tree.get_children():
                    if tree.item(item, 'values')[0] == title:
                        tree.item(item, values=(
                            title,
                            f"{filesize_mb:.2f} MB",
                            quality,
                            f"{speed:.2f} MB/s",
                            eta_text,
                            filepath,
                            f"{progress:.1f}%"
                        ))
                        break
                if title in progress_bars and progress_bars[title].winfo_exists():
                    progress_bars[title].configure(value=progress)
                self.root.update_idletasks()
            elif d['status'] == 'finished':
                filepath = d.get('filename', '')
                if not filepath:
                    filepath = self.download_threads[task_id].get('filepath', save_path)
                filesize_mb = os.path.getsize(filepath) / (1024 * 1024) if os.path.exists(filepath) else 0
                quality = self.download_threads[task_id].get('quality', 'Unknown')
                ext = self.download_threads[task_id].get('ext', 'mp4')
                download_time = time.time() - self.download_threads[task_id].get('start_time', time.time())
                completed_downloads.append({
                    'title': title,
                    'filesize_mb': filesize_mb,
                    'quality': quality,
                    'save_path': filepath,
                    'download_time': download_time,
                    'ext': ext
                })
                for item in tree.get_children():
                    if tree.item(item, 'values')[0] == title:
                        tree.item(item, values=(
                            title,
                            f"{filesize_mb:.2f} MB",
                            quality,
                            "0.00 MB/s",
                            "مكتمل",
                            filepath,
                            "100%"
                        ))
                        break
                if title in progress_bars and progress_bars[title].winfo_exists():
                    progress_bars[title].configure(value=100)
                self.root.update_idletasks()
                logging.debug(f"اكتمل تنزيل {title} إلى {filepath}")

        # بدء التنزيلات
        def start_downloads():
            self.start_batch_button.configure(state="disabled")
            status_label.configure(text=self.translations[self.language].get("downloading", "Downloading..."))
            self.status_bar.configure(text=self.translations[self.language]["downloading"])
            temp_dir = os.path.join(save_path, "temp_parts")
            os.makedirs(temp_dir, exist_ok=True)

            for item in selected_items:
                if not batch_pause_event.is_set():
                    batch_pause_event.wait()

                values = self.batch_tree.item(item)["values"]
                url = values[0] if len(values[0]) <= 53 else next((u for u in self.batch_urls if u.startswith(values[0][:-3])), values[0])
                title = values[1]
                sanitized_title = self._sanitize_filename(title)
                quality = self.batch_quality_selections.get(url, values[3])
                clean_quality = quality.split(' - ')[0].strip() if quality and ' - ' in quality else quality
                url_hash = hashlib.md5(url.encode('utf-8')).hexdigest()
                task_id = f"download_{url_hash}"

                format_id = None
                ext = 'mp4'
                is_combined = True
                is_audio_only = False
                include_subtitles = False
                filesize = 0

                if clean_quality in self.batch_formats_cache.get(url, {}):
                    format_info = self.batch_formats_cache[url][clean_quality]
                    format_id = format_info[0]
                    ext = format_info[1]
                    filesize = format_info[2] if format_info[2] else 0
                    is_combined = format_info[4]
                elif clean_quality == "best":
                    format_id = "bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]"
                else:
                    format_id = "bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]"

                download_type = self.download_type_combo.get()
                if download_type == self.translations[self.language]["audio_only"]:
                    is_audio_only = True
                    format_id = "bestaudio[ext=m4a]"
                    ext = "mp3"
                elif download_type == self.translations[self.language]["video_with_subtitles"]:
                    include_subtitles = True

                # تهيئة download_threads
                self.download_threads[task_id] = {
                    'url': url,
                    'completed': False,
                    'merge_completed': False,
                    'cancel': False,
                    'pause': False,
                    'pause_event': threading.Event(),
                    'ratelimit': None,
                    'thread': None,
                    'temp_filepath': None,
                    'downloaded_bytes': 0,
                    'ydl': None,
                    'start_time': time.time(),
                    'duration': 0,
                    'file_size': filesize,
                    'filepath': os.path.join(save_path, f"{sanitized_title}.{ext}"),
                    'merged': is_combined,
                    'notified': False,
                    'tree_item_id': item,
                    'last_update_time': time.time(),
                    'last_downloaded_bytes': 0,
                    'quality': clean_quality,
                    'format_id': format_id,
                    'ext': ext,
                    'is_audio': is_audio_only,
                    'subtitles': include_subtitles,
                    'is_batch': True
                }
                self.download_threads[task_id]['pause_event'].set()

                # بدء التنزيل
                try:
                    self.download(
                        url=url,
                        is_batch=True,
                        quality=clean_quality,
                        filename=sanitized_title,
                        custom_save_path=save_path,
                        is_audio=is_audio_only,
                        format_id=format_id,
                        ext=ext,
                        is_combined=is_combined,
                        is_general_download=False,
                        subtitles=include_subtitles,
                        tree_item_id=item
                    )
                except Exception as e:
                    logging.error(f"فشل بدء التنزيل لـ {url}: {str(e)}")
                    for tree_item in tree.get_children():
                        if tree.item(tree_item, 'values')[0] == sanitized_title:
                            tree.item(tree_item, values=(
                                sanitized_title,
                                "غير معروف",
                                clean_quality,
                                "0.00 MB/s",
                                "فشل",
                                save_path,
                                "0%"
                            ))
                            break
                    if sanitized_title in progress_bars:
                        progress_bars[sanitized_title].configure(value=0)

            # مراقبة اكتمال التنزيلات
            def check_completion():
                all_completed = all(
                    self.download_threads.get(task_ids.get(self._sanitize_filename(values[1])), {}).get('completed', False)
                    for item in selected_items
                    for values in [self.batch_tree.item(item)["values"]]
                )
                if all_completed:
                    self.start_batch_button.configure(state="normal")
                    status_label.configure(text=self.translations[self.language].get("completed", "Batch download completed"))
                    self.status_bar.configure(text=self.translations[self.language]["completed"])
                    if completed_downloads:
                        self.show_completion_window(completed_downloads)
                    progress_window.destroy()
                    # تنظيف الملفات المؤقتة
                    try:
                        if os.path.exists(temp_dir):
                            shutil.rmtree(temp_dir)
                            logging.debug(f"تم حذف المجلد المؤقت: {temp_dir}")
                    except Exception as e:
                        logging.error(f"فشل حذف المجلد المؤقت {temp_dir}: {e}")
                else:
                    progress_window.after(1000, check_completion)

            progress_window.after(1000, check_completion)

        # بدء التنزيلات في خيط منفصل
        threading.Thread(target=start_downloads, daemon=True).start()
    def start_download(self):
        """بدء عملية التنزيل."""
        import tkinter
        from tkinter import ttk, messagebox
        import yt_dlp
        import threading
        import os
        import time
        import logging
        import hashlib

        logging.basicConfig(level=logging.DEBUG)

        url = self.url_entry.get().strip()
        if not url:
            messagebox.showerror("خطأ", self.translations[self.language]["no_url"])
            return

        if not self.is_valid_url(url):
            messagebox.showerror("خطأ", self.translations[self.language]["invalid_url"])
            return

        download_path = self.save_path
        if not download_path or not os.path.isdir(download_path):
            messagebox.showerror("خطأ", self.translations[self.language]["invalid_path"])
            return

        if self.active_downloads >= self.max_workers:
            messagebox.showwarning("تحذير", self.translations[self.language]["max_downloads_reached"])
            return

        selected_quality = self.quality_combo.get()
        title = self.get_video_title(url)
        clean_url = self.normalize_url(url)
        download_type = self.download_type_combo.get()
        is_audio_only = download_type == self.translations[self.language]["audio_only"]
        include_subtitles = download_type == self.translations[self.language]["video_with_subtitles"]

        # تنظيف العنوان لتجنب أخطاء الصياغة
        sanitized_title = self._sanitize_filename(title) if title else "downloaded_file"

        # إنشاء task_id
        url_hash = hashlib.md5(clean_url.encode('utf-8')).hexdigest()
        task_id = f"download_{url_hash}"

        # التحقق مما إذا كانت هناك جودات متاحة
        format_id = None
        ext = None
        is_combined = True
        filesize_mb = 0.0
        resolution = 0

        if selected_quality and selected_quality in self.formats_cache:
            format_info = self.formats_cache[selected_quality]
            format_id = format_info['format_id']
            ext = format_info['ext']
            filesize = format_info['filesize']
            is_combined = format_info['is_combined']
            resolution = format_info['resolution']
            filesize_mb = filesize / (1024 * 1024) if filesize else 0.0
        else:
            ydl_opts = {
                'quiet': True,
                'no_warnings': True,
                'noplaylist': True,
                'http_headers': {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
                },
                'ffmpeg_location': self.ffmpeg_path if self.ffmpeg_available else None,
                'merge_output_format': 'mp4',
                'ignoreerrors': True,
                'socket_timeout': 60,
                'retries': 15,
                'fragment_retries': 15,
                'skip_unavailable_fragments': True,
                'prefer_ffmpeg': True,
            }
            try:
                with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                    info = ydl.extract_info(clean_url, download=False)
                    formats = info.get('formats', [])
                    for f in sorted(formats, key=lambda x: x.get('height', 0) or 0, reverse=True):
                        if f.get('ext', '').lower() == 'webm':
                            continue
                        if f.get('height') is None or (f.get('filesize') is None and f.get('filesize_approx') is None):
                            continue
                        format_id = f.get('format_id')
                        ext = f.get('ext', 'mp4')
                        filesize = f.get('filesize', 0) or f.get('filesize_approx', 0)
                        filesize_mb = filesize / (1024 * 1024) if filesize else 0.0
                        resolution = f.get('height', 0)
                        has_video = f.get('vcodec', 'none') != 'none'
                        has_audio = f.get('acodec', 'none') != 'none'
                        is_combined = has_video and has_audio
                        if is_combined:
                            break
                    if not format_id or not is_combined:
                        format_id = 'bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]'
                        ext = 'mkv' if resolution > 1080 else 'mp4'
                        logging.warning("لم يتم العثور على تنسيق مدمج مناسب، يتم الرجوع إلى bestvideo+bestaudio")
            except Exception as e:
                messagebox.showerror("خطأ", f"فشل جلب بيانات الرابط: {str(e)}")
                logging.error(f"خطأ في جلب التنسيق الافتراضي: {str(e)}")
                return

        if is_audio_only:
            format_id = "bestaudio[ext=m4a]"
            ext = "mp3"

        # إنشاء نافذة تقدم متقدمة
        total_bytes = filesize_mb * 1024 * 1024 if filesize_mb else 0
        window = self.create_download_window(clean_url, total_bytes, sanitized_title)
        if not window:
            messagebox.showerror("خطأ", "فشل إنشاء نافذة التنزيل")
            return
        self.download_windows[task_id] = window

        # إعداد بيانات التنزيل في download_threads
        self.download_threads[task_id] = {
            'completed': False,
            'merge_completed': False,
            'cancel': False,
            'pause': False,
            'pause_event': threading.Event(),
            'ratelimit': None,
            'thread': None,
            'temp_filepath': None,
            'downloaded_bytes': 0,
            'ydl': None,
            'start_time': time.time(),
            'duration': 0,
            'file_size': total_bytes,
            'filepath': '',
            'merged': is_combined,
            'notified': False,
            'tree_item_id': None,
            'last_update_time': time.time(),
            'last_downloaded_bytes': 0,
            'url': clean_url,
            'is_batch': False,
            'quality': selected_quality,
            'format_id': format_id,
            'ext': ext,
            'is_audio': is_audio_only,
            'subtitles': include_subtitles
        }
        self.download_threads[task_id]['pause_event'].set()

        # بدء التنزيل في خيط منفصل
        self.active_downloads += 1
        self.download_queue.append(clean_url)
        threading.Thread(
            target=self.download,
            kwargs={
                'url': clean_url,
                'is_batch': False,
                'quality': selected_quality,
                'filename': sanitized_title,
                'format_id': format_id,
                'ext': ext,
                'is_combined': is_combined,
                'is_general_download': False,
                'is_audio': is_audio_only,
                'subtitles': include_subtitles
            },
            daemon=True
        ).start()
    def confirm_selection(self):
        """Confirm the selected quality for a batch download item."""
        import logging
        logging.basicConfig(level=logging.DEBUG)

        def clean_quality_key(quality):
            """Remove filesize part from quality string."""
            return quality.split(' - ')[0].strip() if ' - ' in quality else quality

        # Assuming this is called within a popup or similar context
        # Get the selected quality and URL (context-specific)
        # This is a placeholder; adjust based on actual implementation
        for item in self.batch_download_items:
            url = item['url']
            selected_quality = item['quality']
            clean_quality = clean_quality_key(selected_quality)
            
            if url in self.batch_formats_cache and clean_quality in self.batch_formats_cache[url]:
                format_id, ext, filesize, format_note, is_combined = self.batch_formats_cache[url][clean_quality]
                filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"
                
                # Update the item in batch_download_items
                item.update({
                    'quality': clean_quality,
                    'format_id': format_id,
                    'ext': ext,
                    'filesize_mb': filesize_mb,
                    'is_combined': is_combined
                })
                
                # Update Treeview
                self.batch_tree.item(item['tree_item_id'], values=(
                    item['url'][:50] + "..." if len(item['url']) > 50 else item['url'],
                    item['title'],
                    item['duration'],
                    clean_quality,
                    f"{filesize_mb:.2f} ميجا" if isinstance(filesize_mb, float) else filesize_mb
                ))
                logging.debug(f"Confirmed quality {clean_quality} for URL {url}")
            else:
                logging.error(f"Quality {clean_quality} not found for URL {url}")
                messagebox.showerror(
                    self.translations[self.language]["error"],
                    f"الجودة {clean_quality} غير متوفرة لـ {url}"
                )

    def url_hash(self, url):
        """إنشاء هاش فريد للرابط لتجنب تضارب الأسماء"""
        return hashlib.md5(url.encode('utf-8')).hexdigest()[:8]


    def download_selected_videos(self):
        """Download selected videos from the playlist with progress windows."""
        import tkinter as tk
        from tkinter import ttk, messagebox
        import yt_dlp
        import threading
        import os
        import time
        import logging
        import hashlib

        logging.basicConfig(level=logging.DEBUG)

        selected_items = self.playlist_tree.selection()
        if not selected_items:
            messagebox.showwarning("تحذير", "يرجى تحديد فيديو واحد على الأقل")
            logging.warning("No videos selected for playlist download")
            return

        download_path = self.playlist_path_entry.get().strip() or self.save_path
        if not os.path.isdir(download_path):
            messagebox.showerror("خطأ", self.translations[self.language]["no_download_path"])
            logging.error(f"Invalid download path: {download_path}")
            return

        completed_downloads = []

        for item in selected_items:
            index = int(self.playlist_tree.item(item)['values'][0]) - 1
            video = self.playlist_videos[index]
            url = video['url']
            filename = video['filename']
            selected_quality = video.get('selected_quality', self.single_quality_value)
            is_audio = self.extract_audio_var.get()

            if not selected_quality or selected_quality == "غير محدد":
                messagebox.showwarning("تحذير", f"يرجى تحديد جودة للفيديو: {video['title']}")
                logging.warning(f"No quality selected for video: {video['title']}")
                continue

            # Get format info
            format_id = None
            ext = 'mp4'
            is_combined = True
            filesize = 0
            if selected_quality in self.playlist_formats_cache.get(url, {}):
                format_id, ext, filesize, format_note, is_combined = self.playlist_formats_cache[url][selected_quality]
            if is_audio:
                format_id = 'bestaudio[ext=m4a]'
                ext = 'mp3'

            # Generate task_id
            url_hash = hashlib.md5(url.encode('utf-8')).hexdigest()
            task_id = f"download_{url_hash}"

            # Create download window
            total_bytes = filesize if filesize else 0
            window = self.create_download_window(url, total_bytes, filename)
            if not window:
                messagebox.showerror("خطأ", "فشل إنشاء نافذة التنزيل")
                logging.error(f"Failed to create download window for {url}")
                continue
            self.download_windows[task_id] = window

            # Initialize download thread tracking
            pause_event = threading.Event()
            pause_event.set()
            self.download_threads[task_id] = {
                'completed': False,
                'merge_completed': False,
                'cancel': False,
                'pause': False,
                'pause_event': pause_event,
                'ratelimit': None,
                'thread': None,
                'temp_filepath': None,
                'downloaded_bytes': 0,
                'ydl': None,
                'start_time': time.time(),
                'duration': 0,
                'file_size': total_bytes,
                'filepath': '',
                'merged': is_combined,
                'notified': False,
                'tree_item_id': item,
                'last_update_time': time.time(),
                'last_downloaded_bytes': 0,
                'url': url,
                'is_batch': False,
                'quality': selected_quality,
                'format_id': format_id,
                'ext': ext,
                'is_audio': is_audio,
                'subtitles': False
            }

            # Start download
            self.active_downloads += 1
            threading.Thread(
                target=self.download,
                kwargs={
                    'url': url,
                    'is_batch': False,
                    'quality': selected_quality,
                    'filename': filename,
                    'custom_save_path': download_path,
                    'is_audio': is_audio,
                    'format_id': format_id,
                    'ext': ext,
                    'is_combined': is_combined,
                    'is_general_download': False,
                    'subtitles': False,
                    'tree_item_id': item
                },
                daemon=True
            ).start()

        # Check completion
        def check_downloads():
            all_completed = True
            for item in selected_items:
                index = int(self.playlist_tree.item(item, 'values')[0]) - 1
                video = self.playlist_videos[index]
                url = video['url']
                url_hash = hashlib.md5(url.encode('utf-8')).hexdigest()
                task_id = f"download_{url_hash}"
                if task_id in self.download_threads and not self.download_threads[task_id]['completed']:
                    all_completed = False
                    break

            if all_completed:
                for item in selected_items:
                    index = int(self.playlist_tree.item(item, 'values')[0]) - 1
                    video = self.playlist_videos[index]
                    url = video['url']
                    filename = video['filename']
                    url_hash = hashlib.md5(url.encode('utf-8')).hexdigest()
                    task_id = f"download_{url_hash}"
                    if task_id in self.download_threads:
                        filepath = self.download_threads[task_id]['filepath']
                        duration = self.download_threads[task_id]['duration']
                        file_size = self.download_threads[task_id]['file_size']
                        completed_downloads.append({
                            'title': video['title'],
                            'filesize_mb': file_size,
                            'quality': self.download_threads[task_id].get('quality', 'N/A'),
                            'save_path': filepath,
                            'download_time': duration,
                            'speed': f"{file_size / duration:.2f} MB/s" if duration > 0 else "Unknown",
                            'ext': self.download_threads[task_id]['ext']
                        })
                self.root.after(0, lambda: self.show_completion_window(completed_downloads))
                logging.info("Playlist download completed")
            else:
                self.root.after(1000, check_downloads)

        check_downloads()

    def extract_audio_from_playlist(self):
        selected_items = self.playlist_tree.selection()
        if not selected_items:
            messagebox.showerror("خطأ", "لم يتم تحديد فيديوهات")
            return
        save_path = self.playlist_path_entry.get().strip()
        if not os.path.isdir(save_path):
            messagebox.showerror("خطأ", "مسار الحفظ غير صالح")
            return
        self.playlist_save_path = save_path
        quality = self.single_quality_value
        if not quality:
            messagebox.showerror("خطأ", "يرجى اختيار جودة أولاً")
            return

        # قائمة لتخزين تفاصيل التنزيل
        download_details = []

        for item in selected_items:
            index = int(self.playlist_tree.item(item, 'values')[0]) - 1
            video = self.playlist_videos[index]
            url = video['url']
            filename = video['filename'].replace('.mp4', '.mp3')
            self.download(url, quality=quality, filename=filename, custom_save_path=self.playlist_save_path, is_audio=True)
            self.playlist_tree.item(item, values=(
                index + 1,
                video['title'],
                video['duration'],
                quality,
                filename
            ))

        # انتظار انتهاء كل التنزيلات
        def check_downloads():
            all_completed = True
            for item in selected_items:
                index = int(self.playlist_tree.item(item, 'values')[0]) - 1
                video = self.playlist_videos[index]
                url = video['url']
                if url in self.download_threads and not self.download_threads[url]['completed']:
                    all_completed = False
                    break

            if all_completed:
                # جمع تفاصيل التنزيل
                for item in selected_items:
                    index = int(self.playlist_tree.item(item, 'values')[0]) - 1
                    video = self.playlist_videos[index]
                    url = video['url']
                    if url in self.download_threads:
                        duration = self.download_threads[url].get('duration', 0)
                        file_size = self.download_threads[url].get('file_size', 0)
                        download_details.append({
                            'title': video['title'],
                            'duration': duration,
                            'file_size': file_size,
                            'status': "نجح" if file_size > 0 else "فشل"
                        })

                # عرض نافذة الانتهاء
                self.show_completion_window(download_details)
            else:
                self.root.after(1000, check_downloads)

        check_downloads()

    def export_playlist_data(self):
        if not self.playlist_videos:
            messagebox.showerror("خطأ", "لا توجد بيانات لقائمة التشغيل لتصديرها")
            return

        # طلب مسار حفظ الملف من المستخدم
        save_path = filedialog.asksaveasfilename(
            initialdir=self.playlist_save_path,
            defaultextension=".json" if self.export_format_var.get() == "JSON" else ".csv",
            filetypes=[("JSON files", "*.json"), ("CSV files", "*.csv")],
            title="اختر مكان حفظ الملف"
        )
        if not save_path:
            return

        # إعداد البيانات للتصدير
        playlist_data = []
        for video in self.playlist_videos:
            playlist_data.append({
                "title": video["title"],
                "url": video["url"],
                "duration": video["duration"],
                "filename": video["filename"]
            })

        try:
            if self.export_format_var.get() == "JSON":
                # تصدير إلى JSON
                import json
                with open(save_path, "w", encoding="utf-8") as f:
                    json.dump(playlist_data, f, ensure_ascii=False, indent=4)
                messagebox.showinfo("نجاح", f"تم تصدير البيانات إلى {save_path}")
            else:
                # تصدير إلى CSV
                import csv
                with open(save_path, "w", encoding="utf-8", newline="") as f:
                    writer = csv.DictWriter(f, fieldnames=["title", "url", "duration", "filename"])
                    writer.writeheader()
                    writer.writerows(playlist_data)
                messagebox.showinfo("نجاح", f"تم تصدير البيانات إلى {save_path}")
        except Exception as e:
            messagebox.showerror("خطأ", f"فشل تصدير البيانات: {e}")

    def export_subtitles(self):
        selected_items = self.playlist_tree.selection()
        if not selected_items:
            messagebox.showerror("خطأ", "لم يتم تحديد فيديوهات")
            return

        # طلب مسار حفظ الترجمات من المستخدم
        save_path = filedialog.askdirectory(
            initialdir=self.playlist_save_path,
            title="اختر مجلد لحفظ الترجمات"
        )
        if not save_path:
            return

        for item in selected_items:
            index = int(self.playlist_tree.item(item, 'values')[0]) - 1
            video = self.playlist_videos[index]
            url = video['url']
            title = video['title']

            # إعداد خيارات yt-dlp لاستخراج الترجمات
            ydl_opts = {
                'writesubtitles': True,
                'writeautomaticsub': True,  # استخراج الترجمات التلقائية (إن وجدت)
                'subtitleslangs': ['en', 'ar'],  # اللغات المطلوبة
                'subtitlesformat': 'srt',  # صيغة الترجمة
                'skip_download': True,  # عدم تنزيل الفيديو نفسه
                'outtmpl': os.path.join(save_path, f"{title}.%(ext)s"),
                'http_headers': {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
                }
            }

            try:
                with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                    ydl.download([url])
                messagebox.showinfo("نجاح", f"تم تصدير ترجمات الفيديو: {title}")
            except Exception as e:
                messagebox.showerror("خطأ", f"فشل تصدير ترجمات الفيديو {title}: {e}")

    def select_batch_directory(self):
        """Select the download directory for batch downloads."""
        import tkinter as tk
        from tkinter import filedialog

        folder = filedialog.askdirectory(title=self.translations[self.language].get("select_folder", "Select Download Folder"))
        if folder:
            self.batch_path_var.set(folder)
            self.batch_save_path = folder
            # Update UI if batch_path_label exists
            if hasattr(self, 'batch_path_label') and self.batch_path_label.winfo_exists():
                self.batch_path_label.config(text=f"{self.translations[self.language].get('download_path', 'Download Path')}: {folder}")
            else:
                # Create new Label if not exists
                if hasattr(self, 'batch_path_frame'):
                    for widget in self.batch_path_frame.winfo_children():
                        if isinstance(widget, ttk.Label) and widget.cget("text").startswith(self.translations[self.language].get("download_path", "Download Path")):
                            widget.config(text=f"{self.translations[self.language].get('download_path', 'Download Path')}: {folder}")
                            break
                    else:
                        path_label = ttk.Label(
                            self.batch_path_frame,
                            text=f"{self.translations[self.language].get('download_path', 'Download Path')}: {folder}",
                            foreground="#111827"
                        )
                        path_label.pack(anchor="w", padx=5, pady=2)
                        self.batch_path_label = path_label

    def select_directory(self, tab=None):
        """Select a save directory for downloads and update appropriate save path."""
        import tkinter as tk
        from tkinter import filedialog
        import os
        import logging

        logging.basicConfig(level=logging.DEBUG)

        try:
            # Set initial directory
            initial_dir = self.save_path if os.path.isdir(self.save_path) else os.path.expanduser("~")
            directory = filedialog.askdirectory(
                initialdir=initial_dir,
                title=self.translations[self.language].get("select_directory", "Select Directory")
            )
            if not directory or not os.path.isdir(directory):
                logging.debug("No valid directory selected")
                return

            # Identify batch and playlist tabs using notebook
            batch_tab = None
            playlist_tab = None
            if hasattr(self, 'notebook'):
                for tab_widget in self.notebook.tabs():
                    tab_frame = self.notebook.nametowidget(tab_widget)
                    children = tab_frame.winfo_children()
                    if hasattr(self, 'batch_tree') and self.batch_tree in children:
                        batch_tab = tab_frame
                    if hasattr(self, 'playlist_path_entry') and self.playlist_path_entry in children:
                        playlist_tab = tab_frame

            # Update based on tab
            if tab == batch_tab:
                if hasattr(self, 'batch_path_entry') and self.batch_path_entry.winfo_exists():
                    self.batch_path_entry.delete(0, tk.END)
                    self.batch_path_entry.insert(0, directory)
                self.batch_save_path = directory
                logging.debug(f"Updated batch_save_path to {directory}")
            elif tab == playlist_tab:
                if hasattr(self, 'playlist_path_entry') and self.playlist_path_entry.winfo_exists():
                    self.playlist_path_entry.delete(0, tk.END)
                    self.playlist_path_entry.insert(0, directory)
                self.playlist_save_path = directory
                logging.debug(f"Updated playlist_save_path to {directory}")
            else:
                self.save_path = directory
                if hasattr(self, 'path_label') and self.path_label.winfo_exists():
                    self.path_label.config(text=directory)
                logging.debug(f"Updated save_path to {directory}")

            # Save settings
            if hasattr(self, 'save_settings'):
                self.save_settings()
                logging.debug("Saved settings after directory selection")

            # Update status bar
            if hasattr(self, 'status_bar') and self.status_bar.winfo_exists():
                self.status_bar.config(
                    text=self.translations[self.language].get("directory_selected", "Directory selected: {}").format(directory)
                )

        except Exception as e:
            logging.error(f"Error in select_directory: {str(e)}")
            if hasattr(self, 'status_bar') and self.status_bar.winfo_exists():
                self.status_bar.config(
                    text=self.translations[self.language].get("error_selecting_directory", "Error selecting directory")
                )
    def load_history(self):
        import os
        import logging
        self.history_file = os.path.join(self.save_path, "download_history.txt")
        try:
            if not os.path.exists(self.history_file):
                logging.info(f"History file {self.history_file} does not exist, creating new one")
                with open(self.history_file, 'w', encoding='utf-8') as f:
                    f.write("")
                return

            with open(self.history_file, 'r', encoding='utf-8') as f:
                for line in f:
                    try:
                        time_str, url, dl_type, status, details = line.strip().split('|', 4)
                        self.history_tree.insert("", "end", values=(time_str, url, dl_type, status, details))
                    except Exception as e:
                        logging.error(f"Error parsing history line: {line.strip()} - {e}")
        except Exception as e:
            logging.error(f"Failed to load history from {self.history_file}: {e}")

    # Reused log_history function
    def log_history(self, url, dl_type, status, details):
        import os
        import logging
        from datetime import datetime
        try:
            os.makedirs(self.save_path, exist_ok=True)
            with open(self.history_file, 'a', encoding='utf-8') as f:
                timestamp = datetime.now().strftime("%Y-%m-d %H:%M:%S")
                f.write(f"{timestamp}|{url}|{dl_type}|{status}|{details}\n")
            self.history_tree.insert("", "end", values=(timestamp, url, dl_type, status, details))
        except Exception as e:
            logging.error(f"Failed to log history: {e}")

    def notify_download(self, url, success):
        title = self.translations[self.language]["download_complete"] if success else self.translations[self.language]["download_failed"].format(url)
        message = self.translations[self.language]["download_success"] if success else "فشل التنزيل"
        try:
            notification.notify(
                title=title,
                message=message,
                timeout=10
            )
        except Exception as e:
            print(f"فشل إرسال الإشعار: {e}")

    def open_file(self, filepath):
        """Open a file using the default application associated with its type."""
        import platform
        import subprocess
        try:
            if not os.path.exists(filepath):
                messagebox.showerror("خطأ", f"الملف غير موجود: {filepath}")
                return
            if platform.system() == "Windows":
                os.startfile(filepath)
            elif platform.system() == "Darwin":  # macOS
                subprocess.run(["open", filepath])
            else:  # Linux and others
                subprocess.run(["xdg-open", filepath])
            self.log_history(filepath, "OpenFile", "Success", "File opened successfully")
        except Exception as e:
            self.log_history(filepath, "OpenFile", "Failed", str(e))
            messagebox.showerror("خطأ", f"فشل فتح الملف: {e}")

    def open_folder(self, folder_path):
        """Open the folder in the operating system's file explorer."""
        import platform
        import subprocess
        try:
            if not os.path.isdir(folder_path):
                messagebox.showerror("خطأ", f"المجلد غير موجود: {folder_path}")
                return
            if platform.system() == "Windows":
                os.startfile(folder_path)
            elif platform.system() == "Darwin":  # macOS
                subprocess.run(["open", folder_path])
            else:  # Linux and others
                subprocess.run(["xdg-open", folder_path])
            self.log_history(folder_path, "OpenFolder", "Success", "Folder opened successfully")
        except Exception as e:
            self.log_history(folder_path, "OpenFolder", "Failed", str(e))
            messagebox.showerror("خطأ", f"فشل فتح المجلد: {e}")

    def show_custom_notification(self, title, duration, file_size, status):
        # تحويل المدة إلى صيغة دقائق:ثواني
        minutes = int(duration // 60)
        seconds = int(duration % 60)
        duration_str = f"{minutes} دقيقة و {seconds} ثانية"

        # إعداد نافذة الإشعار
        notification_window = tk.Toplevel(self.root)
        notification_window.title("إشعار انتهاء التنزيل")
        notification_window.geometry("400x200")
        notification_window.configure(bg=self.secondary_color)

        # إضافة تفاصيل الإشعار
        ttk.Label(
            notification_window,
            text=f"الفيديو: {title[:30]}...",
            foreground="#1E3A8A"
        ).pack(anchor="w", padx=10, pady=5)
        ttk.Label(
            notification_window,
            text=f"الحالة: {status}",
            foreground="#111827"
        ).pack(anchor="w", padx=10, pady=5)
        ttk.Label(
            notification_window,
            text=f"مدة التنزيل: {duration_str}",
            foreground="#111827"
        ).pack(anchor="w", padx=10, pady=5)
        ttk.Label(
            notification_window,
            text=f"حجم الملف: {file_size:.2f} ميجا",
            foreground="#111827"
        ).pack(anchor="w", padx=10, pady=5)

        # زر لإغلاق النافذة
        ttk.Button(
            notification_window,
            text="إغلاق",
            command=notification_window.destroy,
            style="Accent.TButton"
        ).pack(pady=10)

        # إغلاق النافذة تلقائيًا بعد 10 ثواني
        notification_window.after(10000, notification_window.destroy)


    def update_stats(self, downloaded_bytes, download_count):
        """تحديث الإحصائيات"""
        if not hasattr(self, 'stats'):
            self.stats = {'files': 0, 'size': 0.0, 'downloads': 0}
        self.stats['files'] += 1
        self.stats['size'] += downloaded_bytes / (1024 * 1024)  # Convert to MB
        self.stats['downloads'] += download_count
        with open(self.stats_file, 'w', encoding='utf-8') as f:
            json.dump(self.stats, f, ensure_ascii=False, indent=4)
        self.stats_label.config(text=self.get_stats_text())

    def upload_to_cloud(self, filepath):
        if not os.path.exists(filepath):
            print(f"الملف {filepath} غير موجود")
            return
        try:
            dbx = dropbox.Dropbox(self.cloud_token)
            filename = os.path.basename(filepath)
            with open(filepath, 'rb') as f:
                dbx.files_upload(f.read(), f"/{filename}", mute=True)
            self.log_history(filepath, "Cloud", "Success", "Uploaded to Dropbox")
            print(f"تم رفع {filename} إلى Dropbox")
        except Exception as e:
            self.log_history(filepath, "Cloud", "Failed", str(e))
            print(f"فشل رفع {filepath} إلى Dropbox: {e}")

    def update_batch_progress(self):
        """تحديث شريط التقدم للتنزيل الجماعي"""
        if not hasattr(self, 'batch_download_items') or not self.batch_download_items:
            return
            
        total = len(self.batch_download_items)
        completed = 0
        total_size = 0
        downloaded_size = 0
        
        for item in self.batch_download_items:
            total_size += item.get('filesize_mb', 0)
            url = item['url']
            
            if url in self.download_threads:
                if self.download_threads[url]['completed']:
                    completed += 1
                    downloaded_size += item.get('filesize_mb', 0)
                else:
                    downloaded_size += self.download_threads[url].get('downloaded_bytes', 0) / (1024 * 1024)
        
        # حساب النسبة المئوية
        if total_size > 0:
            percent = (downloaded_size / total_size) * 100
        else:
            percent = (completed / total) * 100 if total > 0 else 0
            
        # تحديث واجهة المستخدم
        self.overall_progress_label.config(
            text=f"التقدم الجماعي: {completed}/{total} - {percent:.1f}%"
        )
        
        # الاستمرار في التحديث إذا لم يكتمل التنزيل
        if completed < total:
            self.root.after(1000, self.update_batch_progress)

 

    def on_closing(self):
        """Handle application closing."""
        self.running = False  # Stop the queue manager thread
        try:
            self.save_settings()
        except Exception as e:
            logging.error(f"Failed to save settings on closing: {e}")
        self.root.destroy()
    def save_settings(self):
        """Save current settings to settings.json."""
        settings = {
            "language": self.language,
            "save_path": self.save_path,
            "max_workers": self.max_workers,
            "max_speed": self.max_speed,
            "ffmpeg_path": self.ffmpeg_path,
            "cloud_enabled": self.cloud_enabled,
            "cloud_token": self.cloud_token
        }
        settings_file = os.path.join(self.save_path, "settings.json")
        try:
            with open(settings_file, 'w', encoding='utf-8') as f:
                json.dump(settings, f, ensure_ascii=False, indent=4)
            logging.debug(f"Settings saved to {settings_file}")
        except Exception as e:
            logging.error(f"Failed to save settings: {e}")

    def update_history_list(self):
        for item in self.history_tree.get_children():
            self.history_tree.delete(item)
        try:
            with open(self.history_file, 'r', encoding='utf-8') as f:
                for line in f:
                    entry = json.loads(line.strip())
                    self.history_tree.insert("", "end", values=(
                        entry["time"],
                        entry["url"][:50] + "..." if len(entry["url"]) > 50 else entry["url"],
                        entry["type"],
                        entry["status"],
                        entry["details"]
                    ))
        except Exception as e:
            print(f"خطأ في تحديث قائمة السجل: {e}")

    def clear_history(self):
        if messagebox.askyesno("تأكيد", "هل تريد مسح السجل؟"):
            try:
                with open(self.history_file, 'w', encoding='utf-8') as f:
                    f.write('')
                self.update_history_list()
                self.status_bar.config(text=self.translations[self.language]["cleared"])
            except Exception as e:
                print(f"خطأ في مسح السجل: {e}")

    def search_history(self, event=None):
        query = self.search_entry.get().lower()
        for item in self.history_tree.get_children():
            self.history_tree.delete(item)
        try:
            with open(self.history_file, 'r', encoding='utf-8') as f:
                for line in f:
                    entry = json.loads(line.strip())
                    if query in entry["url"].lower() or query in entry["details"].lower():
                        self.history_tree.insert("", "end", values=(
                            entry["time"],
                            entry["url"][:50] + "..." if len(entry["url"]) > 50 else entry["url"],
                            entry["type"],
                            entry["status"],
                            entry["details"]
                        ))
        except Exception as e:
            print(f"خطأ في البحث في السجل: {e}")

    def on_history_double_click(self, event):
        item = self.history_tree.selection()
        if item:
            values = self.history_tree.item(item, 'values')
            url = values[1]
            if "..." in url:
                try:
                    with open(self.history_file, 'r', encoding='utf-8') as f:
                        for line in f:
                            entry = json.loads(line.strip())
                            if entry["time"] == values[0] and entry["details"] == values[4]:
                                url = entry["url"]
                                break
                except Exception as e:
                    print(f"خطأ في استرجاع الرابط الكامل: {e}")
            pyperclip.copy(url)
            self.status_bar.config(text=self.translations[self.language]["copy_link"])
    def resume_incomplete(self):
        """استئناف تحميل غير مكتمل من تبويب Incomplete Downloads"""
        import tkinter.messagebox as messagebox
        import logging

        logging.basicConfig(level=logging.DEBUG)

        try:
            selected = self.incomplete_downloads.winfo_children()
            if not selected or not any(isinstance(w, ttk.Frame) for w in selected):
                messagebox.showerror(
                    self.translations[self.language]["error"],
                    self.translations[self.language]["no_incomplete"]
                )
                return

            # Find the selected download (assuming first frame for simplicity)
            for frame in selected:
                if isinstance(frame, ttk.Frame):
                    for widget in frame.winfo_children():
                        if isinstance(widget, ttk.Button) and widget.cget("text") == self.translations[self.language]["resume_download"]:
                            task_id = widget.cget("command").__code__.co_consts[0]
                            self.resume_download(task_id)
                            break
                    break
            logging.debug(f"Resumed incomplete download for task_id {task_id}")
        except Exception as e:
            logging.error(f"Error resuming incomplete download: {str(e)}")
            messagebox.showerror(
                self.translations[self.language]["error"],
                self.translations[self.language]["download_error"].format("Incomplete Download", str(e))
            )
    def clear_incomplete(self):
        if messagebox.askyesno("تأكيد", "هل تريد مسح التنزيلات الناقصة؟"):
            self.incomplete_downloads = []
            try:
                with open(self.incomplete_file, 'w', encoding='utf-8') as f:
                    json.dump([], f, ensure_ascii=False, indent=4)
                self.update_incomplete_list()
                self.status_bar.config(text=self.translations[self.language]["cleared"])
            except Exception as e:
                print(f"خطأ في مسح التنزيلات الناقصة: {e}")

    def update_incomplete_list(self):
        """تحديث قائمة التحميلات غير المكتملة (احتياطية)"""
        import logging

        logging.basicConfig(level=logging.DEBUG)

        try:
            # Clear current Treeview
            for item in self.incomplete_tree.get_children():
                self.incomplete_tree.delete(item)

            # Populate from self.download_threads
            for task_id, info in self.download_threads.items():
                if not info.get('completed', False):
                    time_str = info.get('start_time', time.time())
                    time_str = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(time_str))
                    url = info.get('url', 'Unknown')
                    filename = info.get('filename', 'Unknown')
                    status = info.get('status', 'downloading')
                    self.incomplete_tree.insert("", "end", values=(
                        time_str,
                        url,
                        filename,
                        status.capitalize()
                    ))
                    logging.debug(f"Added {filename} to incomplete list with status {status}")
        except Exception as e:
            logging.error(f"Error updating incomplete list: {str(e)}")
    def get_stats_text(self):
        """Generate formatted stats text for display."""
        return self.translations[self.language]["stats_text"].format(
            self.stats['total_files'],
            self.stats['total_size_mb'],
            self.stats['avg_speed_mbps'],
            self.stats['total_downloads']
        )

    def update_stats(self, size_bytes, count):
        """Update download statistics."""
        self.stats['total_files'] += count
        self.stats['total_size_mb'] += size_bytes / (1024 * 1024)
        self.stats['total_downloads'] += 1
        # Update avg_speed_mbps if applicable (placeholder for speed calculation)
        self.stats['avg_speed_mbps'] = self.stats.get('avg_speed_mbps', 0.0)  # Modify based on actual speed calculation
        try:
            with open(self.stats_file, 'w', encoding='utf-8') as f:
                json.dump(self.stats, f, ensure_ascii=False, indent=4)
        except IOError as e:
            logging.error(f"Error saving stats to {self.stats_file}: {e}")


    def toggle_dark_mode(self):
        self.dark_mode = not self.dark_mode
        self.primary_color = "#111827" if self.dark_mode else "#1E3A8A"
        self.secondary_color = "#1F2937" if self.dark_mode else "#F3F4F6"
        self.accent_color = "#F59E0B"
        self.setup_styles()
        self.root.configure(bg=self.primary_color)
        self.header_frame.configure(style="Header.TFrame")
        self.welcome_label.configure(background=self.primary_color, foreground=self.accent_color)
        self.hello_label.configure(background=self.primary_color, foreground=self.accent_color)
        self.update_ui_language()

    def check_ffmpeg(self):
        if os.path.exists(self.ffmpeg_path):
            self.ffmpeg_available = True
            self.status_bar.config(text=self.translations[self.language]["ffmpeg_ready"].format(self.ffmpeg_path))
        else:
            self.ffmpeg_available = False
            self.status_bar.config(text=self.translations[self.language]["ffmpeg_not_found"])

    def setup_directories(self):
        for path in [os.path.join(self.save_path, d) for d in ["videos", "audios", "others"]]:
            os.makedirs(path, exist_ok=True)

    def add_to_queue(self, url, is_batch, quality, filename, format_id, ext, is_combined, download_type):
        """
        Adds an item to the download queue after validating it has 8 values.
        """
        item = (url, is_batch, quality, filename, format_id, ext, is_combined, download_type)
        if len(item) != 8:
            logging.error(f"Attempted to add invalid item to queue: {item}, length={len(item)}")
            self.root.after(0, lambda: messagebox.showerror(
                self.translations[self.language]["error"],
                f"خطأ في إضافة عنصر: يجب أن يحتوي على 8 قيم، لكن يحتوي على {len(item)}"
            ))
            return
        logging.debug(f"Adding to queue: {item}")
        self.download_queue.put(item)

    def start_queue_manager(self):
        """Manage the download queue."""
        processed_urls = set()  # Track processed URLs
        try:
            while self.download_queue:
                task = self.download_queue.pop(0)
                if len(task) != 8:
                    logging.error(f"Invalid task format: {task}")
                    continue
                url, is_batch, quality, filename, format_id, ext, is_combined, download_type = task
                if url in processed_urls:
                    logging.debug(f"Skipping already processed URL: {url}")
                    continue
                processed_urls.add(url)
                logging.debug(f"Processing task: {task}, Queue size: {len(self.download_queue)}")
                self.download(
                    url,
                    is_batch=is_batch,
                    quality=quality,
                    filename=filename,
                    custom_save_path=self.download_path,
                    format_id=format_id,
                    ext=ext,
                    is_combined=is_combined,
                    is_general_download=(download_type == "general")
                )
                # Wait for the download to complete before processing the next task
                while url in self.download_threads and not self.download_threads[url]['completed']:
                    time.sleep(0.1)
        except Exception as e:
            logging.error(f"Queue manager error: {str(e)}")
    def manage_queue(self):
        """Manage the download queue in a separate thread."""
        while self.running:
            try:
                if self.download_queue and self.active_downloads < self.max_workers:
                    task = self.download_queue.pop(0)
                    if not isinstance(task, dict) or 'url' not in task:
                        logging.error(f"Invalid task format: {task}")
                        continue
                    self.active_downloads += 1
                    threading.Thread(
                        target=self.process_task,
                        args=(task,),
                        daemon=True
                    ).start()
                time.sleep(0.1)  # Prevent busy-waiting
            except Exception as e:
                logging.error(f"خطأ غير متوقع في إدارة القائمة: {e}")
        logging.debug("Queue manager thread terminated")

    def process_task(self, task):
        """Process a single download task."""
        try:
            url = task['url']
            save_path = task.get('save_path', self.save_path)
            quality = task.get('quality', 'best')
            mp3 = task.get('mp3', self.mp3_var.get())
            subtitles = task.get('subtitles', self.subtitles_var.get())

            logging.debug(f"Processing download for URL: {url}, Save Path: {save_path}, Quality: {quality}")

            # Configure yt-dlp options
            ydl_opts = {
                'outtmpl': os.path.join(save_path, '%(title)s.%(ext)s'),
                'format': quality,
                'noplaylist': True,
                'ffmpeg_location': self.ffmpeg_path if self.ffmpeg_available else None,
                'writesubtitles': subtitles,
                'subtitleslangs': ['all'] if subtitles else [],
                'postprocessors': [{
                    'key': 'FFmpegExtractAudio',
                    'preferredcodec': 'mp3',
                    'preferredquality': '192',
                }] if mp3 else [],
            }

            # Download using yt-dlp
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                ydl.download([url])

            logging.debug(f"Download completed for URL: {url}")
            self.root.after(0, lambda: messagebox.showinfo("نجاح", f"تم التنزيل بنجاح: {url}"))

        except Exception as e:
            error_message = f"خطأ غير متوقع في معالجة التنزيل: {e}"
            logging.error(error_message)
            self.root.after(0, lambda: messagebox.showerror("خطأ", error_message))
        finally:
            self.active_downloads -= 1


    def log_history(self, url, download_type, status, details):
        """تسجيل التنزيل في السجل"""
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        log_entry = f"{timestamp} | {url} | {download_type} | {status} | {details}\n"
        with open(self.history_file, 'a', encoding='utf-8') as f:
            f.write(log_entry)
        self.load_history()  # Refresh the history tab
    def setup_clipboard_monitor(self):
        def monitor():
            last_clipboard = ""
            while True:
                try:
                    clipboard = pyperclip.paste()
                    if clipboard != last_clipboard and self.is_valid_url(clipboard):
                        self.url_entry.delete(0, tk.END)
                        self.url_entry.insert(0, clipboard)
                        last_clipboard = clipboard
                    time.sleep(1)
                except Exception:
                    time.sleep(1)
        threading.Thread(target=monitor, daemon=True).start()

    def is_valid_url(self, url):
        """Check if the URL is valid."""
        regex = re.compile(
            r'^(?:http|ftp)s?://'
            r'(?:(?:[A-Z0-9](?:[A-Z0-9-]{0,61}[A-Z0-9])?\.)+(?:[A-Z]{2,6}\.?|[A-Z0-9-]{2,}\.?)|'
            r'localhost|'
            r'\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})'
            r'(?::\d+)?'
            r'(?:/?|[/?]\S+)$', re.IGNORECASE)
        return re.match(regex, url) is not None

    def clean_youtube_url(self, url):
        """Clean and normalize YouTube URLs to ensure consistency."""
        try:
            parsed_url = urlparse(url)
            if parsed_url.netloc in ('www.youtube.com', 'youtu.be', 'youtube.com'):
                if parsed_url.netloc == 'youtu.be':
                    video_id = parsed_url.path.lstrip('/')
                    cleaned_url = f"https://www.youtube.com/watch?v={video_id}"
                else:
                    query = parse_qs(parsed_url.query)
                    video_id = query.get('v', [None])[0]
                    if video_id:
                        cleaned_url = f"https://www.youtube.com/watch?v={video_id}"
                    else:
                        cleaned_url = url
                return cleaned_url
            return url
        except Exception as e:
            logging.error(f"Error cleaning URL {url}: {e}")
            return url

    def is_video_url(self, url):
        """Check if the provided URL points to a video or audio content."""
        import logging
        import requests
        from urllib.parse import urlparse, parse_qs

        video_domains = [
            "youtube.com", "youtu.be", "vimeo.com", "dailymotion.com",
            "facebook.com", "instagram.com", "tiktok.com", "twitter.com",
            "x.com", "soundcloud.com", "twitch.tv", "bilibili.com",
            "ok.ru", "reddit.com", "tumblr.com", "pinterest.com",
            "metacafe.com", "vevo.com", "liveleak.com", "myspace.com",
            "niconico.jp", "rutube.ru", "youku.com", "bitchute.com",
            "odysee.com", "rumble.com", "brighteon.com"
        ]
        hls_extensions = [".m3u", ".m3u8", ".pls"]
        video_extensions = [".mp4", ".webm", ".flv", ".avi", ".mkv"]

        try:
            parsed_url = urlparse(url)
            domain = parsed_url.netloc.lower()
            path = parsed_url.path.lower()

            # Check if domain matches known video platforms
            is_domain_match = any(v_domain in domain for v_domain in video_domains)
            logging.debug(f"Checking URL {url}: domain_match={is_domain_match}")

            # Special handling for YouTube URLs
            if "youtube.com" in domain or "youtu.be" in domain:
                query = parse_qs(parsed_url.query)
                if 'list' in query:
                    logging.debug(f"URL {url} is a YouTube playlist, returning False")
                    return False
                if "youtu.be" in domain and path.strip('/'):
                    logging.debug(f"URL {url} is a valid YouTube short link")
                    return True
                if "watch" in path and 'v' in query:
                    logging.debug(f"URL {url} is a valid YouTube watch link")
                    return True

            # Check for HLS or direct video file extensions
            is_hls = any(path.endswith(ext) for ext in hls_extensions)
            is_direct_video = any(path.endswith(ext) for ext in video_extensions)
            logging.debug(f"URL {url}: is_hls={is_hls}, is_direct_video={is_direct_video}")

            # Check content-type for direct video links
            if not is_domain_match:
                try:
                    response = requests.head(url, timeout=5, allow_redirects=True)
                    content_type = response.headers.get('content-type', '').lower()
                    if content_type.startswith(('video/', 'audio/')):
                        logging.debug(f"URL {url} is a direct video/audio (content-type: {content_type})")
                        return False  # Treat as direct file, not platform video
                except requests.RequestException as e:
                    logging.warning(f"Failed to check content-type for {url}: {e}")

            # Check with yt_dlp for non-listed video platforms
            if not is_domain_match and not is_hls and not is_direct_video:
                try:
                    with yt_dlp.YoutubeDL({
                        'quiet': True,
                        'noplaylist': True,
                        'extractor_args': {
                            'okru': {'skip_auth': True}
                        }
                    }) as ydl:
                        info = ydl.extract_info(url, download=False)
                        if info.get('formats') or info.get('url'):
                            logging.debug(f"URL {url} is a valid video (confirmed by yt_dlp)")
                            return True
                except yt_dlp.utils.DownloadError as e:
                    logging.warning(f"yt_dlp failed to extract info for {url}: {e}")
                    return False

            result = is_domain_match or is_hls or is_direct_video
            logging.debug(f"URL {url} is_video_url result: {result}")
            return result

        except (ValueError, urllib.error.URLError) as e:
            logging.error(f"Error parsing URL {url}: {e}")
            return False
    def extract_video_links(self):
        url = self.url_entry.get().strip()
        if not url:
            messagebox.showerror("خطأ", self.translations[self.language]["no_url"])
            return

        def extract_thread():
            try:
                response = requests.get(url, headers={
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
                })
                response.raise_for_status()
                soup = BeautifulSoup(response.text, 'html.parser')
                links = []
                for a in soup.find_all('a', href=True):
                    href = a['href']
                    if self.is_valid_url(href) and self.is_video_url(href):
                        links.append(href)
                if links:
                    self.root.after(0, lambda: messagebox.showinfo(
                        "نجاح",
                        self.translations[self.language]["extracted_links"].format(len(links))
                    ))
                    for link in links:
                        self.batch_url_entry.delete(0, tk.END)
                        self.batch_url_entry.insert(0, link)
                        self.add_batch_url()
                else:
                    self.root.after(0, lambda: messagebox.showinfo("معلومات", "لم يتم العثور على روابط فيديو"))
            except Exception as e:
                self.root.after(0, lambda: messagebox.showerror("خطأ", f"فشل استخراج الروابط: {e}"))
        threading.Thread(target=extract_thread, daemon=True).start()

    def add_batch_url_with_quality(self):
        """Add URLs to the batch download list with a popup window for quality selection."""
        import logging
        import threading
        import time
        import yt_dlp
        import tkinter
        from tkinter import messagebox, ttk
        from urllib.parse import urlparse

        logging.basicConfig(level=logging.DEBUG)

        # Get and validate URLs
        raw_urls = self.batch_urls_text.get("1.0", tkinter.END).strip().splitlines()
        urls = []
        for url in raw_urls:
            url = url.strip()
            if not url or url in self.batch_urls:
                continue
            # Basic URL validation
            try:
                parsed = urlparse(url)
                if not all([parsed.scheme, parsed.netloc]) or parsed.scheme not in ['http', 'https']:
                    logging.warning(f"Invalid URL skipped: {url}")
                    continue
                urls.append(url)
            except Exception as e:
                logging.warning(f"Invalid URL {url}: {e}")
                continue

        if not urls:
            messagebox.showwarning(
                self.translations[self.language]["warning"],
                self.translations[self.language]["no_batch_urls"]
            )
            logging.warning("No valid URLs provided for batch download")
            return

        self.batch_urls.extend(urls)
        self.root.after(0, lambda: self.status_bar.configure(
            text=self.translations[self.language]["batch_added"].format(len(urls))
        ))

        def fetch_qualities_thread():
            ydl_opts = {
                'format': 'bestvideo+bestaudio/best',
                'noplaylist': True,
                'quiet': True,
                'no_warnings': True,
                'no_m3u8': True,
                'http_headers': {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
                },
                'socket_timeout': 30,
                'retries': 3,
                'fragment_retries': 3,
                'retry_sleep': 5
            }

            retries = 3
            for cleaned_url in urls:
                logging.debug(f"Fetching qualities for URL: {cleaned_url}")
                self.batch_formats_cache[cleaned_url] = {}
                self.batch_available_qualities[cleaned_url] = []
                for attempt in range(retries):
                    try:
                        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                            info = ydl.extract_info(cleaned_url, download=False)
                            formats = info.get('formats', [])
                            quality_list = []
                            seen_qualities = set()  # To track unique qualities
                            for f in formats:
                                resolution = f.get('height', None)
                                ext = f.get('ext', '')
                                vcodec = f.get('vcodec', 'none')
                                format_note = f.get('format_note', '').lower()
                                # Filter: Accept mp4/mkv video formats with resolution, exclude storyboards and audio-only
                                if (not resolution or ext not in ['mp4', 'mkv'] or vcodec == 'none' or
                                    'storyboard' in format_note or 'audio only' in format_note):
                                    continue
                                # Use mkv for resolutions > 1080p, mp4 otherwise
                                if resolution > 1080 and ext != 'mkv':
                                    continue
                                if resolution <= 1080 and ext != 'mp4':
                                    continue
                                format_id = f.get('format_id')
                                fps = f.get('fps', '')
                                filesize = f.get('filesize', 0) or f.get('filesize_approx', 0)
                                # Skip formats with no valid filesize
                                if not filesize or filesize <= 0:
                                    logging.debug(f"Skipped format for {cleaned_url}: {resolution}p {ext} - No valid filesize")
                                    continue
                                # Skip unrealistic filesizes (e.g., >10GB for a typical video)
                                if filesize > 10 * 1024 * 1024 * 1024:  # 10GB
                                    logging.debug(f"Skipped format for {cleaned_url}: {resolution}p {ext} - Unrealistic filesize {filesize}")
                                    continue
                                filesize_mb = filesize / (1024 * 1024)
                                # Create unique key without filesize
                                quality_key = f"{resolution}p {ext}"
                                if format_note and format_note != str(resolution) + 'p':
                                    quality_key += f" ({format_note})"
                                if fps:
                                    quality_key += f" {fps}fps"
                                if quality_key in seen_qualities:
                                    logging.debug(f"Skipped duplicate format for {cleaned_url}: {quality_key}")
                                    continue
                                seen_qualities.add(quality_key)
                                quality_display = f"{quality_key} - {filesize_mb:.2f} ميجا"
                                has_audio = f.get('acodec', 'none') != 'none'
                                is_combined = vcodec != 'none' and has_audio
                                quality_list.append(quality_display)
                                self.batch_formats_cache[cleaned_url][quality_key] = (
                                    format_id,
                                    ext,
                                    filesize,
                                    format_note,
                                    is_combined
                                )
                                logging.debug(f"Format added for {cleaned_url}: {quality_key}, format_id={format_id}, filesize={filesize}")

                            if not quality_list:
                                raise Exception("No valid formats found")

                            quality_list.sort(key=lambda x: int(x.split('p')[0]) if 'p' in x and x.split('p')[0].isdigit() else 0)
                            self.batch_available_qualities[cleaned_url] = quality_list

                            title = info.get('title', 'غير معروف')
                            duration = info.get('duration', 'غير معروف')
                            if isinstance(duration, (int, float)):
                                duration = f"{int(duration // 60)}:{int(duration % 60):02d}"

                            # Show popup window for quality selection
                            def show_quality_popup():
                                popup = tkinter.Toplevel(self.root)
                                popup.title(self.translations[self.language].get("select_quality", "Select Quality"))
                                popup.geometry("400x200")
                                popup.transient(self.root)
                                popup.grab_set()

                                ttk.Label(popup, text=self.translations[self.language].get("select_quality", "Select Quality for:") + f" {title}").pack(pady=10)
                                quality_var = tkinter.StringVar(value=quality_list[-1] if quality_list else '')  # Default to highest quality
                                quality_combo = ttk.Combobox(popup, textvariable=quality_var, values=quality_list, state="readonly", width=50)
                                quality_combo.pack(pady=10)

                                def confirm_selection():
                                    selected_quality = quality_var.get()
                                    if not selected_quality:
                                        logging.warning(f"No quality selected for {cleaned_url}")
                                        popup.destroy()
                                        return
                                    # Clean selected_quality to remove filesize part
                                    clean_quality = selected_quality.split(' - ')[0].strip()
                                    self.batch_quality_selections[cleaned_url] = clean_quality
                                    filesize = self.batch_formats_cache[cleaned_url][clean_quality][2]
                                    filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"
                                    format_id, ext, filesize, format_note, is_combined = self.batch_formats_cache[cleaned_url][clean_quality]
                                    
                                    item_id = self.batch_tree.insert("", "end", values=(
                                        cleaned_url[:50] + "..." if len(cleaned_url) > 50 else cleaned_url,
                                        title,
                                        duration,
                                        clean_quality,
                                        f"{filesize_mb:.2f} ميجا" if isinstance(filesize_mb, float) else filesize_mb
                                    ))

                                    self.batch_download_items.append({
                                        'url': cleaned_url,
                                        'title': title,
                                        'duration': duration,
                                        'quality': clean_quality,
                                        'format_id': format_id,
                                        'ext': ext,
                                        'is_combined': is_combined,
                                        'filesize_mb': filesize_mb,
                                        'tree_item_id': item_id
                                    })
                                    logging.debug(f"Added {cleaned_url} to Treeview with quality {clean_quality}, format_id={format_id}")
                                    popup.destroy()

                                confirm_button = ttk.Button(
                                    popup,
                                    text=self.translations[self.language].get("confirm", "Confirm"),
                                    command=confirm_selection,
                                    style="Accent.TButton"
                                )
                                confirm_button.pack(pady=10)

                            self.root.after(0, show_quality_popup)
                        break

                    except Exception as e:
                        logging.error(f"Error for {cleaned_url} (attempt {attempt + 1}/{retries}): {type(e).__name__}: {e}")
                        if attempt == retries - 1:
                            self.failed_quality_urls.append(cleaned_url)
                            self.root.after(0, lambda err=str(e): messagebox.showwarning(
                                self.translations[self.language]["warning"],
                                f"فشل جلب الجودات لـ {cleaned_url}: {err}"
                            ))
                            item_id = self.batch_tree.insert("", "end", values=(
                                cleaned_url[:50] + "..." if len(cleaned_url) > 50 else cleaned_url,
                                "غير معروف",
                                "غير معروف",
                                "غير محدد",
                                "غير معروف"
                            ))
                            logging.debug(f"Added {cleaned_url} to tree with 'غير محدد' and to failed_quality_urls")
                        time.sleep(5)
                        continue

            self.root.after(0, lambda: [
                self.status_bar.configure(
                    text=self.translations[self.language].get("found_formats", "تم العثور على {} جودة/جودات").format(len(self.batch_download_items))
                ),
                self.batch_progress_bar.stop(),
                self.batch_progress_bar.grid_remove()
            ])
            logging.debug(f"تم جلب {len(self.batch_download_items)} عنصر/عناصر للتنزيل")

        # Show and start progress bar
        self.batch_progress_bar.grid(row=3, column=0, sticky="ew", padx=5, pady=5)
        self.batch_progress_bar.start(10)
        threading.Thread(target=fetch_qualities_thread, daemon=True).start()
    def retry_fetch_qualities(self):
        """Retry fetching qualities for URLs that failed initially."""
        import logging
        import tkinter
        from tkinter import messagebox, ttk
        import yt_dlp
        import time
        import threading

        logging.basicConfig(level=logging.DEBUG)

        if not self.failed_quality_urls:
            messagebox.showinfo(
                self.translations[self.language]["info"],
                self.translations[self.language]["no_failed_urls"]
            )
            logging.info("No failed URLs to retry")
            return

        def retry_thread():
            ydl_opts = {
                'format': 'bestvideo+bestaudio/best',
                'noplaylist': True,
                'quiet': True,
                'no_warnings': True,
                'no_m3u8': True,
                'http_headers': {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
                },
                'socket_timeout': 30,
                'retries': 3,
                'fragment_retries': 3,
                'retry_sleep': 5
            }

            retries = 3
            for cleaned_url in self.failed_quality_urls[:]:  # Copy to allow removal
                logging.debug(f"Retrying qualities for URL: {cleaned_url}")
                self.batch_formats_cache[cleaned_url] = {}
                self.batch_available_qualities[cleaned_url] = []
                for attempt in range(retries):
                    try:
                        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                            info = ydl.extract_info(cleaned_url, download=False)
                            formats = info.get('formats', [])
                            quality_list = []
                            seen_qualities = set()  # To track unique qualities
                            for f in formats:
                                resolution = f.get('height', None)
                                ext = f.get('ext', '')
                                vcodec = f.get('vcodec', 'none')
                                format_note = f.get('format_note', '').lower()
                                # Filter: Accept mp4/mkv video formats with resolution, exclude storyboards and audio-only
                                if (not resolution or ext not in ['mp4', 'mkv'] or vcodec == 'none' or
                                    'storyboard' in format_note or 'audio only' in format_note):
                                    continue
                                # Use mkv for resolutions > 1080p, mp4 otherwise
                                if resolution > 1080 and ext != 'mkv':
                                    continue
                                if resolution <= 1080 and ext != 'mp4':
                                    continue
                                format_id = f.get('format_id')
                                fps = f.get('fps', '')
                                filesize = f.get('filesize', 0) or f.get('filesize_approx', 0)
                                # Skip formats with no valid filesize
                                if not filesize or filesize <= 0:
                                    logging.debug(f"Skipped format for {cleaned_url}: {resolution}p {ext} - No valid filesize")
                                    continue
                                # Skip unrealistic filesizes (e.g., >10GB for a typical video)
                                if filesize > 10 * 1024 * 1024 * 1024:  # 10GB
                                    logging.debug(f"Skipped format for {cleaned_url}: {resolution}p {ext} - Unrealistic filesize {filesize}")
                                    continue
                                filesize_mb = filesize / (1024 * 1024)
                                # Create unique key to prevent duplicates
                                quality_key = f"{resolution}p_{ext}_{format_note}_{fps}"
                                if quality_key in seen_qualities:
                                    logging.debug(f"Skipped duplicate format for {cleaned_url}: {quality_key}")
                                    continue
                                seen_qualities.add(quality_key)
                                description = f"{resolution}p {ext}"
                                if format_note and format_note != str(resolution) + 'p':
                                    description += f" ({format_note})"
                                if fps:
                                    description += f" {fps}fps"
                                quality_display = f"{description} - {filesize_mb:.2f} ميجا"
                                has_audio = f.get('acodec', 'none') != 'none'
                                is_combined = vcodec != 'none' and has_audio
                                quality_list.append(quality_display)
                                self.batch_formats_cache[cleaned_url][quality_display] = (
                                    format_id,
                                    ext,
                                    filesize,
                                    format_note,
                                    is_combined
                                )
                                logging.debug(f"Format added for {cleaned_url}: {quality_display}, format_id={format_id}, filesize={filesize}")

                            if not quality_list:
                                raise Exception("No valid formats found")

                            quality_list.sort(key=lambda x: int(x.split('p')[0]) if 'p' in x and x.split('p')[0].isdigit() else 0)
                            self.batch_available_qualities[cleaned_url] = quality_list

                            title = info.get('title', 'غير معروف')
                            duration = info.get('duration', 'غير معروف')
                            if isinstance(duration, (int, float)):
                                duration = f"{int(duration // 60)}:{int(duration % 60):02d}"

                            # Show popup window for quality selection
                            def show_quality_popup():
                                popup = tkinter.Toplevel(self.root)
                                popup.title(self.translations[self.language].get("select_quality", "Select Quality"))
                                popup.geometry("400x200")
                                popup.transient(self.root)
                                popup.grab_set()

                                ttk.Label(popup, text=self.translations[self.language].get("select_quality", "Select Quality for:") + f" {title}").pack(pady=10)
                                quality_var = tkinter.StringVar(value=quality_list[-1] if quality_list else '')  # Default to highest quality
                                quality_combo = ttk.Combobox(popup, textvariable=quality_var, values=quality_list, state="readonly", width=50)
                                quality_combo.pack(pady=10)

                                def confirm_selection():
                                    selected_quality = quality_var.get()
                                    if not selected_quality:
                                        logging.warning(f"No quality selected for {cleaned_url}")
                                        popup.destroy()
                                        return
                                    self.batch_quality_selections[cleaned_url] = selected_quality
                                    filesize = self.batch_formats_cache[cleaned_url][selected_quality][2]
                                    filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"
                                    format_id, ext, filesize, format_note, is_combined = self.batch_formats_cache[cleaned_url][selected_quality]
                                    
                                    # Update Treeview item
                                    for item in self.batch_tree.get_children():
                                        if self.batch_tree.item(item)["values"][0].startswith(cleaned_url[:50]):
                                            self.batch_tree.item(item, values=(
                                                cleaned_url[:50] + "..." if len(cleaned_url) > 50 else cleaned_url,
                                                title,
                                                duration,
                                                selected_quality,
                                                f"{filesize_mb:.2f} ميجا" if isinstance(filesize_mb, float) else filesize_mb
                                            ))
                                            break

                                    self.batch_download_items.append({
                                        'url': cleaned_url,
                                        'title': title,
                                        'duration': duration,
                                        'quality': selected_quality,
                                        'format_id': format_id,
                                        'ext': ext,
                                        'is_combined': is_combined,
                                        'filesize_mb': filesize_mb,
                                        'tree_item_id': item
                                    })
                                    self.failed_quality_urls.remove(cleaned_url)
                                    logging.debug(f"Added {cleaned_url} to Treeview with quality {selected_quality}, format_id={format_id}")
                                    popup.destroy()

                                confirm_button = ttk.Button(
                                    popup,
                                    text=self.translations[self.language].get("confirm", "Confirm"),
                                    command=confirm_selection,
                                    style="Accent.TButton"
                                )
                                confirm_button.pack(pady=10)

                            self.root.after(0, show_quality_popup)
                        break

                    except Exception as e:
                        logging.error(f"Retry error for {cleaned_url} (attempt {attempt + 1}/{retries}): {type(e).__name__}: {e}")
                        if attempt == retries - 1:
                            self.root.after(0, lambda err=str(e): messagebox.showwarning(
                                self.translations[self.language]["warning"],
                                f"فشل جلب الجودات لـ {cleaned_url}: {err}"
                            ))
                            logging.debug(f"Retry failed for {cleaned_url}, kept in failed_quality_urls")
                        time.sleep(5)
                        continue

            self.root.after(0, lambda: [
                self.status_bar.configure(
                    text=self.translations[self.language].get("found_formats", "تم العثور على {} جودة/جودات").format(len(self.batch_download_items))
                ),
                self.batch_progress_bar.stop(),
                self.batch_progress_bar.pack_forget()
            ])
            logging.debug(f"Retry completed, {len(self.batch_download_items)} items ready for download")

        # Show and start progress bar
        self.batch_progress_bar.pack(fill=tkinter.X, padx=5, pady=5)
        self.batch_progress_bar.start(10)  # Faster animation
        threading.Thread(target=retry_thread, daemon=True).start()
    def create_quality_combobox(self, item_id, url, qualities, default_quality, vcodec, acodec, filesize_mb):
        """Create a Combobox for quality selection with enhanced features."""
        def try_create_combobox(attempt=0, max_attempts=20):
            try:
                # تحديث الواجهة لضمان العرض الصحيح
                self.batch_tree.update()
                self.batch_tree.update_idletasks()
                self.root.update()
                self.root.update_idletasks()

                bbox = self.batch_tree.bbox(item_id, "#4")
                logging.debug(f"Attempt {attempt} to create Combobox for {item_id}, bbox: {bbox}")
                if not bbox or not all(bbox):
                    if attempt < max_attempts:
                        # زيادة التأخير الأولي للتأكد من الرندر
                        self.root.after(1500 if attempt == 0 else 500, lambda: try_create_combobox(attempt + 1))
                        return
                    else:
                        logging.error(f"Failed to create Combobox for {item_id} after {max_attempts} attempts")
                        # محاولة وضع الـ Combobox في مكان افتراضي إذا فشل الـ bbox
                        x, y, width, height = 300, 100, 150, 25  # قيم افتراضية
                else:
                    x, y, width, height = bbox

                combo = ttk.Combobox(self.batch_tree, values=qualities, state="readonly", width=20)
                combo.set(default_quality)
                combo.place(x=x, y=y, width=width, height=height)
                combo.lift()

                # تحديد اللون بناءً على الجودة
                resolution = int(default_quality.split('p')[0]) if 'p' in default_quality and default_quality.split('p')[0].isdigit() else 0
                if resolution >= 1080:
                    combo.configure(style="HighQuality.TCombobox")
                elif resolution >= 720:
                    combo.configure(style="MediumQuality.TCombobox")
                else:
                    combo.configure(style="LowQuality.TCombobox")

                self.combobox_widgets[item_id] = combo

                def show_tooltip(event):
                    if item_id in self.tooltip_windows and self.tooltip_windows[item_id]:
                        self.tooltip_windows[item_id].destroy()
                    tooltip = tk.Toplevel(self.batch_tree)
                    tooltip.wm_overrideredirect(True)
                    tooltip.wm_geometry(f"+{event.x_root + 10}+{event.y_root + 10}")
                    filesize_mb = self.batch_formats_cache[url][combo.get()][2] / (1024 * 1024) if self.batch_formats_cache[url][combo.get()][2] else 0
                    label = tk.Label(
                        tooltip,
                        text=(
                            self.translations[self.language]["tooltip_video"].format(self.batch_formats_cache[url][combo.get()][5]) +
                            self.translations[self.language]["tooltip_audio"].format(self.batch_formats_cache[url][combo.get()][6]) +
                            self.translations[self.language]["tooltip_size"].format(filesize_mb)
                        ),
                            background="#ffffe0",
                            relief="solid",
                            borderwidth=1
                    )
                    label.pack()
                    self.tooltip_windows[item_id] = tooltip

                def hide_tooltip(event):
                    if item_id in self.tooltip_windows and self.tooltip_windows[item_id]:
                        self.tooltip_windows[item_id].destroy()
                        self.tooltip_windows[item_id] = None

                combo.bind("<Enter>", show_tooltip)
                combo.bind("<Leave>", hide_tooltip)

                def on_select(event):
                    new_quality = event.widget.get()
                    if new_quality:
                        self.batch_quality_selections[url] = new_quality
                        format_id, ext, filesize, format_note, is_combined, vcodec, acodec = self.batch_formats_cache[url][new_quality]
                        filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"
                        values = self.batch_tree.item(item_id, "values")
                        self.batch_tree.item(item_id, values=(
                            values[0],
                            values[1],
                            values[2],
                            new_quality,
                            f"{filesize_mb:.2f} ميجا" if isinstance(filesize_mb, float) else filesize_mb,
                            values[5]
                        ))
                        for data in self.batch_download_items:
                            if data['url'] == url:
                                data.update({
                                    'quality': new_quality,
                                    'format_id': format_id,
                                    'ext': ext,
                                    'filesize_mb': filesize_mb,
                                    'is_combined': is_combined
                                })
                                break

                        # تحديث لون الـ Combobox بناءً على الجودة الجديدة
                        resolution = int(new_quality.split('p')[0]) if 'p' in new_quality and new_quality.split('p')[0].isdigit() else 0
                        if resolution >= 1080:
                            combo.configure(style="HighQuality.TCombobox")
                        elif resolution >= 720:
                            combo.configure(style="MediumQuality.TCombobox")
                        else:
                            combo.configure(style="LowQuality.TCombobox")

                combo.bind("<<ComboboxSelected>>", on_select)
                self.update_comboboxes_on_scroll()

            except Exception as e:
                logging.error(f"Error creating Combobox for {item_id}: {e}")
                if attempt < max_attempts:
                    self.root.after(1500 if attempt == 0 else 500, lambda: try_create_combobox(attempt + 1))

        # استدعاء الدالة فورًا لضمان ظهور الـ Combobox تلقائيًا
        try_create_combobox()
    def retry_selected_qualities(self):
        """Retry fetching qualities for selected URLs in the Treeview."""
        selected_items = self.batch_tree.selection()
        if not selected_items:
            messagebox.showinfo("معلومات", "يرجى تحديد رابط واحد على الأقل لإعادة جلب الجودات")
            return

        ydl_opts = {
            'quiet': True,
            'no_warnings': True,
            'no_m3u8': True,
            'http_headers': {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
            },
            'socket_timeout': 30,
            'retries': 3,
            'fragment_retries': 3,
            'retry_sleep': 5,
            'format_sort': ['+res', '+fps']
        }

        def process_selected(index=0):
            if index >= len(selected_items):
                messagebox.showinfo("معلومات", f"تم إعادة جلب الجودات لـ {len(selected_items)} رابط/روابط")
                return

            item_id = selected_items[index]
            values = self.batch_tree.item(item_id, "values")
            url = values[0] if len(values[0]) <= 53 else values[0][:-3]  # إزالة "..." إذا كان موجودًا
            cleaned_url = self.clean_youtube_url(url)
            retries = 3
            attempt = 0

            def try_fetch():
                nonlocal attempt
                try:
                    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                        info = ydl.extract_info(cleaned_url, download=False)
                        if not info or 'title' not in info:
                            raise yt_dlp.utils.DownloadError("Video unavailable or restricted")

                        title = info.get('title', 'غير معروف')
                        duration = info.get('duration', 'غير معروف')
                        if isinstance(duration, (int, float)):
                            duration = f"{int(duration // 60)}:{int(duration % 60):02d}"

                        formats = info.get('formats', [])
                        quality_list = []
                        self.batch_formats_cache[cleaned_url] = {}
                        self.batch_available_qualities[cleaned_url] = []

                        for f in formats:
                            resolution = f.get('height', None)
                            ext = f.get('ext', 'mp4')
                            if not resolution or ext == 'webm':
                                continue
                            format_id = f.get('format_id')
                            format_note = f.get('format_note', '')
                            fps = f.get('fps', '')
                            filesize = f.get('filesize', 0) or f.get('filesize_approx', 0)
                            filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"
                            description = f"{resolution}p {ext} ({format_note})" if format_note else f"{resolution}p {ext}"
                            if fps:
                                description += f" {fps}fps"
                            quality_display = description
                            has_video = f.get('vcodec', 'none') != 'none'
                            has_audio = f.get('acodec', 'none') != 'none'
                            is_combined = has_video and has_audio
                            quality_list.append(quality_display)
                            self.batch_formats_cache[cleaned_url][quality_display] = (
                                format_id,
                                ext,
                                filesize if filesize else 0,
                                format_note,
                                is_combined,
                                f.get('vcodec', 'غير معروف'),
                                f.get('acodec', 'غير معروف')
                            )

                        quality_list.sort(key=lambda x: int(x.split('p')[0]) if 'p' in x and x.split('p')[0].isdigit() else 0)
                        self.batch_available_qualities[cleaned_url] = quality_list

                        default_quality = quality_list[-1] if quality_list else "غير محدد"
                        self.batch_quality_selections[cleaned_url] = default_quality

                        filesize = self.batch_formats_cache[cleaned_url][default_quality][2] if default_quality != "غير محدد" else 0
                        filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"
                        self.batch_tree.item(item_id, values=(
                            cleaned_url[:50] + "..." if len(cleaned_url) > 50 else cleaned_url,
                            title,
                            duration,
                            default_quality,
                            f"{filesize_mb:.2f} ميجا" if isinstance(filesize_mb, float) else filesize_mb
                        ))

                        # تحديث الـ Combobox إذا كان موجودًا
                        if item_id in self.combobox_widgets:
                            self.combobox_widgets[item_id].destroy()
                            del self.combobox_widgets[item_id]

                        if default_quality != "غير محدد" and not self.use_single_quality_var.get() and quality_list:
                            format_id, ext, filesize, format_note, is_combined, vcodec, acodec = self.batch_formats_cache[cleaned_url][default_quality]
                            for data in self.batch_download_items:
                                if data['url'] == cleaned_url:
                                    data.update({
                                        'title': title,
                                        'duration': duration,
                                        'quality': default_quality,
                                        'format_id': format_id,
                                        'ext': ext,
                                        'is_combined': is_combined,
                                        'filesize_mb': filesize_mb
                                    })
                                    break
                            self.create_quality_combobox(item_id, cleaned_url, quality_list, default_quality, vcodec, acodec, filesize_mb)

                        process_selected(index + 1)

                except Exception as e:
                    logging.error(f"Error retrying qualities for {cleaned_url}: {e}")
                    if attempt < retries - 1:
                        attempt += 1
                        self.root.after(5000, try_fetch)
                    else:
                        messagebox.showwarning("تحذير", f"فشل إعادة جلب الجودات لـ {cleaned_url}: {e}")
                        process_selected(index + 1)

            try_fetch()

        process_selected()
    def create_action_buttons(self, item_id, url):
        """Create action buttons in the 'actions' column of the Treeview."""
        def try_create_buttons(attempt=0, max_attempts=15):
            try:
                self.batch_tree.update()
                self.batch_tree.update_idletasks()
                self.root.update()
                self.root.update_idletasks()

                bbox = self.batch_tree.bbox(item_id, "#6")  # عمود "الإجراءات"
                logging.debug(f"Attempt {attempt} to create buttons for {item_id}, bbox: {bbox}")
                if not bbox or not all(bbox):
                    if attempt < max_attempts:
                        self.root.after(500, lambda: try_create_buttons(attempt + 1))
                        return
                    else:
                        logging.error(f"Failed to create buttons for {item_id} after {max_attempts} attempts")
                        return

                x, y, width, height = bbox
                button_frame = tk.Frame(self.batch_tree)
                button_frame.place(x=x, y=y, width=width, height=height)

                retry_button = ttk.Button(
                    button_frame,
                    text=self.translations[self.language].get("retry", "إعادة جلب"),
                    style="Accent.TButton",
                    command=lambda: self.retry_fetch_qualities(item_id, url)
                )
                retry_button.pack(side=tk.LEFT, padx=2)

                self.action_buttons[item_id] = button_frame

            except Exception as e:
                logging.error(f"Error creating buttons for {item_id}: {e}")
                if attempt < max_attempts:
                    self.root.after(500, lambda: try_create_buttons(attempt + 1))

        try_create_buttons()
    def retry_fetch_qualities(self, item_id, url):
        """Retry fetching qualities for a specific URL in the Treeview."""
        cleaned_url = self.clean_youtube_url(url)
        ydl_opts = {
            'quiet': True,
            'no_warnings': True,
            'no_m3u8': True,
            'http_headers': {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
            },
            'socket_timeout': 30,
            'retries': 3,
            'fragment_retries': 3,
            'retry_sleep': 5,
            'format_sort': ['+res', '+fps']
        }

        retries = 3
        attempt = 0

        def try_fetch():
            nonlocal attempt
            try:
                with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                    info = ydl.extract_info(cleaned_url, download=False)
                    if not info or 'title' not in info:
                        raise yt_dlp.utils.DownloadError("Video unavailable or restricted")

                    title = info.get('title', 'غير معروف')
                    duration = info.get('duration', 'غير معروف')
                    if isinstance(duration, (int, float)):
                        duration = f"{int(duration // 60)}:{int(duration % 60):02d}"

                    formats = info.get('formats', [])
                    quality_list = []
                    self.batch_formats_cache[cleaned_url] = {}
                    self.batch_available_qualities[cleaned_url] = []

                    for f in formats:
                        resolution = f.get('height', None)
                        ext = f.get('ext', 'mp4')
                        if not resolution or ext == 'webm':
                            continue
                        format_id = f.get('format_id')
                        format_note = f.get('format_note', '')
                        fps = f.get('fps', '')
                        filesize = f.get('filesize', 0) or f.get('filesize_approx', 0)
                        filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"
                        quality_key = f"{resolution}p {ext}"
                        if format_note and format_note != str(resolution) + 'p':
                            quality_key += f" ({format_note})"
                        if fps:
                            quality_key += f" {fps}fps"
                        quality_display = f"{quality_key} - {filesize_mb:.2f} ميجا" if isinstance(filesize_mb, float) else f"{quality_key} - {filesize_mb}"
                        has_video = f.get('vcodec', 'none') != 'none'
                        has_audio = f.get('acodec', 'none') != 'none'
                        is_combined = has_video and has_audio
                        quality_list.append(quality_display)
                        self.batch_formats_cache[cleaned_url][quality_key] = (
                            format_id,
                            ext,
                            filesize,
                            format_note,
                            is_combined,
                            f.get('vcodec', 'غير معروف'),
                            f.get('acodec', 'غير معروف')
                        )

                    quality_list.sort(key=lambda x: int(x.split('p')[0]) if 'p' in x and x.split('p')[0].isdigit() else 0)
                    self.batch_available_qualities[cleaned_url] = quality_list

                    default_quality = quality_list[-1].split(' - ')[0].strip() if quality_list else "غير محدد"
                    self.batch_quality_selections[cleaned_url] = default_quality

                    filesize = self.batch_formats_cache[cleaned_url][default_quality][2] if default_quality != "غير محدد" else 0
                    filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"
                    self.batch_tree.item(item_id, values=(
                        cleaned_url[:50] + "..." if len(cleaned_url) > 50 else cleaned_url,
                        title,
                        duration,
                        default_quality,
                        f"{filesize_mb:.2f} ميجا" if isinstance(filesize_mb, float) else filesize_mb,
                        ""
                    ))

                    # تحديث الـ Combobox إذا كان موجودًا
                    if item_id in self.combobox_widgets:
                        self.combobox_widgets[item_id].destroy()
                        del self.combobox_widgets[item_id]

                    if default_quality != "غير محدد" and not self.use_single_quality_var.get() and quality_list:
                        format_id, ext, filesize, format_note, is_combined, vcodec, acodec = self.batch_formats_cache[cleaned_url][default_quality]
                        for data in self.batch_download_items:
                            if data['url'] == cleaned_url:
                                data.update({
                                    'title': title,
                                    'duration': duration,
                                    'quality': default_quality,
                                    'format_id': format_id,
                                    'ext': ext,
                                    'is_combined': is_combined,
                                    'filesize_mb': filesize_mb
                                })
                                break
                        # إنشاء الـ Combobox بعد إعادة جلب الجودات
                        self.create_quality_combobox(item_id, cleaned_url, quality_list, default_quality, vcodec, acodec, filesize_mb)

            except Exception as e:
                logging.error(f"Error retrying qualities for {cleaned_url}: {e}")
                if attempt < retries - 1:
                    attempt += 1
                    self.root.after(5000, try_fetch)
                else:
                    messagebox.showwarning("تحذير", f"فشل إعادة جلب الجودات لـ {cleaned_url}: {e}")

        try_fetch()
    def show_video_preview(self, event):
        """Show a preview window with the video thumbnail on double-click."""
        import tkinter as tk
        from tkinter import ttk, messagebox

        item_id = self.batch_tree.identify_row(event.y)
        if not item_id:
            return

        values = self.batch_tree.item(item_id, "values")
        url = values[0] if len(values[0]) <= 53 else values[0][:-3]  # Remove "..." if present

        # Fallback if thumbnail_cache or clean_youtube_url are not defined
        if not hasattr(self, 'thumbnail_cache') or not hasattr(self, 'clean_youtube_url'):
            messagebox.showinfo(
                self.translations[self.language]["info"],
                self.translations[self.language]["preview"] if self.language == "en" else "معاينة الفيديو غير متاحة"
            )
            return

        cleaned_url = self.clean_youtube_url(url)
        if cleaned_url not in self.thumbnail_cache or self.thumbnail_cache[cleaned_url] is None:
            messagebox.showinfo(
                self.translations[self.language]["info"],
                self.translations[self.language]["preview"] if self.language == "en" else "الصورة المصغرة غير متاحة لهذا الفيديو"
            )
            return

        preview_window = tk.Toplevel(self.root)
        preview_window.title(self.translations[self.language].get("preview", "معاينة الفيديو"))
        preview_window.geometry("400x400")

        thumbnail = self.thumbnail_cache[cleaned_url]
        label = tk.Label(preview_window, image=thumbnail)
        label.pack(padx=10, pady=10)

        preview_window.transient(self.root)
        preview_window.grab_set()

    def update_batch_quality(self, event, url, item_id):
        """Update the quality for a batch item when selected from Combobox."""
        quality_combobox = event.widget
        selected_quality = quality_combobox.get()
        if not selected_quality:
            logging.debug("لم يتم اختيار جودة من القائمة المنسدلة")
            return

        for item_data in self.batch_download_items:
            if item_data['tree_item_id'] == item_id:
                item_data['quality'] = selected_quality
                format_id, ext, filesize, format_note, is_combined = self.batch_formats_cache[url][selected_quality]
                filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"
                item_data.update({
                    'format_id': format_id,
                    'ext': ext,
                    'filesize_mb': filesize_mb,
                    'is_combined': is_combined
                })
                logging.debug(f"تم تحديث الجودة لـ {url}: {selected_quality}")

                self.batch_tree.item(item_id, values=(
                    item_data['url'][:50] + "..." if len(item_data['url']) > 50 else item_data['url'],
                    item_data['title'],
                    item_data['duration'],
                    selected_quality,
                    f"{filesize_mb:.2f} ميجا" if isinstance(filesize_mb, float) else filesize_mb
                ))
                break


    def create_progress_window(self, url, total_bytes, filename, save_path):
        """Create a progress window similar to IDM with smooth progress bar and controls."""
        import tkinter as tk
        from tkinter import ttk
        import logging
        import hashlib

        logging.basicConfig(level=logging.DEBUG)

        try:
            # Create a unique task_id for the download
            url_hash = hashlib.md5(url.encode('utf-8')).hexdigest()
            task_id = f"download_{url_hash}"

            # Check if window already exists
            if task_id in self.download_windows and self.download_windows[task_id]['window'].winfo_exists():
                logging.debug(f"Progress window for {url} (task_id: {task_id}) already exists")
                self.download_windows[task_id]['window'].lift()
                return self.download_windows[task_id]

            # Create a new top-level window
            window = tk.Toplevel(self.root)
            window.title(self.translations[self.language].get("downloading", "Downloading").format(url[:30] + "..."))
            window.geometry("600x400")
            window.transient(self.root)
            window.grab_set()
            window.configure(bg=self.secondary_color)
            window.resizable(False, False)

            # Main frame
            main_frame = ttk.Frame(window, padding="10")
            main_frame.pack(fill=tk.BOTH, expand=True)
            main_frame.grid_columnconfigure(0, weight=1)
            main_frame.grid_columnconfigure(1, weight=1)
            main_frame.grid_rowconfigure(0, weight=1)
            main_frame.grid_rowconfigure(1, weight=0)
            main_frame.grid_rowconfigure(2, weight=0)
            main_frame.grid_rowconfigure(3, weight=0)
            main_frame.grid_rowconfigure(4, weight=0)
            main_frame.grid_rowconfigure(5, weight=0)
            main_frame.grid_rowconfigure(6, weight=1)

            # Progress bar
            progress_bar = ttk.Progressbar(main_frame, mode="determinate", maximum=100, length=550)
            progress_bar.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 10))

            # Status label for download stage
            status_label = ttk.Label(
                main_frame,
                text=self.translations[self.language].get("starting_download", "Starting download..."),
                style="TLabel"
            )
            status_label.grid(row=1, column=0, columnspan=2, sticky="w")

            # Labels for file info
            filename_label = ttk.Label(
                main_frame,
                text=f"{self.translations[self.language].get('file_name', 'File')}: {filename or 'غير معروف'}",
                wraplength=550,
                style="TLabel"
            )
            filename_label.grid(row=2, column=0, columnspan=2, sticky="w")

            save_path_label = ttk.Label(
                main_frame,
                text=f"{self.translations[self.language].get('save_path', 'Path')}: {save_path or self.save_path}",
                wraplength=550,
                style="TLabel"
            )
            save_path_label.grid(row=3, column=0, columnspan=2, sticky="w")

            # File size label
            file_size_text = "-- MB"
            try:
                total_bytes = int(total_bytes) if total_bytes else 0
                if total_bytes > 0:
                    file_size_text = f"{total_bytes / (1024 * 1024):.2f} MB"
            except (ValueError, TypeError):
                logging.warning(f"Invalid total_bytes value for {url}: {total_bytes}")
            file_size_label = ttk.Label(
                main_frame,
                text=f"{self.translations[self.language].get('file_size', 'File Size')}: {file_size_text}",
                style="TLabel"
            )
            file_size_label.grid(row=4, column=0, columnspan=2, sticky="w")

            # Labels for dynamic info
            speed_label = ttk.Label(
                main_frame,
                text=f"{self.translations[self.language].get('speed', 'Speed')}: 0.00 MB/s",
                style="TLabel"
            )
            speed_label.grid(row=5, column=0, sticky="w")

            eta_label = ttk.Label(
                main_frame,
                text=f"{self.translations[self.language].get('eta', 'Time remaining')}: --",
                style="TLabel"
            )
            eta_label.grid(row=5, column=1, sticky="e")

            # Buttons frame
            button_frame = ttk.Frame(main_frame)
            button_frame.grid(row=6, column=0, columnspan=2, pady=10)

            def pause_download_wrapper():
                if task_id in self.download_threads:
                    pause_event = self.download_threads[task_id].get('pause_event')
                    if pause_event and pause_event.is_set():
                        self.pause_download(task_id, pause_button, resume_button)
                        status_label.config(
                            text=self.translations[self.language].get("paused", "Paused (Low Speed)")
                        )
                        logging.debug(f"Paused download for {url}")

            def resume_download_wrapper():
                if task_id in self.download_threads:
                    pause_event = self.download_threads[task_id].get('pause_event')
                    if pause_event and not pause_event.is_set():
                        self.resume_download(task_id, pause_button, resume_button)
                        status_label.config(
                            text=self.translations[self.language].get("starting_download", "Starting download...")
                        )
                        logging.debug(f"Resumed download for {url}")

            def cancel_download_wrapper():
                if task_id in self.download_threads:
                    self.cancel_download(url, window, task_id)
                    logging.debug(f"Cancelled download for {url}")

            pause_button = ttk.Button(
                button_frame,
                text=self.translations[self.language].get("pause", "Pause"),
                command=pause_download_wrapper,
                style="Accent.TButton"
            )
            pause_button.pack(side=tk.LEFT, padx=5)

            resume_button = ttk.Button(
                button_frame,
                text=self.translations[self.language].get("resume", "Resume"),
                command=resume_download_wrapper,
                style="Accent.TButton",
                state="disabled"
            )
            resume_button.pack(side=tk.LEFT, padx=5)

            cancel_button = ttk.Button(
                button_frame,
                text=self.translations[self.language].get("cancel", "Cancel"),
                command=cancel_download_wrapper,
                style="Accent.TButton"
            )
            cancel_button.pack(side=tk.LEFT, padx=5)

            # Store window and widgets in download_windows
            self.download_windows[task_id] = {
                'window': window,
                'progress_bar': progress_bar,
                'status_label': status_label,
                'filename_label': filename_label,
                'save_path_label': save_path_label,
                'file_size_label': file_size_label,
                'speed_label': speed_label,
                'eta_label': eta_label,
                'pause_button': pause_button,
                'resume_button': resume_button,
                'cancel_button': cancel_button,
                'stage': 'initial'  # Track download stage: initial, video, audio, merging
            }

            # Handle window close
            window.protocol("WM_DELETE_WINDOW", cancel_download_wrapper)

            logging.debug(f"Progress window created for URL: {url} with task_id {task_id}")
            return self.download_windows[task_id]

        except Exception as e:
            logging.error(f"Error creating progress window for {url}: {str(e)}")
            return None

    def update_progress_window(self, window, progress, speed, eta, size):
        """Update the progress window with current download stats."""
        try:
            if not window or not window['window'].winfo_exists():
                logging.warning("Progress window does not exist or was destroyed")
                return

            # Update progress bar
            window['progress_bar']['value'] = progress
            window['status_label'].config(
                text=self.translations[self.language].get("progress", "Progress") + f": {progress:.1f}%"
            )

            # Update file size
            window['size_label'].config(text=f"{size:.2f} MB")

            # Update speed
            window['speed_label'].config(
                text=self.translations[self.language].get("download_speed", "Speed: {:.2f} MB/s").format(speed / 1024)
            )

            # Format and update ETA
            if eta <= 0:
                eta_text = self.translations[self.language].get("eta", "ETA: {}").format("Unknown")
            elif eta < 60:
                eta_text = self.translations[self.language].get("eta", "ETA: {}").format(f"{int(eta)} seconds")
            elif eta < 3600:
                eta_text = self.translations[self.language].get("eta", "ETA: {}").format(f"{int(eta // 60)} minutes")
            else:
                hours = int(eta // 3600)
                minutes = int((eta % 3600) // 60)
                eta_text = self.translations[self.language].get("eta", "ETA: {}").format(f"{hours} hours {minutes} minutes")

            window['eta_label'].config(text=eta_text)

            # Update window
            window['window'].update_idletasks()
            logging.debug(f"Progress window updated: progress={progress:.1f}%, speed={speed / 1024:.2f} MB/s, eta={eta_text}")

        except Exception as e:
            logging.error(f"Error updating progress window: {str(e)}")

    def create_progress_hook(self):
        """Create a progress hook for yt_dlp to update download progress."""
        import time
        import logging
        import hashlib
        import os

        logging.basicConfig(level=logging.DEBUG)

        def progress_hook(d):
            url = d.get('info_dict', {}).get('webpage_url', 'unknown')
            url_hash = hashlib.md5(url.encode('utf-8')).hexdigest()
            task_id = f"download_{url_hash}"

            logging.debug(f"Progress hook called for {url}, task_id: {task_id}, status: {d.get('status')}")

            try:
                # Check if task exists
                if task_id not in self.download_threads:
                    logging.warning(f"Task {task_id} not found in download_threads")
                    return

                # Check if window exists
                if task_id not in self.download_windows or not self.download_windows[task_id]['window'].winfo_exists():
                    logging.warning(f"No window found for task_id {task_id}")
                    return

                window = self.download_windows[task_id]
                progress_bar = window['progress_bar']
                status_label = window['status_label']
                speed_label = window['speed_label']
                eta_label = window['eta_label']
                file_size_label = window['file_size_label']

                # Determine current stage
                if d['status'] == 'downloading':
                    if d.get('filename', '').endswith(('.mp3', '.m4a')):
                        window['stage'] = 'audio'
                    else:
                        window['stage'] = 'video'
                elif d.get('status') == 'postprocessing' and 'Merging' in d.get('postprocessor', ''):
                    window['stage'] = 'merging'
                elif d['status'] == 'finished':
                    if self.download_threads[task_id].get('merged', True):
                        window['stage'] = 'finished'
                    elif window['stage'] == 'video':
                        window['stage'] = 'audio'
                    elif window['stage'] == 'audio':
                        window['stage'] = 'merging'

                # Calculate progress based on stage
                downloaded_bytes = d.get('downloaded_bytes', 0)
                total_bytes = d.get('total_bytes', d.get('total_bytes_estimate', self.download_threads[task_id]['file_size']))
                current_time = time.time()

                # Check if paused (low speed mode)
                is_paused = self.download_threads[task_id].get('ratelimit', None) == 1024
                if is_paused:
                    status_label.config(
                        text=self.translations[self.language].get("paused", "Paused (Low Speed)")
                    )

                if window['stage'] == 'video':
                    # Video: 0-50%
                    progress = (downloaded_bytes / total_bytes * 50) if total_bytes > 0 else 0
                    if not is_paused:
                        status_label.config(
                            text=self.translations[self.language].get("downloading_video", "Downloading video...")
                        )
                elif window['stage'] == 'audio':
                    # Audio: 50-80%
                    progress = 50 + (downloaded_bytes / total_bytes * 30) if total_bytes > 0 else 50
                    if not is_paused:
                        status_label.config(
                            text=self.translations[self.language].get("downloading_audio", "Downloading audio...")
                        )
                elif window['stage'] == 'merging':
                    # Merging: 80-100%
                    progress = 80 + (downloaded_bytes / total_bytes * 20) if total_bytes > 0 else 80
                    if not is_paused:
                        status_label.config(
                            text=self.translations[self.language].get("merging", "Merging video and audio...")
                        )
                elif window['stage'] == 'finished':
                    progress = 100
                    if not is_paused:
                        status_label.config(
                            text=self.translations[self.language].get("download_complete", "Download complete!")
                        )

                # Update progress bar
                progress_bar.configure(value=progress)

                # Update file size
                file_size_text = f"{total_bytes / (1024 * 1024):.2f} MB" if total_bytes > 0 else "-- MB"
                file_size_label.configure(
                    text=f"{self.translations[self.language].get('file_size', 'File Size')}: {file_size_text}"
                )

                # Calculate speed and ETA
                time_diff = current_time - self.download_threads[task_id]['last_update_time']
                bytes_diff = downloaded_bytes - self.download_threads[task_id]['last_downloaded_bytes']
                speed_mbps = (bytes_diff / (1024 * 1024)) / time_diff if time_diff > 0 else 0
                remaining_bytes = total_bytes - downloaded_bytes if total_bytes > 0 else 0
                eta_seconds = remaining_bytes / (bytes_diff / time_diff) if bytes_diff > 0 and time_diff > 0 else 0

                # Format ETA
                if eta_seconds < 60:
                    eta_text = f"{int(eta_seconds)} ثانية" if self.language == "ar" else f"{int(eta_seconds)} seconds"
                elif eta_seconds < 3600:
                    eta_text = f"{int(eta_seconds // 60)} دقائق" if self.language == "ar" else f"{int(eta_seconds // 60)} minutes"
                else:
                    minutes = int(eta_seconds // 60)
                    seconds = int(eta_seconds % 60)
                    eta_text = f"{minutes} دقيقة و{seconds} ثانية" if self.language == "ar" else f"{minutes} minutes and {seconds} seconds"

                # Update labels
                speed_label.configure(
                    text=f"{self.translations[self.language].get('speed', 'Speed')}: {speed_mbps:.2f} MB/s"
                )
                eta_label.configure(
                    text=f"{self.translations[self.language].get('eta', 'Time remaining')}: {eta_text}"
                )

                # Update download_threads
                self.download_threads[task_id]['downloaded_bytes'] = downloaded_bytes
                self.download_threads[task_id]['file_size'] = total_bytes
                self.download_threads[task_id]['last_update_time'] = current_time
                self.download_threads[task_id]['last_downloaded_bytes'] = downloaded_bytes

                window['window'].update()

                # Handle completion
                if d['status'] == 'finished' and window['stage'] == 'finished' and self.download_threads[task_id]['merge_completed']:
                    logging.debug(f"Download finished for {task_id}")
                    title = d['info_dict'].get('title', 'Unknown')
                    filename = self.download_threads[task_id]['filepath']
                    file_size_bytes = os.path.getsize(filename) if os.path.exists(filename) else 0
                    duration = time.time() - self.download_threads[task_id]['start_time']

                    # Store completion details
                    completed_downloads = [{
                        'title': title,
                        'filesize_mb': file_size_bytes / (1024 * 1024),
                        'quality': self.download_threads[task_id].get('quality', 'N/A'),
                        'save_path': filename,
                        'download_time': duration,
                        'speed': f"{(file_size_bytes / (1024 * 1024)) / duration:.2f} MB/s" if duration > 0 else "Unknown",
                        'ext': self.download_threads[task_id]['ext']
                    }]

                    # Show completion window and clean up
                    self.root.after(0, lambda: self.show_completion_window(completed_downloads))
                    self.root.after(0, lambda: window['window'].destroy())
                    if task_id in self.download_windows:
                        del self.download_windows[task_id]
                    self.active_downloads -= 1
                    self.update_overall_progress()

            except Exception as e:
                logging.error(f"Error in progress_hook for {task_id}: {str(e)}")

        return progress_hook
    def fetch_batch(self):
        """Fetch qualities for batch URLs with enhanced error handling and display Combobox."""
        import logging
        import threading
        import tkinter as tk
        from tkinter import messagebox
        import yt_dlp

        logging.basicConfig(level=logging.DEBUG)

        urls_text = self.batch_urls_text.get("1.0", tk.END).strip()
        if not urls_text:
            logging.error("No URLs provided in batch input")
            messagebox.showerror("خطأ", self.translations[self.language].get("no_batch_urls", "يرجى إدخال روابط صالحة"))
            return

        urls = [url.strip() for url in urls_text.split('\n') if url.strip()]
        if not urls:
            logging.error("No valid URLs found in input")
            messagebox.showerror("خطأ", self.translations[self.language].get("no_batch_urls", "يرجى إدخال روابط صالحة"))
            return

        # Initialize batch data structures
        self.batch_urls = urls
        self.batch_download_items = []
        self.batch_available_qualities = {}
        self.batch_formats_cache = {}
        self.batch_quality_selections = {}
        self.batch_quality_comboboxes = {}

        def fetch_qualities_thread():
            ydl_opts = {
                'quiet': True,
                'no_warnings': True,
                'no_m3u8': True,
                'http_headers': {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
                },
                'socket_timeout': 30,
                'retries': 3,
                'fragment_retries': 3,
                'retry_sleep': 5,
                'format_sort': ['+res', '+fps']
            }

            # Clear existing items and Comboboxes
            self.root.after(0, lambda: [combo.destroy() for combo in self.batch_quality_comboboxes.values()])
            self.root.after(0, lambda: self.batch_quality_comboboxes.clear())
            self.root.after(0, lambda: [self.batch_tree.delete(item) for item in self.batch_tree.get_children()])

            for url in urls:
                cleaned_url = self.clean_youtube_url(url)
                retries = 3
                for attempt in range(retries):
                    try:
                        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                            info = ydl.extract_info(cleaned_url, download=False)
                            formats = info.get('formats', [])
                            quality_list = []
                            self.batch_formats_cache[cleaned_url] = {}
                            self.batch_available_qualities[cleaned_url] = []

                            if not info or 'title' not in info:
                                raise yt_dlp.utils.DownloadError("Video unavailable or restricted")

                            for f in formats:
                                resolution = f.get('height', None)
                                ext = f.get('ext', 'mp4')
                                if not resolution or ext == 'webm':
                                    continue
                                format_id = f.get('format_id')
                                format_note = f.get('format_note', '')
                                fps = f.get('fps', '')
                                filesize = f.get('filesize', 0) or f.get('filesize_approx', 0)
                                filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"
                                description = f"{resolution}p {ext} ({format_note})" if format_note else f"{resolution}p {ext}"
                                if fps:
                                    description += f" {fps}fps"
                                quality_display = f"{description} - {filesize_mb:.2f} ميجا" if isinstance(filesize_mb, float) else f"{description} - {filesize_mb}"
                                has_video = f.get('vcodec', 'none') != 'none'
                                has_audio = f.get('acodec', 'none') != 'none'
                                is_combined = has_video and has_audio
                                quality_list.append(quality_display)
                                self.batch_formats_cache[cleaned_url][quality_display] = (
                                    format_id,
                                    ext,
                                    filesize if filesize else 0,
                                    format_note,
                                    is_combined
                                )
                                logging.debug(f"Format added for {cleaned_url}: {quality_display}, filesize: {filesize}")

                            quality_list.sort(key=lambda x: int(x.split('p')[0]) if 'p' in x and x.split('p')[0].isdigit() else 0)
                            self.batch_available_qualities[cleaned_url] = quality_list

                            title = info.get('title', 'غير معروف')
                            duration = info.get('duration', 'غير معروف')
                            if isinstance(duration, (int, float)):
                                duration = f"{int(duration // 60)}:{int(duration % 60):02d}"

                            default_quality = quality_list[-1] if quality_list else "غير محدد"
                            self.batch_quality_selections[cleaned_url] = default_quality

                            filesize = self.batch_formats_cache[cleaned_url][default_quality][2] if default_quality != "غير محدد" else 0
                            filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"
                            item_id = self.batch_tree.insert("", "end", values=(
                                cleaned_url[:50] + "..." if len(cleaned_url) > 50 else cleaned_url,
                                title,
                                duration,
                                default_quality,
                                f"{filesize_mb:.2f} ميجا" if isinstance(filesize_mb, float) else filesize_mb
                            ))

                            if default_quality != "غير محدد":
                                format_id, ext, filesize, format_note, is_combined = self.batch_formats_cache[cleaned_url][default_quality]
                                self.batch_download_items.append({
                                    'url': cleaned_url,
                                    'title': title,
                                    'duration': duration,
                                    'quality': default_quality,
                                    'format_id': format_id,
                                    'ext': ext,
                                    'is_combined': is_combined,
                                    'filesize_mb': filesize_mb,
                                    'tree_item_id': item_id
                                })
                                logging.debug(f"Added download item for {cleaned_url} with quality {default_quality}")

                                # Create Combobox for quality selection if not using single quality
                                if not self.use_single_quality_var.get() and quality_list:
                                    def add_combobox(i=item_id, u=cleaned_url, q=quality_list, attempt=0):
                                        if i in self.batch_quality_comboboxes:
                                            self.batch_quality_comboboxes[i].destroy()
                                            del self.batch_quality_comboboxes[i]

                                        self.batch_tree.update()
                                        self.batch_tree.update_idletasks()
                                        bbox = self.batch_tree.bbox(i, "#4")
                                        logging.debug(f"Attempt {attempt} - Creating Combobox for item {i}, bbox: {bbox}")
                                        if not bbox or not all(bbox):
                                            if attempt < 5:
                                                self.root.after(500, lambda: add_combobox(i, u, q, attempt + 1))
                                                return
                                            logging.error(f"Failed to get valid bbox for item {i} after {attempt} attempts")
                                            return

                                        x, y, width, height = bbox
                                        logging.debug(f"Placing Combobox at x={x}, y={y}, width={width}, height={height}")
                                        combo = ttk.Combobox(self.batch_tree, values=q, state="readonly", width=40)
                                        combo.set(self.batch_quality_selections.get(u, q[-1]))
                                        combo.place(x=x, y=y, width=width, height=height)
                                        combo.lift()
                                        self.batch_quality_comboboxes[i] = combo

                                        def on_select(event, u=u, i=i):
                                            new_quality = event.widget.get()
                                            if new_quality:
                                                self.batch_quality_selections[u] = new_quality
                                                format_id, ext, filesize, format_note, is_combined = self.batch_formats_cache[u][new_quality]
                                                filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"
                                                values = self.batch_tree.item(i, "values")
                                                self.batch_tree.item(i, values=(
                                                    values[0],
                                                    values[1],
                                                    values[2],
                                                    new_quality,
                                                    f"{filesize_mb:.2f} ميجا" if isinstance(filesize_mb, float) else filesize_mb
                                                ))
                                                for data in self.batch_download_items:
                                                    if data['url'] == u:
                                                        data.update({
                                                            'quality': new_quality,
                                                            'format_id': format_id,
                                                            'ext': ext,
                                                            'filesize_mb': filesize_mb,
                                                            'is_combined': is_combined
                                                        })
                                                        break

                                        combo.bind("<<ComboboxSelected>>", on_select)
                                        self.update_combobox_position()

                                    self.root.after(500, lambda: add_combobox(i=item_id, u=cleaned_url, q=quality_list))
                            else:
                                logging.warning(f"No qualities available for {cleaned_url}")
                                self.root.after(0, lambda: messagebox.showwarning(
                                    "تحذير", f"لم يتم العثور على جودات لـ {cleaned_url}"
                                ))

                        break

                    except yt_dlp.utils.DownloadError as e:
                        logging.error(f"DownloadError for {cleaned_url} (attempt {attempt + 1}/{retries}): {e}")
                        if attempt == retries - 1:
                            self.root.after(0, lambda: messagebox.showwarning(
                                "تحذير", f"فشل جلب الجودات لـ {cleaned_url} بعد {retries} محاولات: {e}"
                            ))
                            self.batch_tree.insert("", "end", values=(
                                cleaned_url[:50] + "..." if len(cleaned_url) > 50 else cleaned_url,
                                "غير معروف",
                                "غير معروف",
                                "غير محدد",
                                "غير معروف"
                            ))
                        time.sleep(5)
                        continue
                    except yt_dlp.utils.ExtractorError as e:
                        logging.error(f"ExtractorError for {cleaned_url} (attempt {attempt + 1}/{retries}): {e}")
                        if attempt == retries - 1:
                            self.root.after(0, lambda: messagebox.showwarning(
                                "تحذير", f"لا يمكن استخراج بيانات الرابط {cleaned_url}: {e}"
                            ))
                            self.batch_tree.insert("", "end", values=(
                                cleaned_url[:50] + "..." if len(cleaned_url) > 50 else cleaned_url,
                                "غير معروف",
                                "غير معروف",
                                "غير محدد",
                                "غير معروف"
                            ))
                        time.sleep(5)
                        continue
                    except Exception as e:
                        logging.error(f"Unexpected error for {cleaned_url} (attempt {attempt + 1}/{retries}): {type(e).__name__}: {e}")
                        if attempt == retries - 1:
                            self.root.after(0, lambda: messagebox.showwarning(
                                "تحذير", f"خطأ غير متوقع للرابط {cleaned_url}: {type(e).__name__}: {e}"
                            ))
                            self.batch_tree.insert("", "end", values=(
                                cleaned_url[:50] + "..." if len(cleaned_url) > 50 else cleaned_url,
                                "غير معروف",
                                "غير معروف",
                                "غير محدد",
                                "غير معروف"
                            ))
                        time.sleep(5)
                        continue

            self.root.after(0, lambda: self.status_bar.config(
                text=self.translations[self.language].get("found_formats", "تم العثور على {} جودة/جودات").format(len(self.batch_download_items))
            ))
            logging.debug(f"Fetched {len(self.batch_download_items)} items for download")
            self.root.after(0, self._update_single_quality_value)  # تصحيح استدعاء الدالة

        threading.Thread(target=fetch_qualities_thread, daemon=True).start()
    def remove_batch_url(self):
        """Remove selected URLs from the batch tree."""
        selected = self.batch_tree.selection()
        for item in selected:
            values = self.batch_tree.item(item, "values")
            url = values[0] if len(values[0]) <= 53 else values[0][:-3]  # Remove "..." if present
            if url in self.batch_urls:
                self.batch_urls.remove(url)
            if url in self.batch_formats_cache:
                del self.batch_formats_cache[url]
            if url in self.batch_quality_selections:
                del self.batch_quality_selections[url]
            self.batch_download_items = [di for di in self.batch_download_items if di['tree_item_id'] != item]
            self.batch_tree.delete(item)

    def clear_batch_urls(self):
        """Clear all URLs from the batch tree."""
        for item in self.batch_tree.get_children():
            self.batch_tree.delete(item)
        self.batch_urls = []
        self.batch_formats_cache = {}
        self.batch_quality_selections = {}
        self.batch_download_items = []
        self.batch_urls_text.delete("1.0", tk.END)
    def select_all_videos(self):
        for item in self.playlist_tree.get_children():
            self.playlist_tree.selection_add(item)

    def deselect_all_videos(self):
        for item in self.playlist_tree.get_children():
            self.playlist_tree.selection_remove(item)

    def select_single_quality(self):
        url = self.playlist_url_var.get().strip()
        if not url:
            messagebox.showerror("خطأ", self.translations[self.language]["no_url"])
            return
        self.fetch_qualities_for_playlist()



    def fetch_qualities_for_playlist(self):
        url = self.playlist_url_var.get().strip()
        if not url:
            messagebox.showerror("خطأ", self.translations[self.language]["no_url"])
            return

        # تحقق من وجود self.playlist_available_qualities
        if not hasattr(self, 'playlist_available_qualities'):
            print("خطأ: self.playlist_available_qualities غير معرف")
            messagebox.showerror("خطأ", "فشل تهيئة قائمة الجودات لقائمة التشغيل")
            return

        ydl_opts = {
            'quiet': True,
            'no_warnings': True,
            'extract_flat': True,
            'http_headers': {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
            }
        }

        def fetch_thread():
            try:
                with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                    info = ydl.extract_info(url, download=False)
                    if 'entries' not in info:
                        self.root.after(0, lambda: messagebox.showerror(
                            "خطأ", "الرابط ليس قائمة تشغيل صالحة"
                        ))
                        return
                    
                    # تنظيف الكاش
                    print(f"قبل التنظيف: self.playlist_available_qualities = {self.playlist_available_qualities}")
                    self.playlist_available_qualities.clear()
                    self.playlist_formats_cache.clear()
                    print(f"بعد التنظيف: self.playlist_available_qualities = {self.playlist_available_qualities}")

                    # إذا كانت الجودة الموحدة مفعلة، نجلب الجودات لفيديو واحد فقط
                    if self.use_single_quality_var.get():
                        # جلب أول فيديو فقط لتحديد الجودات الموحدة
                        first_entry = info['entries'][0] if info['entries'] else None
                        if not first_entry:
                            self.root.after(0, lambda: messagebox.showwarning(
                                "تحذير", "لم يتم العثور على فيديوهات في قائمة التشغيل"
                            ))
                            return

                        video_url = first_entry.get('url') or first_entry.get('webpage_url')
                        if not video_url:
                            self.root.after(0, lambda: messagebox.showwarning(
                                "تحذير", "فشل في جلب رابط الفيديو الأول"
                            ))
                            return

                        try:
                            ydl_opts['extract_flat'] = False
                            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                                video_info = ydl.extract_info(video_url, download=False)
                                formats = video_info.get('formats', [])
                                quality_list = []
                                self.playlist_formats_cache[video_url] = {}
                                self.playlist_available_qualities[video_url] = []
                                print(f"جلب التنسيقات لـ {video_url} (جودة موحدة), عدد التنسيقات: {len(formats)}")

                                for f in formats:
                                    resolution = f.get('height', None)
                                    ext = f.get('ext', 'N/A')
                                    if ext.lower() == 'webm' or not resolution:
                                        continue
                                    format_id = f.get('format_id')
                                    format_note = f.get('format_note', '')
                                    fps = f.get('fps', '')
                                    filesize = f.get('filesize', 0) or f.get('filesize_approx', 0)
                                    filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"
                                    description = f"{resolution}p {ext} ({format_note})" if format_note else f"{resolution}p {ext}"
                                    if fps:
                                        description += f" {fps}fps"
                                    quality_display = f"{description} - {filesize_mb:.2f} ميجا" if isinstance(filesize_mb, float) else f"{description} - {filesize_mb}"
                                    has_video = f.get('vcodec', 'none') != 'none'
                                    has_audio = f.get('acodec', 'none') != 'none'
                                    is_combined = has_video and has_audio
                                    quality_list.append(quality_display)
                                    self.playlist_formats_cache[video_url][quality_display] = (
                                        format_id, ext, filesize, format_note, is_combined
                                    )
                                    self.playlist_available_qualities[video_url].append(quality_display)

                                # ترتيب الجودات
                                quality_list.sort(key=lambda x: int(x.split('p')[0]) if 'p' in x and x.split('p')[0].isdigit() else 0)
                                self.playlist_available_qualities[video_url].sort(key=lambda x: int(x.split('p')[0]) if 'p' in x and x.split('p')[0].isdigit() else 0)
                                print(f"الجودات المتاحة لـ {video_url} (جودة موحدة): {self.playlist_available_qualities[video_url]}")

                        except Exception as e:
                            print(f"خطأ في جلب الجودات الموحدة لـ {video_url}: {e}")
                            self.root.after(0, lambda: messagebox.showerror(
                                "خطأ", f"فشل جلب الجودات الموحدة: {e}"
                            ))
                            return

                    # تحديث Combobox للجودة الموحدة
                    def update_combo():
                        print(f"تحديث Combobox: self.playlist_available_qualities = {self.playlist_available_qualities}")
                        if self.playlist_available_qualities:
                            first_url = next(iter(self.playlist_available_qualities))
                            quality_list = self.playlist_available_qualities[first_url]
                            print(f"تحديث self.quality_combo_playlist بالجودات: {quality_list}")
                            self.quality_combo_playlist.config(values=quality_list)
                            if quality_list:
                                self.quality_combo_playlist.current(0)
                                self._update_single_quality_value()
                                print(f"تم تعيين الجودة الافتراضية في Combobox: {self.quality_combo_playlist.get()}")
                            else:
                                messagebox.showwarning(
                                    "تحذير", "لم يتم العثور على جودات متاحة"
                                )
                        else:
                            messagebox.showwarning(
                                "تحذير", "لم يتم العثور على جودات متاحة لأي فيديو"
                            )

                    self.root.after(0, update_combo)

            except Exception as e:
                print(f"خطأ في جلب الجودات: {e}")
                self.root.after(0, lambda: messagebox.showerror(
                    "خطأ", f"فشل جلب الجودات: {e}"
                ))

        threading.Thread(target=fetch_thread, daemon=True).start()

    def fetch_individual_qualities(self):
        """Fetch individual qualities for each video in the playlist and create Combobox for quality selection."""
        if not self.playlist_videos:
            print("لا توجد فيديوهات لجلب الجودات لها")
            return

        ydl_opts = {
            'quiet': True,
            'no_warnings': True,
            'extract_flat': False,
            'http_headers': {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
            }
        }

        def fetch_thread():
            try:
                # تنظيف الكاش (للجودات المنفردة فقط)
                print(f"قبل التنظيف: self.playlist_available_qualities = {self.playlist_available_qualities}")
                self.playlist_available_qualities.clear()
                self.playlist_formats_cache.clear()
                print(f"بعد التنظيف: self.playlist_available_qualities = {self.playlist_available_qualities}")

                for video in self.playlist_videos:
                    video_url = video['url']
                    item_id = None
                    for item in self.playlist_tree.get_children():
                        values = self.playlist_tree.item(item)['values']
                        if int(values[0]) - 1 == self.playlist_videos.index(video):
                            item_id = item
                            break

                    try:
                        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                            video_info = ydl.extract_info(video_url, download=False)
                            formats = video_info.get('formats', [])
                            quality_list = []
                            self.playlist_formats_cache[video_url] = {}
                            self.playlist_available_qualities[video_url] = []
                            print(f"جلب التنسيقات لـ {video_url} (جودة منفردة), عدد التنسيقات: {len(formats)}")

                            for f in formats:
                                resolution = f.get('height', None)
                                ext = f.get('ext', 'N/A')
                                if ext.lower() == 'webm' or not resolution:
                                    continue
                                format_id = f.get('format_id')
                                format_note = f.get('format_note', '')
                                fps = f.get('fps', '')
                                filesize = f.get('filesize', 0) or f.get('filesize_approx', 0)
                                filesize_mb = filesize / (1024 * 1024) if filesize else "غير معروف"
                                description = f"{resolution}p {ext} ({format_note})" if format_note else f"{resolution}p {ext}"
                                if fps:
                                    description += f" {fps}fps"
                                quality_display = f"{description} - {filesize_mb:.2f} ميجا" if isinstance(filesize_mb, float) else f"{description} - {filesize_mb}"
                                has_video = f.get('vcodec', 'none') != 'none'
                                has_audio = f.get('acodec', 'none') != 'none'
                                is_combined = has_video and has_audio
                                quality_list.append(quality_display)
                                self.playlist_formats_cache[video_url][quality_display] = (
                                    format_id, ext, filesize, format_note, is_combined
                                )
                                self.playlist_available_qualities[video_url].append(quality_display)

                            # ترتيب الجودات
                            quality_list.sort(key=lambda x: int(x.split('p')[0]) if 'p' in x and x.split('p')[0].isdigit() else 0)
                            self.playlist_available_qualities[video_url].sort(key=lambda x: int(x.split('p')[0]) if 'p' in x and x.split('p')[0].isdigit() else 0)
                            print(f"الجودات المتاحة لـ {video_url} (جودة منفردة): {self.playlist_available_qualities[video_url]}")

                            default_quality = quality_list[0] if quality_list else "غير محدد"
                            video['selected_quality'] = default_quality
                            print(f"تم تعيين الجودة الافتراضية لـ {video_url}: {video['selected_quality']}")

                            # تحديث الجدول
                            if item_id:
                                values = self.playlist_tree.item(item_id)['values']
                                self.playlist_tree.item(item_id, values=(
                                    values[0],
                                    values[1],
                                    values[2],
                                    default_quality,
                                    values[4],
                                    values[5]
                                ))

                                # إنشاء Combobox للجودة
                                if quality_list and item_id:
                                    def create_combobox(attempt=0):
                                        self.playlist_tree.update_idletasks()
                                        bbox = self.playlist_tree.bbox(item_id, "#4")  # العمود الرابع (Quality)
                                        if not bbox or not all(bbox):
                                            if attempt < 5:
                                                self.root.after(500, lambda: create_combobox(attempt + 1))
                                                return
                                            print(f"فشل إنشاء Combobox لـ {video_url} بعد {attempt} محاولات")
                                            return

                                        x, y, width, height = bbox
                                        combo = ttk.Combobox(self.playlist_tree, values=quality_list, state="readonly", width=40)
                                        combo.set(default_quality)
                                        combo.place(x=x, y=y, width=width, height=height)
                                        combo.lift()
                                        self.combobox_widgets[item_id] = combo

                                        def on_select(event):
                                            new_quality = combo.get()
                                            if new_quality:
                                                video['selected_quality'] = new_quality
                                                values = self.playlist_tree.item(item_id)['values']
                                                self.playlist_tree.item(item_id, values=(
                                                    values[0],
                                                    values[1],
                                                    values[2],
                                                    new_quality,
                                                    values[4],
                                                    values[5]
                                                ))

                                        combo.bind("<<ComboboxSelected>>", on_select)

                                    self.root.after(500, create_combobox)

                    except Exception as e:
                        print(f"خطأ في جلب الجودات المنفردة لـ {video_url}: {e}")
                        self.root.after(0, lambda: messagebox.showwarning(
                            "تحذير", f"فشل جلب الجودات لـ {video_url}: {e}"
                        ))

            except Exception as e:
                print(f"خطأ عام في جلب الجودات المنفردة: {e}")
                self.root.after(0, lambda: messagebox.showerror(
                    "خطأ", f"فشل جلب الجودات المنفردة: {e}"
                ))

        threading.Thread(target=fetch_thread, daemon=True).start()
    def fetch_formats_for_url(self, url):
        """Fetch available formats for a URL and populate batch_formats_cache."""
        try:
            ydl_opts = {
                'format': 'bestvideo+bestaudio/best',
                'noplaylist': True,
                'quiet': True,
                'no_warnings': True,
                'no_m3u8': True,  # Skip HLS streams to prevent stalling
                'http_headers': {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
                },
                'socket_timeout': 30,
                'retries': 3,
                'fragment_retries': 3,
                'retry_sleep': 5
            }
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(url, download=False)
                formats = info.get('formats', [])
                self.batch_formats_cache[url] = {}
                if not formats:
                    logging.warning(f"No formats found for URL: {url}")
                    return
                for fmt in formats:
                    filesize = fmt.get('filesize') or fmt.get('filesize_approx', 0)
                    resolution = fmt.get('height', 'unknown')
                    ext = fmt.get('ext', 'mp4')
                    if not isinstance(resolution, int):
                        continue
                    quality_key = f"{resolution}p {ext}"
                    self.batch_formats_cache[url][quality_key] = (
                        fmt.get('format_id'),
                        ext,
                        filesize if filesize else 0,  # Ensure filesize is 0 if None
                        fmt.get('format_note', 'unknown'),
                        fmt.get('acodec') != 'none' and fmt.get('vcodec') != 'none'
                    )
                    logging.debug(f"Format added for {url}: {quality_key}, filesize: {filesize}")
        except yt_dlp.utils.DownloadError as e:
            logging.error(f"DownloadError fetching formats for {url}: {e}")
            raise
        except yt_dlp.utils.ExtractorError as e:
            logging.error(f"ExtractorError fetching formats for {url}: {e}")
            raise
        except Exception as e:
            logging.error(f"Unexpected error fetching formats for {url}: {type(e).__name__}: {e}")
            raise

    def _update_single_quality_value(self):
        """Update the single quality value from the playlist combobox."""
        self.single_quality_value = self.quality_combo_playlist.get()
    def update_overall_progress(self):
      if not hasattr(self, 'overall_progress_label'):
          return  # Skip if label isn't initialized yet
      completed_tasks = sum(1 for task in self.download_threads.values() if task['completed'])
      total = self.total_tasks
      if total > 0:
          progress = (completed_tasks / total) * 100
          self.overall_progress_label.config(text=f"التقدم الكلي: {progress:.2f}%")
      else:
          self.overall_progress_label.config(text="التقدم الكلي: 0.00%")

    def progress_hook(self, d, download_type):
        """Handle download progress updates for both combined and separate formats."""
        import logging
        import hashlib
        from tkinter import messagebox

        url = d['info_dict'].get('webpage_url', 'unknown')
        url_hash = hashlib.md5(url.encode('utf-8')).hexdigest()
        task_id = f"{download_type}_{url_hash}"
        logging.debug(f"Progress hook called for task: {task_id}, status: {d['status']}")

        try:
            if task_id not in self.download_threads:
                logging.warning(f"Task {task_id} not found in download_threads, skipping progress update")
                return

            filename = d.get('filename', '')
            if d['status'] == 'downloading':
                file_progress = 0.0
                total_bytes = d.get('total_bytes') or d.get('total_bytes_estimate') or 0
                downloaded_bytes = d.get('downloaded_bytes', 0)
                speed = (d.get('speed', 0) or 0) / 1024  # KB/s
                eta = d.get('eta', 0) or 0

                if total_bytes and total_bytes > 0:
                    file_progress = (downloaded_bytes / total_bytes) * 100
                    self.download_threads[task_id]['downloaded_bytes'] = downloaded_bytes
                    logging.debug(f"Progress: {file_progress:.1f}% ({downloaded_bytes}/{total_bytes} bytes)")
                else:
                    file_progress = 0.0
                    logging.debug("Total bytes unknown, setting progress to 0")

                if filename in self.download_windows:
                    window = self.download_windows[filename]
                    self.update_download_window(window, file_progress, speed, eta, f"{downloaded_bytes / 1024 / 1024:.2f} MB")

                self.pause_event.wait()
                if not self.pause_event.is_set():
                    raise Exception("Download paused")

            elif d['status'] == 'finished':
                logging.debug(f"Download finished for {task_id}")
                title = d['info_dict'].get('title', 'Unknown')

                self.download_threads[task_id]['completed'] = True
                self.download_threads[task_id]['filepath'] = filename
                file_size_bytes = os.path.getsize(filename) if os.path.exists(filename) else 0
                self.download_threads[task_id]['file_size'] = file_size_bytes / (1024 * 1024)

                self.update_stats(file_size_bytes, 1)
                self.cleanup_temp_files(filename)

                # عرض نافذة الإكمال
                completed_downloads = [{
                    'title': title,
                    'filesize_mb': file_size_bytes / (1024 * 1024),
                    'quality': self.download_threads[task_id].get('quality', 'N/A'),
                    'save_path': filename,
                    'download_time': time.time() - self.download_threads[task_id]['start_time'],
                    'ext': os.path.splitext(filename)[1][1:] if filename else 'mp4'
                }]
                self.root.after(0, lambda: self.show_completion_window(completed_downloads))

                if filename in self.download_windows:
                    if self.download_windows[filename].get('window') and self.download_windows[filename]['window'].winfo_exists():
                        self.download_windows[filename]['window'].destroy()
                        del self.download_windows[filename]

            elif d['status'] == 'error':
                logging.error(f"Download error for {task_id}: {d.get('error', 'Unknown error')}")
                title = d['info_dict'].get('title', 'Unknown')

                self.download_threads[task_id]['completed'] = False
                self.download_threads[task_id]['notified'] = True

                if filename in self.download_windows:
                    self.root.after(0, lambda: messagebox.showerror(
                        self.translations[self.language]["error"],
                        self.translations[self.language]["download_failed"].format(title)
                    ))
                    if self.download_windows[filename].get('window') and self.download_windows[filename]['window'].winfo_exists():
                        self.download_windows[filename]['window'].destroy()
                        del self.download_windows[filename]

        except Exception as e:
            logging.error(f"Unexpected error in progress_hook for {task_id}: {str(e)}")



    def cleanup_temp_files(self, filepath):
        if not filepath or not os.path.exists(filepath):
            logging.debug(f"لا يوجد ملف للتنظيف: {filepath}")
            return

        base_path = os.path.splitext(filepath)[0]
        temp_extensions = ['.part', '.fvideo.mp4', '.faudio.m4a', '.ytdl']  # أضفنا .ytdl لتغطية ملفات إضافية محتملة
        for ext in temp_extensions:
            temp_file = base_path + ext
            if os.path.exists(temp_file):
                try:
                    os.remove(temp_file)
                    logging.debug(f"تم حذف الملف المؤقت: {temp_file}")
                except Exception as e:
                    logging.error(f"فشل حذف الملف المؤقت {temp_file}: {e}")
            else:
                logging.debug(f"الملف المؤقت غير موجود: {temp_file}")

    def start_general_download(self):
        """بدء تنزيل عام للرابط المقدم مع تحسين اختيار التنسيق ومعالجة الأخطاء."""
        import logging
        import requests
        from tkinter import messagebox
        import yt_dlp
        import threading

        logging.basicConfig(level=logging.DEBUG)

        url = self.general_url_entry.get().strip()
        if not url:
            messagebox.showerror("خطأ", self.translations[self.language].get("no_url", "No URL provided"))
            logging.error("لم يتم تقديم رابط للتنزيل العام")
            return

        # التحقق مما إذا كان الرابط ملفًا مباشرًا
        is_direct_file = False
        content_type = None
        total_bytes = 0
        try:
            response = requests.head(url, headers={
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
            }, allow_redirects=True, timeout=5)
            response.raise_for_status()
            content_type = response.headers.get('content-type', '').lower()
            total_bytes = int(response.headers.get('content-length', 0))
            if content_type.startswith(('video/', 'audio/', 'application/octet-stream', 'application/pdf')):
                is_direct_file = True
                logging.debug(f"تم اكتشاف تنزيل ملف مباشر لـ {url}، نوع المحتوى: {content_type}")
        except Exception as e:
            logging.warning(f"تعذر تحديد نوع المحتوى لـ {url}: {str(e)}")

        if is_direct_file:
            self.download_general_file(url)
            return

        # التحقق مما إذا كان الرابط فيديو
        is_video = self.is_video_url(url)
        if not is_video:
            messagebox.showerror("خطأ", self.translations[self.language].get("invalid_url", "Invalid URL"))
            logging.error(f"الرابط ليس فيديو أو ملف مباشر معروف: {url}")
            return

        # إعداد خيارات yt_dlp
        ydl_opts = {
            'quiet': True,
            'noplaylist': True,
            'format': 'best',
            'extractor_args': {
                'okru': {'skip_auth': True}
            }
        }

        # التحقق مما إذا كان الفيديو يحتوي على تنسيقات متعددة
        has_multiple_formats = False
        formats = []
        info = None
        try:
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(url, download=False)
                formats = info.get('formats', [])
                has_multiple_formats = len([f for f in formats if f.get('vcodec') != 'none']) > 1
                logging.debug(f"الرابط {url}: has_multiple_formats={has_multiple_formats}, عدد التنسيقات={len(formats)}")
        except Exception as e:
            logging.error(f"تعذر استخراج معلومات التنسيق لـ {url}: {str(e)}")
            messagebox.showerror("خطأ", self.translations[self.language].get("invalid_url", "Invalid URL"))
            return

        # جلب نوع التنزيل
        download_type = self.download_type_combo.get()
        is_audio_only = download_type == self.translations[self.language]["audio_only"]
        include_subtitles = download_type == self.translations[self.language]["video_with_subtitles"]

        # تحذير المستخدم إذا تم اختيار الصوت فقط
        if is_audio_only:
            response = messagebox.askyesno(
                self.translations[self.language]["warning"],
                self.translations[self.language]["audio_only"] + ". هل تريد المتابعة أو تنزيل الفيديو؟",
                default="no"
            )
            if not response:
                is_audio_only = False
                logging.info("اختار المستخدم تنزيل الفيديو بدلاً من الصوت فقط")

        # إعداد التنزيل
        try:
            format_id = "best"
            ext = "mp4"
            is_combined = True
            filesize = info.get('filesize', 0) or 0
            clean_quality = "best"

            if has_multiple_formats:
                # جلب الجودة من القائمة المنسدلة
                quality = self.quality_combo.get()
                clean_quality = quality.split(' - ')[0].strip() if quality and ' - ' in quality else quality
                if not quality and self.formats_cache:
                    clean_quality = list(self.formats_cache.keys())[0]
                    logging.debug(f"لم يتم اختيار جودة، يتم الافتراض إلى: {clean_quality}")
                elif not quality:
                    clean_quality = "best"
                    logging.debug("لم يتم اختيار جودة، يتم الافتراض إلى 'best'")
                else:
                    logging.debug(f"الجودة المختارة: {clean_quality}")

                if clean_quality == "best":
                    format_id = "bestaudio[ext=m4a]" if is_audio_only else "bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]"
                    ext = "mp3" if is_audio_only else "mp4"
                    logging.debug(f"استخدام سلسلة التنسيق: {format_id}")
                elif clean_quality in self.formats_cache:
                    format_info = self.formats_cache[clean_quality]
                    format_id = format_info['format_id']
                    ext = format_info['ext']
                    filesize = format_info['filesize'] or filesize
                    is_combined = format_info['is_combined']
                    logging.debug(f"التنسيق المختار: format_id={format_id}, ext={ext}, is_combined={is_combined}")
                    if not is_combined and not self.ffmpeg_available:
                        messagebox.showwarning(
                            self.translations[self.language]["warning"],
                            self.translations[self.language]["ffmpeg_missing_warning"]
                        )
                        logging.warning("FFmpeg غير متاح، يتم الرجوع إلى أفضل تنسيق مدمج")
                        format_id = "bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]"
                        ext = "mp4"
                        is_combined = True
                    elif not is_combined and not is_audio_only:
                        format_id = f"{format_id}+bestaudio[ext=m4a]"
                        logging.debug(f"تنسيق غير مدمج، تم تعديل format_id ليشمل الصوت: {format_id}")
                else:
                    messagebox.showerror("خطأ", self.translations[self.language].get("no_qualities", "No qualities available"))
                    logging.error(f"الجودة المختارة غير موجودة في formats_cache: {clean_quality}")
                    return
            else:
                # فيديو بتنسيق واحد، استخدام الإعدادات الافتراضية
                format_id = "bestaudio[ext=m4a]" if is_audio_only else "best"
                ext = "mp3" if is_audio_only else "mp4"
                logging.debug(f"فيديو بتنسيق واحد، باستخدام التنسيق: {format_id}")

            # إنشاء نافذة التقدم
            total_bytes = filesize if filesize else 0
            filename = info.get('title', 'downloaded_video') + f".{ext}"
            window = self.create_download_window(url, total_bytes, filename)
            if not window:
                logging.error("فشل إنشاء نافذة التقدم")
                return
            self.download_windows[url] = window

            # إعداد خيط التنزيل
            url_hash = hashlib.md5(url.encode('utf-8')).hexdigest()
            task_id = f"general_{url_hash}"
            self.download_threads[task_id] = {
                'url': url,
                'completed': False,
                'is_batch': False,
                'downloaded_bytes': 0,
                'file_size': total_bytes,
                'filepath': None,
                'start_time': time.time(),
                'quality': clean_quality,
                'pause_event': threading.Event(),
                'pause': False,
                'cancel': False,
                'ratelimit': None
            }
            self.download_threads[task_id]['pause_event'].set()

            # بدء التنزيل
            self.download(
                url=url,
                is_batch=False,
                quality=clean_quality,
                filename=filename,
                format_id=format_id,
                ext=ext,
                is_combined=is_combined,
                is_general_download=True,
                is_audio=is_audio_only,
                subtitles=include_subtitles
            )

        except Exception as e:
            logging.error(f"خطأ أثناء بدء التنزيل لـ {url}: {str(e)}")
            messagebox.showerror("خطأ", f"فشل بدء التنزيل: {str(e)}")
            if url in self.download_windows:
                self.download_windows[url]['window'].destroy()
                del self.download_windows[url]

    def download_general_file(self, url):
        """تنزيل ملف عام (غير فيديو) مع نافذة تقدم متقدمة."""
        import requests
        import os
        import time
        import logging
        import hashlib
        import json
        from tkinter import messagebox
        from urllib.parse import urlparse
        import threading
        import traceback

        logging.basicConfig(level=logging.DEBUG)

        # تعريف ترجمات افتراضية إذا لم تكن موجودة
        default_translations = {
            'ar': {
                'speed': 'السرعة',
                'eta': 'الوقت المتبقي',
                'file_size': 'حجم الملف',
                'downloading': 'جاري التنزيل',
                'paused': 'متوقف مؤقتًا (سرعة منخفضة)',
                'starting_download': 'بدء التنزيل...',
                'file_name': 'اسم الملف',
                'save_path': 'مسار الحفظ',
                'cancel': 'إلغاء',
                'pause': 'إيقاف مؤقت',
                'resume': 'استئناف',
                'invalid_url': 'رابط غير صالح'
            },
            'en': {
                'speed': 'Speed',
                'eta': 'Time remaining',
                'file_size': 'File Size',
                'downloading': 'Downloading',
                'paused': 'Paused (Low Speed)',
                'starting_download': 'Starting download...',
                'file_name': 'File',
                'save_path': 'Path',
                'cancel': 'Cancel',
                'pause': 'Pause',
                'resume': 'Resume',
                'invalid_url': 'Invalid URL'
            }
        }

        # دمج الترجمات الافتراضية مع الحالية
        if not hasattr(self, 'translations'):
            self.translations = default_translations
        else:
            for lang in default_translations:
                if lang not in self.translations:
                    self.translations[lang] = default_translations[lang]
                else:
                    self.translations[lang].update(default_translations[lang])

        def update_ui(window, progress, speed, eta_text, downloaded_mb, total_size_mb):
            """تحديث واجهة نافذة التقدم بأمان."""
            try:
                if window['window'].winfo_exists():
                    speed_text = self.translations[self.language].get('speed', 'Speed')
                    eta_text_key = self.translations[self.language].get('eta', 'Time remaining')
                    file_size_text = self.translations[self.language].get('file_size', 'File Size')
                    
                    window['progress_bar'].configure(value=progress)
                    window['speed_label'].configure(text=f"{speed_text}: {speed:.2f} MB/s")
                    window['eta_label'].configure(text=f"{eta_text_key}: {eta_text}")
                    window['file_size_label'].configure(
                        text=f"{file_size_text}: {downloaded_mb:.2f}/{total_size_mb:.2f} MB"
                    )
                    window['status_label'].configure(
                        text=self.translations[self.language].get(
                            'paused' if self.download_threads[task_id]['pause'] else 'downloading',
                            'Paused (Low Speed)' if self.download_threads[task_id]['pause'] else 'Downloading'
                        )
                    )
                    self.root.update_idletasks()
                else:
                    logging.warning(f"نافذة التقدم لـ {url} لم تعد موجودة")
            except Exception as e:
                logging.error(f"خطأ أثناء تحديث الواجهة لـ {url}: {str(e)}\n{traceback.format_exc()}")

        try:
            self.paused = False
            self.cancelled = False

            # إنشاء مجلد مؤقت
            temp_dir = os.path.join(self.save_path, "temp_parts")
            os.makedirs(temp_dir, exist_ok=True)

            # جلب بيانات الملف
            response = requests.head(url, headers={
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
            }, allow_redirects=True)
            response.raise_for_status()

            filename = None
            if 'Content-Disposition' in response.headers:
                content_disposition = response.headers['Content-Disposition']
                if 'filename=' in content_disposition:
                    filename = content_disposition.split('filename=')[1].strip('"')
            if not filename:
                filename = os.path.basename(urlparse(url).path) or "downloaded_file"

            save_path = os.path.join(self.save_path, "others", filename)
            os.makedirs(os.path.dirname(save_path), exist_ok=True)

            total_size = int(response.headers.get('content-length', 0))
            total_size_mb = total_size / (1024 * 1024) if total_size > 0 else 0

            # التحقق من حالة التنزيل غير المكتمل
            state_file = os.path.join(temp_dir, f"{hashlib.md5(url.encode()).hexdigest()}.json")
            downloaded = 0
            part_count = 0
            if os.path.exists(state_file):
                try:
                    with open(state_file, 'r', encoding='utf-8') as f:
                        state = json.load(f)
                        downloaded = state['downloaded']
                        part_count = state['part_count']
                except Exception as e:
                    logging.error(f"فشل تحميل ملف الحالة {state_file}: {e}")

            # إنشاء نافذة التقدم
            window = self.create_download_window(url, total_size, filename)
            if not window:
                logging.error("فشل إنشاء نافذة التقدم")
                messagebox.showerror("خطأ", "فشل إنشاء نافذة التقدم")
                return
            self.download_windows[url] = window

            # إعداد خيط التنزيل
            url_hash = hashlib.md5(url.encode('utf-8')).hexdigest()
            task_id = f"general_{url_hash}"
            pause_event = threading.Event()
            pause_event.set()
            self.download_threads[task_id] = {
                'url': url,
                'completed': False,
                'is_batch': False,
                'downloaded_bytes': downloaded,
                'file_size': total_size,
                'filepath': save_path,
                'start_time': time.time(),
                'pause_event': pause_event,
                'pause': False,
                'cancel': False,
                'ratelimit': None
            }

            def download_task():
                nonlocal downloaded, part_count
                part_size = 1024 * 1024  # 1 ميجابايت أجزاء
                start_time = time.time()
                current_part_data = b""
                current_part_size = 0

                try:
                    while downloaded < total_size:
                        if self.download_threads[task_id]['cancel']:
                            logging.debug(f"تم إلغاء التنزيل لـ {url}")
                            self.log_history(url, "GeneralDownload", "Incomplete", "تم إلغاء التنزيل")
                            self.root.after(0, lambda: messagebox.showinfo("إلغاء", "تم إلغاء التنزيل"))
                            return

                        if self.download_threads[task_id]['pause']:
                            with open(state_file, 'w', encoding='utf-8') as f:
                                json.dump({
                                    'downloaded': downloaded,
                                    'part_count': part_count,
                                    'url': url,
                                    'save_path': save_path
                                }, f)
                            self.log_history(url, "GeneralDownload", "Incomplete", "تم إيقاف التنزيل مؤقتًا")
                            self.download_threads[task_id]['pause_event'].clear()
                            self.download_threads[task_id]['pause_event'].wait()
                            continue

                        headers = {
                            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
                            'Range': f'bytes={downloaded}-'
                        }
                        response = requests.get(url, stream=True, headers=headers, timeout=30)
                        response.raise_for_status()

                        chunk_start_time = time.time()
                        bytes_this_second = 0

                        for chunk in response.iter_content(chunk_size=8192):
                            if self.download_threads[task_id]['cancel']:
                                response.close()
                                logging.debug(f"تم إلغاء التنزيل لـ {url}")
                                self.log_history(url, "GeneralDownload", "Incomplete", "تم إلغاء التنزيل")
                                self.root.after(0, lambda: messagebox.showinfo("إلغاء", "تم إلغاء التنزيل"))
                                return

                            if self.download_threads[task_id]['pause']:
                                response.close()
                                with open(state_file, 'w', encoding='utf-8') as f:
                                    json.dump({
                                        'downloaded': downloaded,
                                        'part_count': part_count,
                                        'url': url,
                                        'save_path': save_path
                                    }, f)
                                self.log_history(url, "GeneralDownload", "Incomplete", "تم إيقاف التنزيل مؤقتًا")
                                self.download_threads[task_id]['pause_event'].clear()
                                self.download_threads[task_id]['pause_event'].wait()
                                break

                            if chunk:
                                chunk_size = len(chunk)
                                downloaded += chunk_size
                                current_part_data += chunk
                                current_part_size += chunk_size

                                # تطبيق ratelimit
                                ratelimit = self.download_threads[task_id].get('ratelimit')
                                if ratelimit is not None:
                                    bytes_this_second += chunk_size
                                    if bytes_this_second >= ratelimit:
                                        elapsed = time.time() - chunk_start_time
                                        if elapsed < 1:
                                            time.sleep(1 - elapsed)
                                        chunk_start_time = time.time()
                                        bytes_this_second = 0

                                if current_part_size >= part_size:
                                    part_file = os.path.join(temp_dir, f"{hashlib.md5(url.encode()).hexdigest()}_part_{part_count}")
                                    with open(part_file, 'wb') as f:
                                        f.write(current_part_data)
                                    part_count += 1
                                    current_part_data = b""
                                    current_part_size = 0

                                if total_size > 0:
                                    progress = (downloaded / total_size) * 100
                                    speed = downloaded / (time.time() - start_time) / (1024 * 1024)  # ميجابايت/ثانية
                                    eta = (total_size - downloaded) / (speed * 1024 * 1024) if speed > 0 else 0
                                    eta_text = (f"{int(eta // 60)} دقيقة" if self.language == "ar" else f"{int(eta // 60)} minutes") if eta >= 60 else \
                                               (f"{int(eta)} ثانية" if self.language == "ar" else f"{int(eta)} seconds")
                                    downloaded_mb = downloaded / (1024 * 1024)
                                    self.root.after(0, lambda: update_ui(window, progress, speed, eta_text, downloaded_mb, total_size_mb))

                        response.close()

                    if current_part_size > 0:
                        part_file = os.path.join(temp_dir, f"{hashlib.md5(url.encode()).hexdigest()}_part_{part_count}")
                        with open(part_file, 'wb') as f:
                            f.write(current_part_data)
                        part_count += 1

                    # دمج الأجزاء
                    with open(save_path, 'wb') as f:
                        for i in range(part_count):
                            part_file = os.path.join(temp_dir, f"{hashlib.md5(url.encode()).hexdigest()}_part_{i}")
                            if os.path.exists(part_file):
                                with open(part_file, 'rb') as pf:
                                    f.write(pf.read())

                    # التنظيف
                    self.cleanup_temp_files(temp_dir)
                    self.log_history(url, "GeneralDownload", "Success", f"تم تنزيل الملف إلى {save_path}")
                    self.update_stats(downloaded, 1)

                    # إظهار نافذة الاكتمال
                    completed_downloads = [{
                        'title': os.path.basename(save_path),
                        'filesize_mb': downloaded / (1024 * 1024),
                        'quality': 'N/A',
                        'save_path': save_path,
                        'download_time': time.time() - self.download_threads[task_id]['start_time'],
                        'ext': os.path.splitext(filename)[1][1:] or 'unknown'
                    }]
                    self.root.after(0, lambda: self.show_completion_window(completed_downloads))

                    # إغلاق نافذة التقدم
                    if url in self.download_windows and self.download_windows[url]['window'].winfo_exists():
                        self.download_windows[url]['window'].destroy()
                        del self.download_windows[url]

                    # تحديث تبويب التنزيلات غير المكتملة
                    if hasattr(self, 'incomplete_downloads') and isinstance(self.incomplete_downloads, (tk.Widget, ttk.Widget)):
                        self.root.after(0, lambda: self.update_incomplete_downloads())

                except Exception as e:
                    logging.error(f"خطأ في مهمة التنزيل لـ {url}: {str(e)}\n{traceback.format_exc()}")
                    self.log_history(url, "GeneralDownload", "Failed", str(e))
                    self.root.after(0, lambda: messagebox.showerror("خطأ", f"فشل تنزيل الملف: {str(e)}"))
                    if url in self.download_windows and self.download_windows[url]['window'].winfo_exists():
                        self.download_windows[url]['window'].destroy()
                        del self.download_windows[url]

            # بدء خيط التنزيل
            download_thread = threading.Thread(target=download_task, daemon=True)
            download_thread.start()
            self.download_threads[task_id]['thread'] = download_thread

        except Exception as e:
            logging.error(f"خطأ أثناء بدء التنزيل لـ {url}: {str(e)}\n{traceback.format_exc()}")
            self.log_history(url, "GeneralDownload", "Failed", str(e))
            messagebox.showerror("خطأ", f"فشل تنزيل الملف: {str(e)}")
            if url in self.download_windows and self.download_windows[url]['window'].winfo_exists():
                self.download_windows[url]['window'].destroy()
                del self.download_windows[url]
    def toggle_pause(self, pause_button, url, downloaded, part_count, temp_dir):
        """تبديل حالة الإيقاف المؤقت"""
        self.paused = not self.paused
        pause_button.config(text="استئناف" if self.paused else "إيقاف مؤقت")
        if not self.paused:
            # استئناف التنزيل
            self.download_general_file(url)

    def cancel_download(self, url, temp_dir):
        """إلغاء التنزيل"""
        self.cancelled = True
        if url in self.download_windows:
            self.download_windows[url]['window'].destroy()
            del self.download_windows[url]

    def cleanup_temp_files(self, temp_dir=None):
        """Remove temporary files and directories created during downloads."""
        import shutil
        import os
        import logging
        try:
            if not temp_dir:
                logging.debug("No temp_dir provided, skipping cleanup")
                return

            if not os.path.exists(temp_dir):
                logging.debug(f"Temp directory {temp_dir} does not exist, skipping cleanup")
                return

            # Check if the directory is still in use by active downloads
            active_downloads = any(
                thread.get('temp_filepath', '').startswith(temp_dir)
                for thread in self.download_threads.values()
            )
            if active_downloads:
                logging.debug(f"Temp directory {temp_dir} is still in use by active downloads, skipping cleanup")
                return

            logging.debug(f"Cleaning up temp directory: {temp_dir}")
            # Recursively delete the entire directory
            shutil.rmtree(temp_dir, ignore_errors=True)
            logging.debug(f"Successfully deleted temp directory: {temp_dir}")

        except PermissionError as e:
            logging.error(f"Permission denied while cleaning up {temp_dir}: {e}")
        except OSError as e:
            logging.error(f"OS error while cleaning up {temp_dir}: {e}")
        except Exception as e:
            logging.error(f"Unexpected error cleaning up {temp_dir}: {e}")
    def update_incomplete_downloads(self):
        """تحديث تبويب التحميلات غير المكتملة بناءً على self.download_threads وملفات الحالة"""
        import os
        import json
        import glob
        import tkinter as tk
        from tkinter import ttk
        import logging

        logging.basicConfig(level=logging.DEBUG)

        # Ensure self.incomplete_downloads is a Tkinter widget
        if not hasattr(self, 'incomplete_downloads') or not isinstance(self.incomplete_downloads, (tk.Widget, ttk.Widget)):
            # Assume self.tab_control exists for tabs; adjust if tab setup is different
            if hasattr(self, 'tab_control'):
                self.incomplete_downloads = ttk.LabelFrame(self.tab_control, text=self.translations[self.language]["incomplete_downloads"])
                self.tab_control.add(self.incomplete_downloads, text=self.translations[self.language]["incomplete_downloads"])
            else:
                self.incomplete_downloads = ttk.LabelFrame(self.root, text=self.translations[self.language]["incomplete_downloads"])
            logging.warning("self.incomplete_downloads was not a widget; initialized as LabelFrame")

        # إعداد مسار الأجزاء المؤقتة
        temp_dir = getattr(self, 'temp_parts_dir', os.path.join(self.save_path, "temp_parts"))
        if not os.path.exists(temp_dir):
            os.makedirs(temp_dir, exist_ok=True)

        # تنظيف المحتوى الحالي للتبويب
        try:
            for widget in self.incomplete_downloads.winfo_children():
                widget.destroy()
        except AttributeError as e:
            logging.error(f"Error accessing winfo_children: {e}")
            self.incomplete_downloads = ttk.LabelFrame(self.root, text=self.translations[self.language]["incomplete_downloads"])
            logging.warning("Re-initialized self.incomplete_downloads due to AttributeError")

        # جمع التحميلات غير المكتملة من self.download_threads
        incomplete_list = []
        for task_id, info in self.download_threads.items():
            if not info.get('completed', False):
                url = info.get('url')
                save_path = info.get('filepath') or os.path.join(self.save_path, f"{info.get('filename', 'Unknown')}.{info.get('ext', 'mp4')}")
                downloaded = info.get('downloaded_bytes', 0)
                total_size = info.get('file_size', 0) or self.get_file_size(url)
                status = info.get('status', 'downloading')
                filename = info.get('filename', os.path.basename(save_path))
                incomplete_list.append({
                    'task_id': task_id,
                    'url': url,
                    'save_path': save_path,
                    'downloaded': downloaded,
                    'total_size': total_size,
                    'status': status,
                    'filename': filename
                })

        # جمع التحميلات من ملفات الحالة (JSON)
        for state_file in glob.glob(os.path.join(temp_dir, "*.json")):
            try:
                with open(state_file, 'r') as f:
                    state = json.load(f)
                    url = state.get('url')
                    task_id = state.get('task_id', f"download_{hashlib.md5(url.encode('utf-8')).hexdigest()}")
                    # تجنب التكرار إذا التحميل موجود في self.download_threads
                    if task_id not in self.download_threads:
                        save_path = state.get('save_path')
                        downloaded = state.get('downloaded', 0)
                        total_size = self.get_file_size(url)
                        filename = os.path.basename(save_path)
                        incomplete_list.append({
                            'task_id': task_id,
                            'url': url,
                            'save_path': save_path,
                            'downloaded': downloaded,
                            'total_size': total_size,
                            'status': 'paused',
                            'filename': filename
                        })
            except Exception as e:
                logging.error(f"Error reading state file {state_file}: {e}")
                continue

        # إذا لم يكن هناك تنزيلات غير مكتملة
        if not incomplete_list:
            ttk.Label(
                self.incomplete_downloads,
                text=self.translations[self.language]["no_incomplete_downloads"],
                style="TLabel",
                font=("Segoe UI", 10)
            ).pack(pady=10)
            return

        # عرض التنزيلات غير المكتملة
        for item in incomplete_list:
            task_id = item['task_id']
            url = item['url']
            save_path = item['save_path']
            downloaded = item['downloaded']
            total_size = item['total_size']
            status = item['status']
            filename = item['filename']

            # إطار لكل تنزيل
            download_frame = ttk.Frame(self.incomplete_downloads)
            download_frame.pack(fill="x", padx=5, pady=2)

            # عرض معلومات التنزيل
            progress = (downloaded / total_size * 100) if total_size > 0 else 0
            info_label = ttk.Label(
                download_frame,
                text=f"{self.translations[self.language]['filename']}: {filename} | "
                     f"{self.translations[self.language]['progress']}: {progress:.1f}% | "
                     f"{self.translations[self.language]['status']}: {status.capitalize()} | "
                     f"{self.translations[self.language]['save_path']}: {save_path}",
                style="TLabel",
                font=("Segoe UI", 9),
                wraplength=600
            )
            info_label.pack(side="left", padx=5)

            # زر استئناف
            resume_button = ttk.Button(
                download_frame,
                text=self.translations[self.language]["resume_download"],
                command=lambda tid=task_id: self.resume_download(tid)
            )
            resume_button.pack(side="right", padx=5)

            # زر إلغاء
            cancel_button = ttk.Button(
                download_frame,
                text=self.translations[self.language]["cancel_download"],
                command=lambda u=url, tid=task_id: self.cancel_download(u, temp_dir, task_id=tid)
            )
            cancel_button.pack(side="right", padx=5)

        logging.debug("Updated Incomplete Downloads tab")
    def get_file_size(self, url):
        """الحصول على حجم الملف من الرابط"""
        try:
            response = requests.head(url, headers={
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
            })
            response.raise_for_status()
            return int(response.headers.get('content-length', 0))
        except:
            return 0

if __name__ == "__main__":
    root = tk.Tk()
    app = UltimateDownloaderPro(root)
    root.mainloop()