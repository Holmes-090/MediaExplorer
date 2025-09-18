import sys
import os
import json
import random
import cv2
import multiprocessing
import hashlib
import fitz
import shutil
import time
import gc
import vlc
import mediathumbgen
from pathlib import Path
from queue import Queue, Empty
from threading import Thread
from multiprocessing.pool import ThreadPool
from concurrent.futures import ThreadPoolExecutor, as_completed

os.environ["QT_QPA_PLATFORM_PLUGIN_PATH"] = os.path.join(os.path.dirname(__file__), "platforms")
os.environ["QT_PLUGIN_PATH"] = os.path.join(os.path.dirname(__file__), "mediaservice")
print("QT_PLUGIN_PATH =", os.environ["QT_PLUGIN_PATH"])
print("QT_QPA_PLATFORM_PLUGIN_PATH =", os.environ["QT_QPA_PLATFORM_PLUGIN_PATH"])

from PyQt5.QtWidgets import (
    QApplication,
    QWidget,
    QLabel,
    QVBoxLayout,
    QPushButton,
    QGridLayout,
    QScrollArea,
    QGraphicsScene,
    QGraphicsPixmapItem,
    QStyle,
    QHBoxLayout,
    QCheckBox,
    QFileDialog,
    QFrame,
    QDialog,
    QListWidget,
    QDialogButtonBox,
    QMessageBox,
    QMenu,
    QInputDialog,
    QSlider,
    QGraphicsView,
    QLineEdit,
    QSizePolicy,
    QToolButton,
    QSizePolicy,
    QLayout,
    QGraphicsOpacityEffect,
    QGraphicsDropShadowEffect,
    QShortcut,
    QAction,
    QActionGroup,
    QWidgetAction,
    QSpacerItem,
    QGraphicsRectItem,
    QGraphicsLineItem,
    QDesktopWidget,
    QButtonGroup,
    QRadioButton,
    QListView,
    QAbstractItemView,
    QStyledItemDelegate,
    QAbstractScrollArea,
    QGroupBox,
    QSplashScreen,
)
from PyQt5.QtGui import (
    QPixmap,
    QPainter,
    QColor,
    QMovie,
    QIcon,
    QImage,
    QFont,
    QPainterPath,
    QPolygon,
    QKeySequence,
    QPainter,
    QBrush,
    QPen,
    QGuiApplication,
    QFontMetrics,
    QCursor,
)
from PyQt5.QtCore import (
    Qt,
    QUrl,
    QSize,
    QTimer,
    QEvent,
    pyqtSignal,
    QObject,
    QRect,
    QPoint,
    QPropertyAnimation,
    QEasingCurve,
    QRectF,
    QPointF,
    QThread,
    QSettings,
    QAbstractListModel,
    QModelIndex,
    QVariant,
)
from PyQt5.QtMultimedia import QMediaPlayer, QMediaContent
from PyQt5.QtMultimediaWidgets import QVideoWidget
from PyQt5.Qt import QDesktopServices, QScroller
from PyQt5.QtPrintSupport import QPrinter, QPrintDialog
from PyQt5.QtSvg import QSvgRenderer


from pathlib import Path

THUMB_SIZE = 450


# -------------------------------------------------------------------------
# Improved safe_video_thumb with FFMPEG fallback
# -------------------------------------------------------------------------
def _safe_video_thumb_worker(path, q):
    """Standalone top-level worker function for multiprocessing"""
    try:
        import cv2

        cap = cv2.VideoCapture(path)
        if not cap.isOpened():
            q.put(None)
            return

        # Set a reasonable timeout for video operations
        cap.set(cv2.CAP_PROP_POS_FRAMES, 0)
        ret, frame = cap.read()
        cap.release()

        if ret:
            q.put(frame)
        else:
            q.put(None)
    except Exception:
        q.put(None)


class ThumbnailWorker(QObject):
    thumbnailReady = pyqtSignal(str, QIcon)
    workerError = pyqtSignal(str, str)  # path, error message

    def __init__(
        self,
        queue,
        stop_flag,
        show_tags=True,
        image_thumb_mode="zoom",
        max_retries=2,
        cleanup_interval=50,
        thumb_cache_dir=None,
    ):
        super().__init__()
        self.queue = queue
        self.stop_flag = stop_flag
        self.show_tags = show_tags
        self.image_thumb_mode = image_thumb_mode  # "zoom", "fit", or "stretch"
        self.max_retries = max_retries
        self.cleanup_interval = cleanup_interval
        self.processed_count = 0
        self.thumb_cache_dir = thumb_cache_dir

        # Setup cleanup timer
        self.cleanup_timer = QTimer()
        self.cleanup_timer.timeout.connect(self._cleanup_resources)
        self.cleanup_timer.start(5000)  # Clean up every 5 seconds

    def _wrap_centered_pixmap(self, pix: QPixmap) -> QPixmap:
        """Center the pixmap into a padded THUMB_SIZE square."""
        final_pix = QPixmap(THUMB_SIZE, THUMB_SIZE)
        final_pix.fill(Qt.transparent)
        painter = QPainter(final_pix)
        painter.setRenderHint(QPainter.SmoothPixmapTransform)
        x = (THUMB_SIZE - pix.width()) // 2 if pix.width() < THUMB_SIZE else 0
        y = (THUMB_SIZE - pix.height()) // 2 if pix.height() < THUMB_SIZE else 0
        painter.drawPixmap(x, y, pix)
        painter.end()
        return final_pix

    def run(self):
        """Main worker loop with improved error handling and resource management"""
        while not self.stop_flag[0]:
            try:
                path = self.queue.get(timeout=0.1)
            except Empty:
                continue
            except Exception:
                continue

            if not os.path.exists(path):
                self.queue.task_done()
                continue

            ext = os.path.splitext(path)[1].lower()

            thumb_path = os.path.normpath(
                os.path.join(
                    os.path.dirname(path),
                    ".thumbs",
                    os.path.splitext(os.path.basename(path))[0] + "_thumb.jpg",
                )
            ).replace("\\", "/")

            cache_file = self._thumb_cache_path(path)

            try:
                if ext in (
                    ".jpg",
                    ".jpeg",
                    ".png",
                    ".bmp",
                    ".webp",
                    ".mp4",
                    ".avi",
                    ".mov",
                    ".webm",
                    ".mkv",
                ):
                    pixmap = None
                    thumb_found = False

                    if os.path.exists(thumb_path):
                        try:
                            pixmap = QPixmap(thumb_path)
                            if not pixmap.isNull():
                                thumb_found = True
                                if (
                                    pixmap.width() < THUMB_SIZE // 2
                                    or pixmap.height() < THUMB_SIZE // 2
                                ):
                                    pixmap = None
                                    thumb_found = False
                            else:
                                pixmap = None
                        except Exception as e:
                            pixmap = None

                    if pixmap is None and cache_file.exists():
                        try:
                            pixmap = QPixmap(str(cache_file))
                            if not pixmap.isNull():
                                print(
                                    f"[ThumbnailWorker][DEBUG] Loaded from .thumbs_cache for {path}: {cache_file}"
                                )
                            else:
                                pixmap = None
                        except Exception as e:
                            pixmap = None

                    if pixmap is None:
                        if ext in (".jpg", ".jpeg", ".png", ".bmp", ".webp"):
                            try:
                                pixmap = QPixmap(path)
                                if pixmap.isNull():
                                    raise Exception("Failed to load image")
                            except Exception as e:
                                pixmap = None
                        elif ext in (".mp4", ".avi", ".mov", ".webm", ".mkv"):
                            frame = self._safe_video_thumb_with_fallback(path)
                            if frame is not None:
                                h, w, ch = frame.shape
                                bytesPerLine = 3 * w
                                qImg = QImage(
                                    frame.data, w, h, bytesPerLine, QImage.Format_RGB888
                                )
                                pixmap = QPixmap.fromImage(qImg)

                    if pixmap and not pixmap.isNull():
                        # ✅ Use selected thumbnail scaling mode
                        if self.image_thumb_mode == "zoom":
                            scaled = pixmap.scaled(
                                THUMB_SIZE,
                                THUMB_SIZE,
                                Qt.KeepAspectRatioByExpanding,
                                Qt.SmoothTransformation,
                            )
                        elif self.image_thumb_mode == "fit":
                            scaled = pixmap.scaled(
                                THUMB_SIZE,
                                THUMB_SIZE,
                                Qt.KeepAspectRatio,
                                Qt.SmoothTransformation,
                            )
                        elif self.image_thumb_mode == "stretch":
                            scaled = pixmap.scaled(
                                THUMB_SIZE,
                                THUMB_SIZE,
                                Qt.IgnoreAspectRatio,
                                Qt.SmoothTransformation,
                            )
                        else:
                            # Default to zoom
                            scaled = pixmap.scaled(
                                THUMB_SIZE,
                                THUMB_SIZE,
                                Qt.KeepAspectRatioByExpanding,
                                Qt.SmoothTransformation,
                            )

                        icon = QIcon(self._wrap_centered_pixmap(scaled))

                        if thumb_found and not cache_file.exists():
                            scaled.save(str(cache_file), "JPG")
                    else:
                        icon = self._create_fallback_icon(path, ext)

                elif ext == ".gif":
                    try:
                        movie = QMovie(path)
                        movie.setCacheMode(QMovie.CacheAll)
                        movie.start()
                        movie.jumpToFrame(0)
                        pixmap = movie.currentPixmap()
                        if not pixmap.isNull():
                            scaled = self._wrap_centered_pixmap(
                                pixmap.scaled(
                                    THUMB_SIZE,
                                    THUMB_SIZE,
                                    Qt.KeepAspectRatioByExpanding,
                                    Qt.SmoothTransformation,
                                )
                            )
                            icon = QIcon(scaled)
                            if not cache_file.exists():
                                scaled.save(str(cache_file), "JPG")
                        else:
                            icon = self._create_fallback_icon(path, ext)
                    except Exception as e:
                        icon = self._create_fallback_icon(path, ext)

                elif ext == ".pdf":
                    try:
                        import fitz

                        doc = fitz.open(path)
                        page = doc.load_page(0)
                        zoom = THUMB_SIZE / max(page.rect.width, page.rect.height)
                        mat = fitz.Matrix(zoom, zoom)
                        pix = page.get_pixmap(matrix=mat, alpha=False)
                        qImg = QImage(
                            pix.samples,
                            pix.width,
                            pix.height,
                            pix.stride,
                            QImage.Format_RGB888,
                        )
                        pixmap = QPixmap.fromImage(qImg)
                        doc.close()

                        if not pixmap.isNull():
                            scaled = self._wrap_centered_pixmap(pixmap)
                            icon = QIcon(scaled)
                            if not cache_file.exists():
                                scaled.save(str(cache_file), "JPG")
                        else:
                            icon = self._create_fallback_icon(path, ext)
                    except Exception as e:
                        icon = self._create_fallback_icon(path, ext)

                else:
                    icon = self._create_fallback_icon(path, ext)

            except Exception as e:
                icon = self._create_fallback_icon(path, ext)

            # Emit result
            if not icon.isNull():
                self.thumbnailReady.emit(path, icon)
            else:
                icon = self._create_fallback_icon(path, ext)
                self.thumbnailReady.emit(path, icon)

            self.queue.task_done()
            self.processed_count += 1

    def _cleanup_resources(self):
        """Clean up zombie processes and force garbage collection"""
        # Force garbage collection periodically
        if self.processed_count % self.cleanup_interval == 0:
            gc.collect()

    def _safe_video_thumb_with_fallback(self, path, timeout=2.0):
        """Extract video thumbnail with proper color conversion"""
        frame = None

        try:
            cap = cv2.VideoCapture(path)
            if cap.isOpened():
                # Try to seek to a frame that's more likely to have content
                frame_count = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
                if frame_count > 10:
                    cap.set(cv2.CAP_PROP_POS_FRAMES, min(10, frame_count // 4))

                ret, frame = cap.read()
                if ret:
                    # Convert BGR to RGB
                    frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                cap.release()
        except Exception as e:
            print(f"[ThumbnailWorker] Video processing error for {path}: {e}")
            frame = None

        return frame

    def _create_fallback_icon(self, path, ext):
        """Create a fallback icon for files that can't be processed"""
        fallback_pix = QPixmap(THUMB_SIZE, THUMB_SIZE)
        fallback_pix.fill(QColor(64, 64, 64))

        painter = QPainter(fallback_pix)
        painter.setRenderHint(QPainter.Antialiasing)

        # Draw file type badge
        badge = QRect(4, 4, THUMB_SIZE - 8, 20)
        painter.fillRect(badge, QColor(100, 100, 100, 180))

        font = QFont()
        font.setBold(True)
        font.setPointSize(10)
        painter.setFont(font)
        painter.setPen(Qt.white)

        label = ext.upper().replace(".", "") if ext else "FILE"
        painter.drawText(badge, Qt.AlignCenter, label)
        painter.end()

        return QIcon(fallback_pix)

    def cleanup(self):
        """Clean up resources when worker is stopped"""
        self.cleanup_timer.stop()
        gc.collect()

    def _thumb_cache_path(self, path: str) -> Path:
        import hashlib
        from pathlib import Path

        h = hashlib.md5(path.encode("utf-8")).hexdigest()
        return Path(self.thumb_cache_dir) / f"{h}_hq.jpg"


class FolderLoader(QObject):
    """Handles folder loading with robust cache validation"""

    folderLoadStarted = pyqtSignal(str)  # folder_path
    folderLoadProgress = pyqtSignal(int, int)  # current, total
    folderLoadCompleted = pyqtSignal(str, list)  # folder_path, file_list
    thumbnailReady = pyqtSignal(str, QIcon)  # file_path, icon

    def __init__(self, cache_manager, thumbnail_worker):
        super().__init__()
        self.cache_manager = cache_manager
        self.thumbnail_worker = thumbnail_worker
        self.current_folder = None
        self.is_loading = False
        self.stop_loading = False
        self.loaded_thumbnails = {}  # path → QIcon

        # Connect thumbnail worker signals
        self.thumbnail_worker.thumbnailReady.connect(self._on_thumbnail_generated)

    def load_folder(self, folder_path, file_extensions=None):
        """Load folder with cache validation and progressive loading"""
        if self.is_loading:
            self.stop_loading = True
            self.loaded_thumbnails.clear()
            return

        self.current_folder = folder_path
        self.is_loading = True
        self.stop_loading = False

        if file_extensions is None:
            file_extensions = {
                ".jpg",
                ".jpeg",
                ".png",
                ".gif",
                ".bmp",
                ".webp",
                ".mp4",
                ".avi",
                ".mov",
                ".webm",
                ".mkv",
                ".pdf",
            }

        try:
            from mediathumbgen import generate_thumbnails

            generate_thumbnails(str(folder_path))
        except Exception as e:
            print(f"[C++ Thumbnail Module] Failed to generate thumbnails: {e}")

            # Get all files in folder
            all_files = []
            folder_path = Path(folder_path)

            if not folder_path.exists():
                self.folderLoadCompleted.emit(str(folder_path), [])
                return

            # Collect files
            for file_path in folder_path.iterdir():
                if file_path.is_file() and file_path.suffix.lower() in file_extensions:
                    all_files.append(str(file_path))

            all_files.sort()  # Sort for consistent ordering

            self.folderLoadStarted.emit(str(folder_path))

            # Phase 1: Load cached thumbnails immediately
            cached_count = 0
            uncached_files = []

            for i, file_path in enumerate(all_files):
                if self.stop_loading:
                    break

                self.folderLoadProgress.emit(i, len(all_files))

                # Check cache first
                if self.cache_manager.has_thumbnail(file_path):
                    cached_icon = self.cache_manager.get_cached_thumbnail(file_path)
                    if cached_icon and not cached_icon.isNull():
                        self.thumbnailReady.emit(file_path, cached_icon)
                        cached_count += 1
                        continue

                # File needs processing
                uncached_files.append(file_path)

            print(
                f"[FolderLoader] Loaded {cached_count} cached thumbnails, {len(uncached_files)} need processing"
            )

            # Phase 2: Queue uncached files for processing
            if not self.stop_loading and uncached_files:
                self._queue_files_for_processing(uncached_files)

            self.folderLoadCompleted.emit(str(folder_path), all_files)

        except Exception as e:
            print(f"[FolderLoader] Error loading folder {folder_path}: {e}")
            self.folderLoadCompleted.emit(str(folder_path), [])
        finally:
            self.is_loading = False

    def _queue_files_for_processing(self, files):
        """Queue files for thumbnail processing in batches"""
        try:
            # Add files to processing queue in small batches
            batch_size = 10
            for i in range(0, len(files), batch_size):
                if self.stop_loading:
                    break

                batch = files[i : i + batch_size]
                for file_path in batch:
                    if not self.stop_loading:
                        self.thumbnail_worker.queue.put(file_path)

                # Small delay between batches to prevent overwhelming
                time.sleep(0.01)

        except Exception as e:
            print(f"[FolderLoader] Error queuing files: {e}")

    def _on_thumbnail_generated(self, file_path, icon):
        """Handle thumbnail generated by worker"""
        if not icon.isNull():
            # Save to cache
            self.cache_manager.save_thumbnail(file_path, icon)
            self.loaded_thumbnails[file_path] = icon

            # Emit if this is for current folder
            if self.current_folder and file_path.startswith(self.current_folder):
                self.thumbnailReady.emit(file_path, icon)

    def stop_current_load(self):
        """Stop current loading operation"""
        self.stop_loading = True
        self.is_loading = False

    def validate_current_folder_cache(self):
        """Validate cache for current folder and clear if needed"""
        if not self.current_folder:
            return

        try:
            folder_path = Path(self.current_folder)
            if not folder_path.exists():
                return

            # Check if cache validation is needed
            stats = self.cache_manager.get_cache_stats()
            if stats.get("corrupt_files", 0) > 10:  # Too many corrupt files
                print(
                    f"[FolderLoader] Cache has {stats['corrupt_files']} corrupt files, clearing..."
                )
                self.cache_manager.clear_cache()
                return True

            return False

        except Exception as e:
            print(f"[FolderLoader] Cache validation error: {e}")
            return False


class SmoothListView(QListView):
    def wheelEvent(self, event):
        # Get existing scrollbar
        scrollbar = self.verticalScrollBar()
        # Scroll smaller steps than default
        delta = event.angleDelta().y() / 120  # each notch is 120
        scrollbar.setValue(scrollbar.value() - int(delta * 30))  # 30 px per notch


class SmartFolderManager(QObject):
    """High-level folder manager that handles the entire loading process"""

    folderChanged = pyqtSignal(str)
    loadingProgress = pyqtSignal(int, int)
    thumbnailReady = pyqtSignal(str, QIcon)

    def __init__(self, cache_manager, thumbnail_worker):
        super().__init__()
        self.cache_manager = cache_manager
        self.thumbnail_worker = thumbnail_worker
        self.folder_loader = FolderLoader(cache_manager, thumbnail_worker)
        self.current_folder = None
        self.loading_timer = QTimer()
        self.loading_timer.timeout.connect(self._check_loading_status)

        # Connect signals
        self.folder_loader.folderLoadStarted.connect(self._on_folder_load_started)
        self.folder_loader.folderLoadProgress.connect(self.loadingProgress)
        self.folder_loader.folderLoadCompleted.connect(self._on_folder_load_completed)
        self.folder_loader.thumbnailReady.connect(self.thumbnailReady)

    def change_folder(self, folder_path):
        """Change to a new folder with smart cache handling"""
        if self.current_folder == folder_path:
            return

        # Stop any current loading
        self.folder_loader.stop_current_load()

        # Clear thumbnail worker queue
        try:
            while not self.thumbnail_worker.queue.empty():
                self.thumbnail_worker.queue.get_nowait()
                self.thumbnail_worker.queue.task_done()
        except:
            pass

        # Validate cache for problematic folders
        if self._is_problematic_folder(folder_path):
            print(
                f"[SmartFolderManager] Detected problematic folder, validating cache..."
            )
            if self.folder_loader.validate_current_folder_cache():
                print(f"[SmartFolderManager] Cache cleared for problematic folder")

        self.current_folder = folder_path
        self.folderChanged.emit(folder_path)

        # Start loading
        self.folder_loader.load_folder(folder_path)
        self.loading_timer.start(100)  # Check loading status every 100ms

    def _is_problematic_folder(self, folder_path):
        """Check if folder is likely to be problematic"""
        try:
            folder_path = Path(folder_path)
            if not folder_path.exists():
                return False

            # Check folder size
            total_size = 0
            file_count = 0
            for file_path in folder_path.iterdir():
                if file_path.is_file():
                    try:
                        total_size += file_path.stat().st_size
                        file_count += 1
                        if file_count > 1000:  # Stop counting after 1000 files
                            break
                    except:
                        continue

            # Problematic if > 10GB or > 500 files
            return total_size > 10 * 1024 * 1024 * 1024 or file_count > 500

        except:
            return False

    def _on_folder_load_started(self, folder_path):
        """Handle folder load started"""
        print(f"[SmartFolderManager] Started loading folder: {folder_path}")

    def _on_folder_load_completed(self, folder_path, file_list):
        """Handle folder load completed"""
        print(
            f"[SmartFolderManager] Completed loading folder: {folder_path} ({len(file_list)} files)"
        )
        self.loading_timer.stop()

    def _check_loading_status(self):
        """Check if loading is taking too long"""
        if not self.folder_loader.is_loading:
            self.loading_timer.stop()
            return

        # If loading takes more than 30 seconds, something might be wrong
        # This is handled by the individual timeout mechanisms
        pass

    def get_cache_stats(self):
        """Get cache statistics"""
        return self.cache_manager.get_cache_stats()

    def clear_cache(self):
        """Clear the entire cache"""
        self.cache_manager.clear_cache()

    def cleanup(self):
        """Cleanup resources"""
        self.folder_loader.stop_current_load()
        self.loading_timer.stop()
        self.cache_manager.finalize()

    def get_loaded_thumbnails(self):
        return dict(self.folder_loader.loaded_thumbnails)
    

class ClickableSmoothListView(SmoothListView):
    heartClicked = pyqtSignal(QModelIndex)

    def mousePressEvent(self, event):
        index = self.indexAt(event.pos())
        if not index.isValid():
            return super().mousePressEvent(event)

        item_data = index.data(Qt.UserRole)
        if not item_data:
            return super().mousePressEvent(event)

        path, icon, is_favorite, is_folder = item_data

        # Determine the item's display rectangle
        item_rect = self.visualRect(index)

        # Calculate heart icon area (same as drawn in delegate)
        heart_rect = QRect(
            item_rect.right() - 36, item_rect.top() + 4,
            32, 32
        )

        if heart_rect.contains(event.pos()):
            self.heartClicked.emit(index)
            return  # Don't trigger normal click

        super().mousePressEvent(event)

# -----------------------------------------------------------------------------
# Clickable slider (video seekbar)
# -----------------------------------------------------------------------------
class ClickableSlider(QSlider):
    def mousePressEvent(self, event):
        if event.button() == Qt.LeftButton:
            val = QStyle.sliderValueFromPosition(
                self.minimum(), self.maximum(), event.pos().x(), self.width()
            )
            self.setValue(val)
            self.sliderMoved.emit(val)
            event.accept()
        super().mousePressEvent(event)


# -----------------------------------------------------------------------------
# Single vs double click button
# -----------------------------------------------------------------------------
class ThumbnailButton(QPushButton):
    def __init__(self, path, click_handler, dblclick_handler):
        super().__init__()
        self._path = path
        self._click = click_handler
        self._dbl = dblclick_handler

    def mouseReleaseEvent(self, e):
        if e.button() == Qt.LeftButton:
            QTimer.singleShot(QApplication.doubleClickInterval(), self._maybe_handle)
        super().mouseReleaseEvent(e)

    def _maybe_handle(self):
        if not getattr(self, "_dbl_clicked", False):
            self._click(self._path)
        self._dbl_clicked = False

    def mouseDoubleClickEvent(self, e):
        if e.button() == Qt.LeftButton:
            self._dbl_clicked = True
            self._dbl(self._path)
        super().mouseDoubleClickEvent(e)


# -----------------------------------------------------------------------------
# Zoomable/scrollable graphics view
# -----------------------------------------------------------------------------
class ZoomableGraphicsView(QGraphicsView):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setDragMode(QGraphicsView.ScrollHandDrag)
        self.setTransformationAnchor(QGraphicsView.AnchorUnderMouse)
        self.setResizeAnchor(QGraphicsView.AnchorUnderMouse)
        self.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.setMouseTracking(True)

    def wheelEvent(self, e):
        f = 1.1 if e.angleDelta().y() > 0 else 0.9
        self.scale(f, f)

    def keyPressEvent(self, e):
        # Let QShortcut system handle it first
        if not self.parent():
            super().keyPressEvent(e)
        else:
            QApplication.sendEvent(self.parent(), e)

    def mousePressEvent(self, e):
        if e.button() == Qt.RightButton:
            self.parent().mousePressEvent(e)
        else:
            super().mousePressEvent(e)


# -----------------------------------------------------------------------------
# Animated-GIF thumbnail widget
# -----------------------------------------------------------------------------
class AnimatedGifItem(QLabel):
    def __init__(self, path):
        super().__init__()
        self.setFixedSize(THUMB_SIZE, THUMB_SIZE)
        movie = QMovie(path)
        movie.setCacheMode(QMovie.CacheAll)
        movie.setScaledSize(QSize(THUMB_SIZE, THUMB_SIZE))
        self.setMovie(movie)
        movie.jumpToFrame(0)
        movie.start()


# -----------------------------------------------------------------------------
# Flow Style Layout
# -----------------------------------------------------------------------------
class FlowLayout(QLayout):
    def __init__(self, parent=None, margin=0, spacing=6):
        super().__init__(parent)
        self.setContentsMargins(margin, margin, margin, margin)
        self.setSpacing(spacing)
        self.itemList = []

    def addItem(self, item):
        self.itemList.append(item)

    def count(self):
        return len(self.itemList)

    def itemAt(self, idx):
        return self.itemList[idx] if idx < len(self.itemList) else None

    def takeAt(self, idx):
        return self.itemList.pop(idx) if idx < len(self.itemList) else None

    def expandingDirections(self):
        return Qt.Orientations(Qt.Orientation(0))

    def hasHeightForWidth(self):
        return True

    def heightForWidth(self, width):
        if not self.itemList:
            return 0
        height = self.doLayout(QRect(0, 0, width, 0), testOnly=True)
        return height

    def setGeometry(self, rect):
        super().setGeometry(rect)
        self.doLayout(rect, testOnly=False)

    def sizeHint(self):
        return self.minimumSize()

    def minimumSize(self):
        size = QSize()
        for item in self.itemList:
            size = size.expandedTo(item.minimumSize())
        return size + QSize(
            2 * self.contentsMargins().top(), 2 * self.contentsMargins().top()
        )

    def doLayout(self, rect, testOnly):
        if not self.itemList:
            return 0

        item_width = self.itemList[0].widget().width() if self.itemList else 0
        item_height = self.itemList[0].widget().height() if self.itemList else 0
        spacing = self.spacing()
        max_items_per_row = max(1, (rect.width() + spacing) // (item_width + spacing))

        # Calculate the left margin for centered full rows
        full_row_width = (
            max_items_per_row * item_width + (max_items_per_row - 1) * spacing
        )
        available_width = rect.width()
        left_margin = rect.x() + (available_width - full_row_width) // 2

        # Group items into rows
        lines = []
        current_line = []
        for item in self.itemList:
            current_line.append(item)
            if len(current_line) == max_items_per_row:
                lines.append(current_line)
                current_line = []
        if current_line:
            lines.append(current_line)

        total_height = 0
        for i, line_items in enumerate(lines):
            is_last_row = i == len(lines) - 1
            line_count = len(line_items)
            line_width = line_count * item_width + (line_count - 1) * spacing
            if not is_last_row and line_count == max_items_per_row:
                # Center full rows
                start_x = left_margin
            elif is_last_row and line_count < max_items_per_row:
                # Left-align last incomplete row with the left edge of centered rows
                start_x = left_margin
            else:
                # Center any other row (shouldn't happen, but for safety)
                start_x = rect.x() + (available_width - line_width) // 2
            x = start_x
            for item in line_items:
                if not testOnly:
                    item.setGeometry(
                        QRect(QPoint(x, total_height + rect.y()), item.widget().size())
                    )
                x += item_width + spacing
            total_height += item_height + spacing
        return total_height - spacing


# -----------------------------------------------------------------------------
# Custom ToolButton Class
# -----------------------------------------------------------------------------
class HoverToolButton(QToolButton):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setStyleSheet(
            """
            QToolButton {
                font-size: 9pt;
                text-align: center;
                padding-top: 6px;
                padding-bottom: 2px;
            }
            QToolButton::menu-indicator {
                subcontrol-position: bottom center;
                subcontrol-origin: padding;
            }
        """
        )
        self.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
        self.setMinimumHeight(72)  # Ensure consistent height

    def setText(self, text):
        super().setText(text)
        # Force layout update after text change
        self.setToolButtonStyle(Qt.ToolButtonIconOnly)
        self.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)

    def enterEvent(self, event):
        super().enterEvent(event)
        # Force layout update on hover
        self.setToolButtonStyle(Qt.ToolButtonIconOnly)
        self.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)

    def leaveEvent(self, event):
        super().leaveEvent(event)
        # Force layout update when leaving
        self.setToolButtonStyle(Qt.ToolButtonIconOnly)
        self.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)


# -----------------------------------------------------------------------------
# Fullscreen viewer (images, GIFs, videos) with slideshow
# -----------------------------------------------------------------------------
class FullscreenImageViewer(QWidget):
    def __init__(
        self,
        media_path,
        pdf_path,
        media_list,
        slideshowInterval=None,
        randomize=False,
        toggle_slideshow_callback=None,
        close_callback=None,
    ):
        super().__init__()

        self.path = media_path
        self.media_path = media_path
        self._close_callback = close_callback
        self.media_list = media_list
        self.randomize = randomize
        self.interval = slideshowInterval
        self.slideshowTimer = None
        self.page_index = 0
        self._is_closing = False
        self._vlc_cleanup_done = False
        
        # Navigation control to prevent freezing
        self._navigating = False
        self._navigation_pending = None
        self._navigation_timer = QTimer()
        self._navigation_timer.setSingleShot(True)
        self._navigation_timer.timeout.connect(self._process_pending_navigation)
        
        # Track if video is supposed to be looping
        self._should_loop = True
        self._loop_timer = QTimer()
        self._loop_timer.setSingleShot(True)
        self._loop_timer.timeout.connect(self._check_and_restart_video)

        # Set fullscreen window flags
        self.setWindowFlags(Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint)
        self.setAttribute(Qt.WA_DeleteOnClose)
        self.setFocusPolicy(Qt.StrongFocus)
        self.setCursor(Qt.ArrowCursor)
        self.setStyleSheet("background-color: black;")

        try:
            self.idx = media_list.index(media_path)
        except ValueError:
            self.idx = 0
        
        # Main layout
        outer_layout = QVBoxLayout(self)
        outer_layout.setContentsMargins(0, 0, 0, 0)
        outer_layout.setSpacing(0)

        self.media_container = QWidget(self)
        self.media_layout = QVBoxLayout(self.media_container)
        self.media_layout.setContentsMargins(0, 0, 0, 0)
        self.media_layout.setSpacing(0)
        outer_layout.addWidget(self.media_container)

        # Mini-menu setup
        self._setup_mini_menu()

        # Create VLC instance with optimized settings
        vlc_args = [
            '--intf', 'dummy',
            '--no-video-title-show',
            '--file-caching=1000',  # Increased for stability
            '--network-caching=1000',
            '--no-audio-time-stretch',
            '--avcodec-fast',
            '--no-spu',
            '--quiet',
            '--no-disable-screensaver',
            '--no-snapshot-preview',
        ]
        
        self.instance = vlc.Instance(vlc_args)
        self.vlc_player = self.instance.media_player_new()

        # Video Container with Controls
        self._setup_video_controls()

        # Navigation buttons
        self._setup_navigation()

        # Timers
        self._setup_timers()

        # Event handling
        self._setup_event_handling()

        # Load initial media
        self.load_media(media_path)

        # Position elements after a short delay
        QTimer.singleShot(100, self._position_elements)

        self.setMouseTracking(True)
        self.media_container.setMouseTracking(True)

    def _setup_mini_menu(self):
        """Setup mini menu components"""
        # Mini-menu arrow
        self._mini_arrow = QToolButton(self)
        self._mini_arrow.setArrowType(Qt.LeftArrow)
        self._mini_arrow.setStyleSheet("background: rgba(30,30,30,220); border: none; border-radius: 4px;")
        self._mini_arrow.setFixedSize(40, 40)

        # Mini-menu container
        self._mini_menu = QFrame(self)
        self._mini_menu_layout = QVBoxLayout(self._mini_menu)
        self._mini_menu_layout.setContentsMargins(8, 8, 8, 8)
        self._mini_menu_layout.setSpacing(10)
        self._mini_menu.setStyleSheet(
            """
            QFrame {
                background-color: rgba(30, 30, 30, 200);
                border-radius: 12px;
                border: 1px solid rgba(255,255,255,0.15);
            }
        """
        )
        self._mini_menu.setFixedSize(150, 200)
        self._mini_menu.hide()

        # Shadow effect for mini menu
        shadow = QGraphicsDropShadowEffect(self)
        shadow.setBlurRadius(20)
        shadow.setXOffset(0)
        shadow.setYOffset(4)
        shadow.setColor(QColor(0, 0, 0, 160))
        self._mini_menu.setGraphicsEffect(shadow)

        # Slide animation
        self._mini_anim = QPropertyAnimation(self._mini_menu, b"pos", self)
        self._mini_anim.setDuration(200)
        self._mini_anim.setEasingCurve(QEasingCurve.InOutQuad)
        self._mini_open = False

        self._mini_arrow.clicked.connect(self._toggle_mini_menu)

        # File label
        self._file_label = QLabel(os.path.basename(self.path), self._mini_menu)
        self._file_label.setAlignment(Qt.AlignCenter)
        self._file_label.setWordWrap(True)
        self._file_label.setStyleSheet(
            """
            QLabel {
                color: white;
                font-weight: bold;
                font-size: 8pt;
                padding: 2px;
            }
        """
        )
        self._mini_menu_layout.insertWidget(0, self._file_label)

        # Add buttons to mini menu
        self._setup_mini_menu_buttons()

    def _setup_mini_menu_buttons(self):
        """Setup mini menu buttons"""
        # Slideshow button
        self._slideshow_btn = QToolButton(self._mini_menu)
        self._slideshow_btn.setText("Slideshow")
        self._slideshow_btn.setStyleSheet(self._get_button_style())
        self._slideshow_btn.clicked.connect(self.start_stop_slideshow)
        self._mini_menu_layout.addWidget(self._slideshow_btn)

        # Random button
        self.rand_btn = QToolButton(self._mini_menu)
        self.rand_btn.setText("Random")
        self.rand_btn.setCheckable(True)
        self.rand_btn.setChecked(self.randomize)
        self.rand_btn.setStyleSheet(self._get_button_style())
        self.rand_btn.toggled.connect(self._toggle_random_mode)
        self._mini_menu_layout.addWidget(self.rand_btn)

        # Print button
        self._print_btn = QToolButton(self._mini_menu)
        self._print_btn.setText("Print")
        self._print_btn.setStyleSheet(self._get_button_style())
        self._print_btn.clicked.connect(self._print_current)
        self._mini_menu_layout.addWidget(self._print_btn)

        # Delete File button (only for static images)
        ext = os.path.splitext(self.path)[1].lower()
        if ext in [".jpg", ".jpeg", ".png", ".bmp", ".webp"]:
            delete_file_btn = QPushButton("Delete File")
            delete_file_btn.setStyleSheet(
                """
                QPushButton {
                    color: white; 
                    background-color: #d32f2f; 
                    border: none;
                    border-radius: 4px; 
                    padding: 6px;
                    font-weight: bold;
                }
                QPushButton:hover {
                    background-color: #f44336;
                }
                """
            )
            delete_file_btn.clicked.connect(self._confirm_delete_file)
            self._mini_menu_layout.addWidget(delete_file_btn)

        self._mini_menu_layout.addStretch()

    def _setup_video_controls(self):
        """Setup video container and controls"""
        self.video_container = QWidget(self)
        video_layout = QVBoxLayout(self.video_container)
        video_layout.setContentsMargins(0, 0, 0, 0)
        video_layout.setSpacing(0)

        # Video display widget
        self.video_display = QWidget(self.video_container)
        self.video_display.setStyleSheet("background-color: black;")
        self.video_container.setMouseTracking(True)
        self.video_display.setMouseTracking(True)
        video_layout.addWidget(self.video_display, 1)

        # Set VLC window
        if sys.platform.startswith("linux"):
            self.vlc_player.set_xwindow(self.video_display.winId())
        elif sys.platform == "win32":
            self.vlc_player.set_hwnd(self.video_display.winId())
        elif sys.platform == "darwin":
            self.vlc_player.set_nsobject(int(self.video_display.winId()))

        # Video controls
        self.video_controls = QWidget(self.video_container)
        self.video_controls.setStyleSheet(
            """
            QWidget {
                background-color: rgba(0, 0, 0, 200);
                border-radius: 8px;
            }
            QPushButton {
                background-color: rgba(255, 255, 255, 30);
                border: 1px solid rgba(255, 255, 255, 50);
                border-radius: 6px;
                color: white;
                padding: 8px;
            }
            QPushButton:hover {
                background-color: rgba(255, 255, 255, 50);
            }
            QPushButton:pressed {
                background-color: rgba(255, 255, 255, 20);
            }
        """
        )
        self.video_controls.setFixedHeight(70)

        controls_layout = QHBoxLayout(self.video_controls)
        controls_layout.setContentsMargins(15, 10, 15, 10)
        controls_layout.setSpacing(15)

        # Play/Pause button
        self.play_btn = QPushButton()
        self.play_btn.setIcon(self._create_white_icon(QStyle.SP_MediaPlay))
        self.play_btn.setFixedSize(50, 50)
        self.play_btn.clicked.connect(self._toggle_play_vlc)
        controls_layout.addWidget(self.play_btn)

        # Seek slider
        self.slider = QSlider(Qt.Horizontal)
        self.slider.setRange(0, 0)
        self.slider.setStyleSheet("""
            QSlider::groove:horizontal {
                border: 1px solid rgba(255, 255, 255, 100);
                height: 6px;
                background: rgba(255, 255, 255, 50);
                margin: 2px 0;
                border-radius: 3px;
            }
            QSlider::handle:horizontal {
                background: white;
                border: 2px solid rgba(0, 0, 0, 100);
                width: 16px;
                margin: -6px 0;
                border-radius: 8px;
            }
            QSlider::handle:horizontal:hover {
                background: #e0e0e0;
            }
        """)
        self._slider_pressed = False
        self.slider.sliderPressed.connect(self._on_slider_pressed)
        self.slider.sliderReleased.connect(self._on_slider_released)
        self.slider.sliderMoved.connect(self._on_slider_moved)
        self.slider.mousePressEvent = self._slider_mouse_press
        controls_layout.addWidget(self.slider, 1)

        # Mute button
        self.mute_btn = QPushButton()
        self.mute_btn.setIcon(self._create_white_icon(QStyle.SP_MediaVolume))
        self.mute_btn.setFixedSize(50, 50)
        self.mute_btn.clicked.connect(self._toggle_mute_vlc)
        controls_layout.addWidget(self.mute_btn)

        # Volume slider
        self.volume_slider = QSlider(Qt.Horizontal)
        self.volume_slider.setRange(0, 100)
        self.volume_slider.setValue(50)
        self.volume_slider.setFixedWidth(100)
        self.volume_slider.setStyleSheet(self.slider.styleSheet())
        self.volume_slider.valueChanged.connect(self._set_volume_vlc)
        controls_layout.addWidget(self.volume_slider)

        video_layout.addWidget(self.video_controls)
        self.media_layout.addWidget(self.video_container)
        self.video_container.hide()

    def _setup_navigation(self):
        """Setup navigation buttons"""
        self.left_nav_btn = QToolButton(self)
        self.left_nav_btn.setText("◀")
        self.left_nav_btn.setFixedSize(60, 60)
        self.left_nav_btn.setCursor(Qt.PointingHandCursor)
        self.left_nav_btn.clicked.connect(self._prev)
        
        self.right_nav_btn = QToolButton(self)
        self.right_nav_btn.setText("▶")
        self.right_nav_btn.setFixedSize(60, 60)
        self.right_nav_btn.setCursor(Qt.PointingHandCursor)
        self.right_nav_btn.clicked.connect(lambda: self._advance(1))

        nav_style = """
            QToolButton {
                background-color: rgba(0, 0, 0, 150);
                border: 2px solid rgba(255, 255, 255, 100);
                color: white;
                font-size: 20px;
                font-weight: bold;
                border-radius: 30px;
            }
            QToolButton:hover {
                background-color: rgba(255, 255, 255, 100);
                color: black;
            }
            QToolButton:pressed {
                background-color: rgba(255, 255, 255, 150);
            }
        """
        
        for btn in [self.left_nav_btn, self.right_nav_btn]:
            btn.setStyleSheet(nav_style)

    def _setup_timers(self):
        """Setup all timers"""
        # Hide/show controls timer
        self.hide_timer = QTimer(self)
        self.hide_timer.setSingleShot(True)
        self.hide_timer.setInterval(3000)
        self.hide_timer.timeout.connect(self._hide_video_controls)

        # Navigation controls auto-hide timer
        self.nav_hide_timer = QTimer(self)
        self.nav_hide_timer.setSingleShot(True)
        self.nav_hide_timer.setInterval(3000)
        self.nav_hide_timer.timeout.connect(self._hide_navigation_controls)

        # Cursor hide timer
        self.cursor_hide_timer = QTimer(self)
        self.cursor_hide_timer.setSingleShot(True)
        self.cursor_hide_timer.setInterval(3000)
        self.cursor_hide_timer.timeout.connect(lambda: self.setCursor(Qt.BlankCursor))

        # VLC position update timer
        self._vlc_timer = QTimer(self)
        self._vlc_timer.timeout.connect(self._update_vlc_slider)
        self._vlc_timer.start(500)

        # Cursor polling timer
        self._last_cursor_pos = QCursor.pos()
        self._cursor_poll = QTimer(self)
        self._cursor_poll.setInterval(120)
        self._cursor_poll.timeout.connect(self._poll_cursor_activity)
        self._cursor_poll.start()

    def _setup_event_handling(self):
        """Setup event filters and VLC events"""
        # Install event filters
        self.video_display.installEventFilter(self)
        self.video_container.installEventFilter(self)
        self.installEventFilter(self)
        if QApplication.instance() is not None:
            QApplication.instance().installEventFilter(self)

        # Setup VLC event manager (will be attached when video loads)
        self.vlc_events = None

        # Enable mouse tracking
        try:
            self.setAttribute(Qt.WA_Hover, True)
            self.video_container.setMouseTracking(True)
            self.video_display.setMouseTracking(True)
            self.video_container.setAttribute(Qt.WA_Hover, True)
            self.video_display.setAttribute(Qt.WA_Hover, True)
            self.video_display.setAttribute(Qt.WA_MouseTracking, True)
            self.video_display.setFocusPolicy(Qt.StrongFocus)
        except Exception:
            pass

    def load_media(self, path):
        """Load images, GIFs, PDFs, or videos into the viewer."""
        # Stop any pending navigation
        if self._navigating:
            self._navigation_pending = path
            return
        
        # Clean up current media
        self._cleanup_current_media()

        # Hide all existing widgets first
        for i in range(self.media_layout.count()):
            w = self.media_layout.itemAt(i).widget()
            if w:
                w.hide()

        ext = os.path.splitext(path)[1].lower()
        self.setWindowTitle(os.path.basename(path))
        self.path = path
        self._update_file_label()

        if ext == ".gif":
            self._load_gif(path)
        elif ext in (".mp4", ".avi", ".mov", ".webm", ".mkv", ".flv"):
            self._load_video(path)
        elif ext == ".pdf":
            self._load_pdf(path)
        else:
            self._load_image(path)

        # Start slideshow if interval is set
        if self.interval:
            self.slideshowTimer = QTimer(self)
            self.slideshowTimer.setSingleShot(True)
            self.slideshowTimer.timeout.connect(self._advance_slideshow)
            self.slideshowTimer.start(self.interval)

    def _cleanup_current_media(self):
        """Properly cleanup current media before loading new one"""
        # Stop looping
        self._should_loop = False
        if hasattr(self, '_loop_timer'):
            self._loop_timer.stop()
        
        # Stop VLC player
        if hasattr(self, "vlc_player") and self.vlc_player and not self._vlc_cleanup_done:
            try:
                # Detach events first
                if hasattr(self, 'vlc_events') and self.vlc_events:
                    try:
                        self.vlc_events.event_detach(vlc.EventType.MediaPlayerEndReached)
                    except:
                        pass
                    self.vlc_events = None
                
                # Stop playback
                if self.vlc_player.is_playing():
                    self.vlc_player.stop()
                
                # Clear media
                self.vlc_player.set_media(None)
                
                # Process events
                for _ in range(3):
                    QApplication.processEvents()
            except Exception as e:
                print(f"Warning during VLC cleanup: {e}")

        # Stop GIF animation
        if hasattr(self, "movie") and self.movie:
            try:
                self.movie.stop()
                self.movie = None
            except:
                pass

        # Stop slideshow timer
        if hasattr(self, "slideshowTimer") and self.slideshowTimer:
            try:
                self.slideshowTimer.stop()
                self.slideshowTimer = None
            except:
                pass

    def contextMenuEvent(self, event):
        """Override default context menu on right-click to exit fullscreen"""
        if not self._is_closing:
            event.accept()
            self._safe_exit()
        else:
            super().contextMenuEvent(event)

    def _load_video(self, path):
        """Load video with improved stability and looping"""
        self.video_container.show()
        self._should_loop = True
        
        try:
            # Ensure clean state
            if self.vlc_player:
                self.vlc_player.stop()
                QApplication.processEvents()
            
            # Create media with optimizations
            media = self.instance.media_new(path)
            
            # Add options for better performance
            media.add_option(":file-caching=1000")
            media.add_option(":no-audio-time-stretch")
            media.add_option(":avcodec-fast")
            media.add_option(":input-repeat=65535")  # Enable VLC-level looping as backup
            
            # Set media
            self.vlc_player.set_media(media)
            self.vlc_player.audio_set_volume(self.volume_slider.value())
            
            # Reattach VLC events for looping
            self._reattach_vlc_events()
            
            # Start playback
            self.vlc_player.play()
            
            # Update UI
            self.play_btn.setIcon(self._create_white_icon(QStyle.SP_MediaPause))
            self.slider.setValue(0)
            self.slider.setRange(0, 0)
            
            # Show controls and start timers
            QTimer.singleShot(100, self._show_video_controls)
            QTimer.singleShot(200, self._show_all_controls)
            
            # Start position update timer
            if hasattr(self, '_vlc_timer'):
                self._vlc_timer.start(500)
            
            # Start loop check timer for short videos
            self._start_loop_checker()
            
        except Exception as e:
            print(f"Error loading video: {e}")
            error_label = QLabel(f"Error loading video:\n{str(e)}")
            error_label.setStyleSheet("color: white; font-size: 16px; padding: 20px;")
            error_label.setAlignment(Qt.AlignCenter)
            self.media_layout.addWidget(error_label)
            error_label.show()

    def _start_loop_checker(self):
        """Start a timer to periodically check if video needs restarting"""
        if hasattr(self, '_loop_timer'):
            self._loop_timer.stop()
            self._loop_timer.start(100)  # Check every 100ms

    def _check_and_restart_video(self):
        """Check if video has ended and restart if needed"""
        if not self._should_loop or self._is_closing or not self.vlc_player:
            return
        
        try:
            # Check if video has ended
            state = self.vlc_player.get_state()
            if state == vlc.State.Ended:
                # Get video length to determine restart strategy
                length = self.vlc_player.get_length()
                
                if length and length < 3000:  # Less than 3 seconds
                    # Immediate restart for very short videos
                    self.vlc_player.set_position(0.0)
                    self.vlc_player.play()
                else:
                    # Normal restart
                    self.vlc_player.set_position(0.0)
                    QTimer.singleShot(50, lambda: self.vlc_player.play() if self._should_loop else None)
            
            # Continue checking if we should be looping
            if self._should_loop and not self._is_closing:
                self._loop_timer.start(100)
                
        except Exception as e:
            print(f"Error in loop checker: {e}")

    def _start_video_playback(self):
        """Start video playback with safety checks"""
        if not self._is_closing and hasattr(self, 'vlc_player') and self.vlc_player:
            try:
                self.vlc_player.play()
                # Restart the VLC timer for seek bar updates
                if hasattr(self, '_vlc_timer') and self._vlc_timer:
                    self._vlc_timer.start(500)
            except Exception as e:
                print(f"Error starting video playback: {e}")

    def _restart_vlc_timer(self):
        """Restart VLC timer for seek bar updates"""
        if not self._is_closing and hasattr(self, '_vlc_timer') and self._vlc_timer:
            try:
                self._vlc_timer.stop()
                self._vlc_timer.start(500)
            except Exception as e:
                print(f"Error restarting VLC timer: {e}")

    def _reattach_vlc_events(self):
        """Reattach VLC events for video looping"""
        if not self._is_closing and hasattr(self, 'vlc_player') and self.vlc_player:
            try:
                # Detach existing events first
                if hasattr(self, 'vlc_events') and self.vlc_events:
                    try:
                        self.vlc_events.event_detach(vlc.EventType.MediaPlayerEndReached)
                    except Exception:
                        pass
                
                # Create new event manager and attach events
                self.vlc_events = self.vlc_player.event_manager()
                self.vlc_events.event_attach(vlc.EventType.MediaPlayerEndReached, self._on_video_end)
                print("VLC events reattached for looping")
            except Exception as e:
                print(f"Error reattaching VLC events: {e}")
                self.vlc_events = None

    def _load_gif(self, path):
        """Load GIF animation"""
        self.movie = QMovie(path)
        self.movie.setCacheMode(QMovie.CacheAll)
        self.view = ZoomableGraphicsView(self)
        scene = QGraphicsScene(self.view)
        self.item = QGraphicsPixmapItem(self.movie.currentPixmap())
        scene.addItem(self.item)
        self.view.setScene(scene)
        self.view.setBackgroundBrush(Qt.black)
        self.media_layout.addWidget(self.view)
        self.view.show()

        self.movie.frameChanged.connect(self._update_gif_frame)
        self.movie.start()

    def _load_image(self, path):
        """Load static image"""
        try:
            self.view = ZoomableGraphicsView(self)
            scene = QGraphicsScene(self.view)
            pix = QPixmap(path)
            if pix.isNull():
                raise Exception("Invalid image file")
            self.item = QGraphicsPixmapItem(pix)
            scene.addItem(self.item)
            self.view.setScene(scene)
            self.view.setBackgroundBrush(Qt.black)
            self.media_layout.addWidget(self.view)
            self.view.show()
            QTimer.singleShot(50, lambda: self.view.fitInView(self.item, Qt.KeepAspectRatio))
        except Exception as e:
            error_label = QLabel(f"Error loading image:\n{str(e)}")
            error_label.setStyleSheet("color: white; font-size: 16px; padding: 20px;")
            error_label.setAlignment(Qt.AlignCenter)
            self.media_layout.addWidget(error_label)
            error_label.show()

    def _load_pdf(self, path):
        """Load PDF file"""
        try:
            import fitz
            self.doc = fitz.open(path)
            self.page_index = 0

            self.view = ZoomableGraphicsView(self)
            self.scene = QGraphicsScene(self.view)
            self.pix_item = QGraphicsPixmapItem()
            self.scene.addItem(self.pix_item)
            self.view.setScene(self.scene)
            self.view.setBackgroundBrush(Qt.black)

            self.media_layout.addWidget(self.view)
            self.view.show()

            # Page number label
            self._page_label = QLabel(self)
            self._page_label.setStyleSheet(
                """
                QLabel {
                    color: white;
                    background-color: rgba(0, 0, 0, 180);
                    padding: 8px 16px;
                    border-radius: 8px;
                    font-weight: bold;
                    font-size: 14px;
                    border: 1px solid rgba(255, 255, 255, 50);
                }
            """
            )
            self._page_label.setAlignment(Qt.AlignCenter)
            self._page_label.show()
            self._page_label.raise_()

            QTimer.singleShot(50, lambda: self.show_page(self.page_index))
        except Exception as e:
            err = QLabel(f"Unable to display PDF:\n{e}")
            err.setStyleSheet("color: white; padding: 12px; font-size: 14px;")
            err.setAlignment(Qt.AlignCenter)
            self.media_layout.addWidget(err)
            err.show()

    # ─── FIXED: Enhanced VLC cleanup methods ───
    def _cleanup_vlc(self):
        """Comprehensive VLC cleanup"""
        if self._vlc_cleanup_done:
            return
            
        try:
            # Stop looping
            self._should_loop = False
            if hasattr(self, '_loop_timer'):
                self._loop_timer.stop()
            
            # Disconnect VLC events
            if hasattr(self, 'vlc_events') and self.vlc_events:
                try:
                    self.vlc_events.event_detach(vlc.EventType.MediaPlayerEndReached)
                except:
                    pass
                self.vlc_events = None

            # Stop and clean up player
            if hasattr(self, 'vlc_player') and self.vlc_player:
                try:
                    if self.vlc_player.is_playing():
                        self.vlc_player.stop()
                    
                    QApplication.processEvents()
                    
                    self.vlc_player.set_media(None)
                    self.vlc_player.release()
                    self.vlc_player = None
                    
                except Exception as e:
                    print(f"Warning during VLC player cleanup: {e}")

            # Release instance
            if hasattr(self, 'instance') and self.instance:
                try:
                    self.instance.release()
                    self.instance = None
                except Exception as e:
                    print(f"Warning during VLC instance cleanup: {e}")

            self._vlc_cleanup_done = True
            
        except Exception as e:
            print(f"Error in VLC cleanup: {e}")
            self._vlc_cleanup_done = True


    def _safe_exit(self):
        """Safely exit with cleanup"""
        if self._is_closing:
            return
            
        self._is_closing = True
        self._should_loop = False
        
        try:
            # Stop all timers
            timers_to_stop = [
                '_vlc_timer', 'hide_timer', 'nav_hide_timer', 
                'cursor_hide_timer', '_cursor_poll', 'slideshowTimer',
                '_mini_anim', '_loop_timer', '_navigation_timer'
            ]
            
            for timer_name in timers_to_stop:
                timer = getattr(self, timer_name, None)
                if timer and hasattr(timer, 'stop'):
                    try:
                        timer.stop()
                    except:
                        pass

            # Clean up VLC
            self._cleanup_vlc()

            # Stop GIFs
            if hasattr(self, "movie") and self.movie:
                try:
                    self.movie.stop()
                except:
                    pass

            # Call callback
            if hasattr(self, '_close_callback') and self._close_callback:
                try:
                    self._close_callback()
                except:
                    pass

            # Close window
            self.hide()
            self.close()

        except Exception as e:
            print(f"Error during safe exit: {e}")
            self.close()

    def _force_exit(self):
        """Force immediate exit"""
        self._safe_exit()  # Use the same comprehensive cleanup

    def closeEvent(self, event):
        """Handle close event"""
        if not self._is_closing:
            self._is_closing = True
            
        self._should_loop = False
        self._cleanup_vlc()
        
        super().closeEvent(event)

    # ─── VLC Event Handlers ───
    def _on_video_end(self, event):
        """Handle video end event for looping"""
        print("Video end event triggered - attempting to loop")
        if not self._should_loop or self._is_closing:
            print("Video end event ignored - not looping or closing")
            return
        
        try:
            # Get video length
            length = self.vlc_player.get_length() if self.vlc_player else 0
            print(f"Video length: {length}ms")
            
            # Use appropriate restart method based on video length
            if length and length < 3000:  # Very short video
                print("Using immediate restart for very short video")
                # Immediate restart
                self.vlc_player.set_position(0.0)
                self.vlc_player.play()
            elif length and length < 5000:  # Short video
                print("Using immediate restart for short video")
                self._restart_video_immediate()
            else:
                print("Using delayed restart for longer video")
                # Small delay for stability
                QTimer.singleShot(100, self._restart_video)
                
        except Exception as e:
            print(f"Error in video end handler: {e}")

    def _restart_video_ultra_fast(self):
        """Ultra-fast restart for very short videos (2-3 seconds)"""
        print("Attempting ultra-fast video restart")
        if not self._is_closing and hasattr(self, 'vlc_player') and self.vlc_player:
            try:
                # For ultra-short videos, use the most aggressive restart possible
                self.vlc_player.set_position(0.0)
                # Use processEvents to ensure position is set immediately
                QApplication.processEvents()
                self.vlc_player.play()
                print("Ultra-fast restart completed")
            except Exception as e:
                print(f"Error in ultra-fast video restart: {e}")
        else:
            print("Ultra-fast restart skipped - closing or no VLC player")

    def _restart_video_immediate(self):
        """Immediate restart for short videos"""
        print("Attempting immediate video restart")
        if not self._is_closing and hasattr(self, 'vlc_player') and self.vlc_player:
            try:
                self.vlc_player.set_position(0.0)
                self.vlc_player.play()
                print("Immediate restart completed")
            except Exception as e:
                print(f"Error in immediate video restart: {e}")
        else:
            print("Immediate restart skipped - closing or no VLC player")

    def _restart_video(self):
        """Restart video playback"""
        print("Attempting delayed video restart")
        if not self._should_loop or self._is_closing or not self.vlc_player:
            print("Delayed restart skipped - not looping, closing, or no VLC player")
            return
        
        try:
            self.vlc_player.set_position(0.0)
            self.vlc_player.play()
            print("Delayed restart completed")
        except Exception as e:
            print(f"Error restarting video: {e}")

    # ─── VLC Control Methods ───
    def _toggle_play_vlc(self):
        if not self._is_closing and self.vlc_player:
            try:
                if self.vlc_player.is_playing():
                    self.vlc_player.pause()
                    self.play_btn.setIcon(self._create_white_icon(QStyle.SP_MediaPlay))
                else:
                    self.vlc_player.play()
                    self.play_btn.setIcon(self._create_white_icon(QStyle.SP_MediaPause))
            except Exception as e:
                print(f"Error toggling play: {e}")

    def _toggle_mute_vlc(self):
        if not self._is_closing and self.vlc_player:
            try:
                muted = self.vlc_player.audio_get_mute()
                self.vlc_player.audio_set_mute(not muted)
                
                if not muted:  # Will be muted after toggle
                    self.mute_btn.setIcon(self._create_white_icon(QStyle.SP_MediaVolumeMuted))
                else:  # Will be unmuted after toggle
                    self.mute_btn.setIcon(self._create_white_icon(QStyle.SP_MediaVolume))
            except Exception as e:
                print(f"Error toggling mute: {e}")

    def _set_volume_vlc(self, val):
        if not self._is_closing and self.vlc_player:
            try:
                self.vlc_player.audio_set_volume(val)
            except Exception as e:
                print(f"Error setting volume: {e}")

    def _update_vlc_slider(self):
        """Update slider position - with safety checks"""
        if (not self._is_closing and self.vlc_player and 
            not self._slider_pressed and self.video_container.isVisible()):
            try:
                if self.vlc_player.is_playing():
                    length = self.vlc_player.get_length()
                    pos = self.vlc_player.get_time()
                    
                    if length > 0:
                        if self.slider.maximum() != length:
                            self.slider.setMaximum(length)
                        if abs(self.slider.value() - pos) > 500:
                            self.slider.setValue(pos)
            except Exception:
                pass  # Ignore VLC errors during playback

    def _on_slider_pressed(self):
        """Called when user starts dragging the slider"""
        self._slider_pressed = True

    def _on_slider_released(self):
        """Called when user releases the slider"""
        self._slider_pressed = False

    def _on_slider_moved(self, position):
        """Called when user moves the slider"""
        if self._slider_pressed and not self._is_closing and self.vlc_player:
            try:
                self.vlc_player.set_time(position)
            except Exception as e:
                print(f"Error seeking: {e}")

    def _slider_mouse_press(self, event):
        """Handle mouse press on slider for click-to-seek"""
        if event.button() == Qt.LeftButton and not self._is_closing:
            slider_range = self.slider.maximum() - self.slider.minimum()
            if slider_range > 0:
                click_pos = event.x()
                slider_width = self.slider.width()
                
                new_value = self.slider.minimum() + (click_pos / slider_width) * slider_range
                new_value = max(self.slider.minimum(), min(self.slider.maximum(), int(new_value)))
                
                self.slider.setValue(new_value)
                if self.vlc_player:
                    try:
                        self.vlc_player.set_time(new_value)
                    except Exception as e:
                        print(f"Error seeking on click: {e}")
        
        # Call the original mouse press event
        QSlider.mousePressEvent(self.slider, event)

    # ─── Controls Visibility Methods ───
    def _hide_video_controls(self):
        if self.video_controls and not self._is_closing:
            self.video_controls.setVisible(False)

    def _show_video_controls(self):
        """Show video controls and restart hide timer"""
        if (self.video_controls and self.video_container.isVisible() 
            and not self._is_closing):
            self.video_controls.show()
            self.video_controls.raise_()
            
            if hasattr(self, 'hide_timer'):
                self.hide_timer.stop()
                self.hide_timer.start()

    def _hide_navigation_controls(self):
        if not self._is_closing:
            if hasattr(self, "_mini_arrow") and not self._mini_open:
                self._mini_arrow.setVisible(False)
            if hasattr(self, "left_nav_btn"):
                self.left_nav_btn.setVisible(False)
            if hasattr(self, "right_nav_btn"):
                self.right_nav_btn.setVisible(False)

    def _show_navigation_controls(self):
        """Show navigation controls and restart hide timer"""
        if not self._is_closing:
            if hasattr(self, '_mini_arrow'):
                self._mini_arrow.show()
            if hasattr(self, 'left_nav_btn'):
                self.left_nav_btn.show()
            if hasattr(self, 'right_nav_btn'):
                self.right_nav_btn.show()
            
            if hasattr(self, 'nav_hide_timer'):
                self.nav_hide_timer.stop()
                self.nav_hide_timer.start()

    def _show_all_controls(self):
        """Show all controls and restart timers"""
        if self._is_closing:
            return
            
        try:
            # Cursor
            self.setCursor(Qt.ArrowCursor)
            if hasattr(self, 'cursor_hide_timer'):
                self.cursor_hide_timer.stop()
                self.cursor_hide_timer.start()

            # Navigation controls
            if hasattr(self, "_mini_arrow"):
                self._mini_arrow.setVisible(True)
                self._mini_arrow.raise_()
            if hasattr(self, "left_nav_btn"):
                self.left_nav_btn.setVisible(True)
                self.left_nav_btn.raise_()
            if hasattr(self, "right_nav_btn"):
                self.right_nav_btn.setVisible(True)
                self.right_nav_btn.raise_()

            # Video controls
            if self._is_video_playing() and hasattr(self, "video_controls"):
                self.video_controls.setVisible(True)
                self.video_controls.raise_()
                if hasattr(self, 'hide_timer'):
                    self.hide_timer.stop()
                    self.hide_timer.start()

            # Restart nav hide timer
            if hasattr(self, 'nav_hide_timer'):
                self.nav_hide_timer.stop()
                self.nav_hide_timer.start()
        except Exception as e:
            print(f"Error showing controls: {e}")

    def _is_video_playing(self):
        """Check if we're currently displaying a video"""
        ext = os.path.splitext(self.path)[1].lower()
        return ext in (".mp4", ".avi", ".mov", ".webm", ".mkv", ".flv") and self.video_container.isVisible()

    # ─── Event Handlers ───
    def keyPressEvent(self, event):
        """Handle keyboard events with navigation protection"""
        if self._is_closing:
            return
            
        key = event.key()

        # Handle escape key
        if key == Qt.Key_Escape:
            event.accept()
            self._safe_exit()
            return

        # Show controls on any key press
        self._show_all_controls()

        if key == Qt.Key_Space and self._is_video_playing():
            self._toggle_play_vlc()
        elif key == Qt.Key_Right:
            # Debounced navigation
            if not self._navigating:
                self._navigate_safe(1)
        elif key == Qt.Key_Left:
            # Debounced navigation
            if not self._navigating:
                self._navigate_safe(-1)
        elif key in (Qt.Key_Down, Qt.Key_Up) and hasattr(self, "doc"):
            # PDF page navigation
            if key == Qt.Key_Down and self.page_index < len(self.doc) - 1:
                self.page_index += 1
                QTimer.singleShot(50, lambda: self.show_page(self.page_index))
            elif key == Qt.Key_Up and self.page_index > 0:
                self.page_index -= 1
                QTimer.singleShot(50, lambda: self.show_page(self.page_index))

        event.accept()

    def _navigate_safe(self, direction):
        """Safe navigation with debouncing"""
        if self._navigating or self._is_closing:
            return
        
        self._navigating = True
        
        # Stop loop checking during navigation
        self._should_loop = False
        if hasattr(self, '_loop_timer'):
            self._loop_timer.stop()
        
        # Perform navigation
        self._advance(direction)
        
        # Reset navigation flag after a delay
        QTimer.singleShot(300, self._reset_navigation_flag)

    def _reset_navigation_flag(self):
        """Reset navigation flag and process any pending navigation"""
        self._navigating = False
        # Re-enable looping after navigation completes
        self._should_loop = True
        print("Navigation completed - looping re-enabled")
        
        if self._navigation_pending:
            path = self._navigation_pending
            self._navigation_pending = None
            self.load_media(path)

    def _process_pending_navigation(self):
        """Process pending navigation request"""
        if self._navigation_pending is not None:
            self._navigating = False
            path = self._navigation_pending
            self._navigation_pending = None
            self.load_media(path)

    def mouseMoveEvent(self, event):
        """Handle mouse movement"""
        if not self._is_closing:
            try:
                self.setCursor(Qt.ArrowCursor)
            except Exception:
                pass
            self._on_user_activity()
        super().mouseMoveEvent(event)

    def mousePressEvent(self, event):
        """Handle mouse clicks"""
        if self._is_closing:
            return
            
        # Right-click exits
        if event.button() == Qt.RightButton:
            event.accept()
            self._safe_exit()
            return
            
        # Left-click shows controls
        if event.button() == Qt.LeftButton:
            self._show_all_controls()
        
        super().mousePressEvent(event)

    def eventFilter(self, obj, event):
        """Handle events for video display and other widgets"""
        if self._is_closing:
            return False

        # Mouse activity
        if event.type() in (QEvent.MouseMove, QEvent.HoverMove, QEvent.Enter, QEvent.HoverEnter, QEvent.Wheel):
            try:
                self.setCursor(Qt.ArrowCursor)
            except Exception:
                pass
            self._on_user_activity()
            return False

        # Handle mouse events on video display or container
        if (obj is self.video_display or obj is self.video_container) and event.type() == QEvent.MouseButtonPress:
            self._on_user_activity()
            if event.button() == Qt.LeftButton:
                self._toggle_play_vlc()
                QTimer.singleShot(50, self._show_video_controls)
                return True
            elif event.button() == Qt.RightButton:
                event.accept()
                self._safe_exit()
                return True
                    
        return super().eventFilter(obj, event)

    def _poll_cursor_activity(self):
        """Poll cursor position for activity"""
        if self._is_closing:
            return
            
        try:
            pos = QCursor.pos()
            if pos != getattr(self, '_last_cursor_pos', pos):
                self._last_cursor_pos = pos
                if self.isVisible() and self.isActiveWindow():
                    self._on_user_activity()
        except Exception:
            pass

    def _on_user_activity(self):
        """Handle user activity"""
        if self._is_closing:
            return
            
        # Show cursor
        try:
            self.setCursor(Qt.ArrowCursor)
        except Exception:
            pass

        # Show controls
        controls = ['video_controls', 'left_nav_btn', 'right_nav_btn', '_mini_arrow']
        for control_name in controls:
            control = getattr(self, control_name, None)
            if control:
                try:
                    control.show()
                    control.raise_()
                except Exception:
                    pass

        # Restart timers
        timers = ['hide_timer', 'nav_hide_timer', 'cursor_hide_timer']
        for timer_name in timers:
            timer = getattr(self, timer_name, None)
            if timer:
                try:
                    if timer.isActive():
                        timer.stop()
                    timer.start()
                except Exception:
                    pass

    # ─── Window Events ───
    def resizeEvent(self, event):
        """Handle window resize"""
        super().resizeEvent(event)
        if not self._is_closing:
            QTimer.singleShot(10, self._position_elements)

    def showEvent(self, event):
        """Handle window show"""
        super().showEvent(event)
        if not self._is_closing:
            self.showFullScreen()
            QTimer.singleShot(100, self._position_elements)
            QTimer.singleShot(200, self._on_user_activity)
            
            if hasattr(self, "view") and hasattr(self, "item"):
                QTimer.singleShot(150, lambda: self.view.fitInView(self.item, Qt.KeepAspectRatio))

    def _position_elements(self):
        """Position all overlay elements"""
        if self._is_closing or self.width() <= 0 or self.height() <= 0:
            return
            
        try:
            # Position mini menu arrow
            self._mini_arrow.move(self.width() - 50, 10)
            
            # Position mini menu (closed position)
            self._mini_menu.move(self.width(), 50)
            
            # Position navigation buttons
            btn_y = (self.height() - 60) // 2
            self.left_nav_btn.move(20, btn_y)
            self.right_nav_btn.move(self.width() - 80, btn_y)
            
            # Raise overlay elements
            for element in [self._mini_arrow, self._mini_menu, self.left_nav_btn, self.right_nav_btn]:
                element.raise_()
        except Exception as e:
            print(f"Error positioning elements: {e}")

    # ─── Navigation Methods ───
    def _advance(self, direction=1):
        """Navigate to next/previous media"""
        try:
            if self._is_closing:
                return
                
            if self.randomize:
                new_idx = random.randint(0, len(self.media_list) - 1)
                while new_idx == self.idx and len(self.media_list) > 1:
                    new_idx = random.randint(0, len(self.media_list) - 1)
                self.idx = new_idx
            else:
                self.idx = (self.idx + direction) % len(self.media_list)

            # Validate index before loading
            if 0 <= self.idx < len(self.media_list):
                self.load_media(self.media_list[self.idx])
                
        except Exception as e:
            print(f"Error in _advance: {e}")

    def _queue_navigation(self, direction):
        """Queue navigation request with debouncing to prevent rapid key presses"""
        current_time = time.time() * 1000  # Convert to milliseconds
        
        # Debounce rapid key presses (minimum 200ms between navigations)
        if current_time - self._last_navigation_time < 200:
            return
            
        # Add to queue if not already navigating
        if not self._navigating:
            self._navigation_queue.append(direction)
            self._process_navigation_queue()
    
    def _process_navigation_queue(self):
        """Process the navigation queue safely"""
        if self._is_closing or self._navigating or not self._navigation_queue:
            return
            
        # Get the latest navigation request (ignore older ones)
        direction = self._navigation_queue.pop()
        self._navigation_queue.clear()  # Clear any remaining requests
        
        # Set navigation flag and process
        self._navigating = True
        self._last_navigation_time = time.time() * 1000
        
        # Use a timer to process navigation asynchronously
        QTimer.singleShot(100, lambda: self._safe_advance(direction))

    def _safe_advance(self, direction=1):
        """Safely navigate to next/previous media with proper cleanup"""
        try:
            if self._is_closing:
                return
                
            # Reset navigation flag
            self._navigating = False
            
            # Process any pending events to prevent blocking
            QApplication.processEvents()
            
            # Call the original advance method with additional safety
            self._advance(direction)
            
        except Exception as e:
            print(f"Error during safe advance: {e}")
            # Ensure navigation flag is reset even on error
            self._navigating = False

    def _prev(self):
        self._advance(-1)

    def _advance_slideshow(self):
        """Advance slideshow"""
        if not self._is_closing:
            self._advance(1)
            if self.slideshowTimer and self.interval:
                self.slideshowTimer.start(self.interval)

    # ─── Utility Methods ───
    def _get_button_style(self):
        return """
            QToolButton {
                color: #e0e0e0;
                background-color: #404040;
                border: 1px solid #666;
                border-radius: 4px;
                padding: 4px 8px;
                font-weight: bold;
                font-size: 10pt;
            }
            QToolButton:hover { 
                background-color: #505050; 
            }
            QToolButton:pressed { 
                background-color: #353535; 
            }
            QToolButton:checked { 
                background-color: #555555;
                border-color: #888;
            }
        """

    def _create_white_icon(self, standard_icon):
        """Create a white version of a standard icon"""
        icon = self.style().standardIcon(standard_icon)
        pixmap = icon.pixmap(32, 32)
        
        white_pixmap = QPixmap(pixmap.size())
        white_pixmap.fill(Qt.transparent)
        
        painter = QPainter(white_pixmap)
        painter.setCompositionMode(QPainter.CompositionMode_SourceOver)
        painter.drawPixmap(0, 0, pixmap)
        painter.setCompositionMode(QPainter.CompositionMode_SourceIn)
        painter.fillRect(white_pixmap.rect(), Qt.white)
        painter.end()
        
        return QIcon(white_pixmap)

    def _update_file_label(self):
        """Update the mini-menu filename label"""
        if hasattr(self, "_file_label"):
            self._file_label.setText(os.path.basename(self.path))

    # ─── Menu Methods ───
    def _toggle_mini_menu(self):
        """Toggle mini menu visibility"""
        if self._is_closing:
            return
            
        self._mini_anim.stop()
        self._show_all_controls()

        if not self._mini_open:
            self._mini_menu.show()
            target_x = self.width() - self._mini_menu.width() - 10
            self._mini_anim.setStartValue(self._mini_menu.pos())
            self._mini_anim.setEndValue(QPoint(target_x, 50))
            self._mini_arrow.setArrowType(Qt.RightArrow)
            if hasattr(self, 'nav_hide_timer'):
                self.nav_hide_timer.stop()
        else:
            self._mini_anim.setStartValue(self._mini_menu.pos())
            self._mini_anim.setEndValue(QPoint(self.width(), 50))
            self._mini_arrow.setArrowType(Qt.LeftArrow)

            def _after_hide():
                if not self._is_closing:
                    self._mini_menu.hide()
            self._mini_anim.finished.connect(_after_hide)
            if hasattr(self, 'nav_hide_timer'):
                self.nav_hide_timer.start()

        self._mini_open = not self._mini_open
        self._mini_anim.start()

    def start_stop_slideshow(self):
        """Start or stop slideshow"""
        if self._is_closing:
            return
            
        if self.slideshowTimer is None:
            from PyQt5.QtWidgets import QInputDialog
            secs, ok = QInputDialog.getInt(
                self, "Slideshow", "Seconds per slide:", 5, 1, 60
            )
            if not ok:
                return

            self.interval = secs * 1000
            self.slideshowTimer = QTimer(self)
            self.slideshowTimer.setSingleShot(True)
            self.slideshowTimer.timeout.connect(self._advance_slideshow)
            self.slideshowTimer.start(self.interval)
            self._slideshow_btn.setText("Stop Slideshow")
        else:
            self.slideshowTimer.stop()
            self.slideshowTimer = None
            self.interval = None
            self._slideshow_btn.setText("Slideshow")

    def _toggle_random_mode(self, checked):
        """Toggle random mode"""
        self.randomize = checked
        self.rand_btn.setText("Exit Random" if checked else "Random")

    def _print_current(self):
        """Print current media"""
        if hasattr(self, "doc") and self.doc:
            self._print_pdf()
            return

        if not hasattr(self, "item") or self.item is None:
            print("No static image to print.")
            return

        from PyQt5.QtPrintSupport import QPrinter, QPrintDialog
        from PyQt5.QtGui import QPainter
        
        printer = QPrinter(QPrinter.HighResolution)
        dialog = QPrintDialog(printer, self)
        if dialog.exec_() == QPrintDialog.Accepted:
            painter = QPainter(printer)
            pixmap = self.item.pixmap()
            rect = painter.viewport()
            size = pixmap.size()
            size.scale(rect.size(), Qt.KeepAspectRatio)
            painter.setViewport(rect.x(), rect.y(), size.width(), size.height())
            painter.setWindow(pixmap.rect())
            painter.drawPixmap(0, 0, pixmap)
            painter.end()

    def _confirm_delete_file(self):
        """Confirm and delete current file"""
        from PyQt5.QtWidgets import QMessageBox
        
        file_path = self.path
        file_name = os.path.basename(file_path)

        reply = QMessageBox.question(
            self, "Delete File",
            f'This will delete "{file_name}" from your computer.\n'
            f"This cannot be undone.\n\nAre you sure you want to delete this file?",
            QMessageBox.Yes | QMessageBox.No,
        )

        if reply == QMessageBox.Yes:
            try:
                os.remove(file_path)
                print(f"Deleted file: {file_path}")
                self._safe_exit()
            except Exception as e:
                QMessageBox.critical(self, "Error", f"Failed to delete file:\n{str(e)}")

    # ─── PDF Methods ───
    def show_page(self, idx):
        """Render PDF page"""
        if not hasattr(self, 'doc') or not self.doc or self._is_closing:
            return
            
        try:
            page = self.doc[idx]
            rect = page.rect

            vp = self.view.viewport().size()
            vp_w, vp_h = vp.width(), vp.height()

            if vp_w <= 0 or vp_h <= 0:
                return

            scale_x = vp_w / rect.width
            scale_y = vp_h / rect.height
            scale = min(scale_x, scale_y)

            mat = fitz.Matrix(scale, scale)
            pix = page.get_pixmap(matrix=mat, alpha=False)

            image = QImage(
                pix.samples, pix.width, pix.height, pix.stride, QImage.Format_RGB888
            )
            self.pix_item.setPixmap(QPixmap.fromImage(image))

            self._page_label.setText(f"Page {idx + 1} of {len(self.doc)}")
            self._page_label.adjustSize()
            label_x = (self.width() - self._page_label.width()) // 2
            self._page_label.move(label_x, 20)

            QTimer.singleShot(10, lambda: self.view.fitInView(self.pix_item, Qt.KeepAspectRatio))
        except Exception as e:
            print(f"Error showing PDF page: {e}")

    def _print_pdf(self):
        """Print PDF pages"""
        from PyQt5.QtPrintSupport import QPrinter, QPrintDialog
        from PyQt5.QtGui import QPainter
        
        if not hasattr(self, "doc") or not self.doc:
            return

        printer = QPrinter(QPrinter.HighResolution)
        dialog = QPrintDialog(printer, self)
        if dialog.exec_() != QPrintDialog.Accepted:
            return

        painter = QPainter(printer)
        for page_num in range(len(self.doc)):
            page = self.doc[page_num]
            mat = fitz.Matrix(2.0, 2.0)
            pix = page.get_pixmap(matrix=mat, alpha=False)
            
            image = QImage(
                pix.samples, pix.width, pix.height, pix.stride, QImage.Format_RGB888
            )
            
            rect = painter.viewport()
            size = image.size()
            size.scale(rect.size(), Qt.KeepAspectRatio)
            painter.setViewport(rect.x(), rect.y(), size.width(), size.height())
            painter.setWindow(image.rect())
            painter.drawImage(0, 0, image)

            if page_num != len(self.doc) - 1:
                printer.newPage()

        painter.end()

    # ─── GIF Methods ───
    def _update_gif_frame(self):
        """Update GIF frame"""
        if self._is_closing:
            return
            
        if hasattr(self, 'item') and hasattr(self, 'movie'):
            try:
                self.item.setPixmap(self.movie.currentPixmap())
                if hasattr(self, 'view'):
                    self.view.fitInView(self.item, Qt.KeepAspectRatio)
            except Exception as e:
                print(f"Error updating GIF frame: {e}")

# -----------------------------------------------------------------------------
# Thumbnail Cropper
# -----------------------------------------------------------------------------
class ImageCropper(QDialog):
    def __init__(self, image_path, on_crop_complete, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Crop & Position Your Image")
        self.setWindowFlags(
            self.windowFlags() & ~Qt.WindowContextHelpButtonHint
        )  # Remove "?"
        self.setStyleSheet("background-color: #1E1E1E; color: white;")
        self.setMinimumSize(720, 720)

        self.image_path = image_path
        self.on_crop_complete = on_crop_complete
        self.crop_size = 400
        self.final_size = 1670
        self.scale = 1.0
        self.offset_x = 0
        self.offset_y = 0
        self.dragging = False
        self.last_mouse_pos = None

        self.img = QPixmap(self.image_path)
        if self.img.isNull():
            QMessageBox.critical(
                self, "Error", f"Could not load image: {self.image_path}"
            )
            self.reject()

        # Canvas with red border
        self.canvas = QLabel()
        self.canvas.setFixedSize(self.crop_size, self.crop_size)
        self.canvas.setStyleSheet("background-color: #1E1E1E; border: 2px solid red;")
        self.canvas.setMouseTracking(True)
        self.canvas.installEventFilter(self)

        # Instructions
        self.instructions = QLabel("Drag to reposition • Use mouse wheel to zoom")
        self.instructions.setAlignment(Qt.AlignCenter)
        self.instructions.setStyleSheet("color: white; font-size: 10pt;")

        # Buttons
        zoom_in_btn = QPushButton("Zoom In")
        zoom_out_btn = QPushButton("Zoom Out")
        reset_btn = QPushButton("Reset Position")
        ok_btn = QPushButton("OK")
        cancel_btn = QPushButton("Cancel")

        zoom_in_btn.clicked.connect(self.zoom_in)
        zoom_out_btn.clicked.connect(self.zoom_out)
        reset_btn.clicked.connect(self.reset_position)
        ok_btn.clicked.connect(self.crop_image)
        cancel_btn.clicked.connect(self.reject)

        # Layouts
        btn_row = QHBoxLayout()
        btn_row.addWidget(zoom_out_btn)
        btn_row.addWidget(zoom_in_btn)
        btn_row.addWidget(reset_btn)
        btn_row.addStretch()
        btn_row.addWidget(ok_btn)
        btn_row.addWidget(cancel_btn)

        center_layout = QVBoxLayout()
        center_layout.addWidget(self.canvas, alignment=Qt.AlignCenter)
        center_layout.addWidget(self.instructions)
        center_layout.addLayout(btn_row)

        self.setLayout(center_layout)

        # Fit on load
        self.auto_fit_image()
        self.draw_image()

    def auto_fit_image(self):
        img_w = self.img.width()
        img_h = self.img.height()
        aspect = img_w / img_h
        if aspect > 1:
            self.scale = self.crop_size / img_w
        else:
            self.scale = self.crop_size / img_h
        self.offset_x = 0
        self.offset_y = 0

    def reset_position(self):
        self.auto_fit_image()
        self.draw_image()

    def draw_image(self):
        canvas_pix = QPixmap(self.crop_size, self.crop_size)
        canvas_pix.fill(QColor("#1E1E1E"))

        painter = QPainter(canvas_pix)
        scaled = self.img.scaled(
            int(self.img.width() * self.scale),
            int(self.img.height() * self.scale),
            Qt.KeepAspectRatio,
            Qt.SmoothTransformation,
        )
        x = int(self.offset_x + (self.crop_size - scaled.width()) / 2)
        y = int(self.offset_y + (self.crop_size - scaled.height()) / 2)
        painter.drawPixmap(x, y, scaled)

        # Draw grid lines (3x3)
        pen = QPen(QColor(255, 255, 255, 100), 1, Qt.DotLine)
        painter.setPen(pen)
        for i in range(1, 3):
            pos = i * self.crop_size // 3
            painter.drawLine(pos, 0, pos, self.crop_size)
            painter.drawLine(0, pos, self.crop_size, pos)

        painter.end()
        self.canvas.setPixmap(canvas_pix)

    def crop_image(self):
        try:
            scale_factor = self.final_size / self.crop_size
            img_scaled_w = self.img.width() * self.scale * scale_factor
            img_scaled_h = self.img.height() * self.scale * scale_factor
            x = (
                self.offset_x + (self.crop_size - self.img.width() * self.scale) / 2
            ) * scale_factor
            y = (
                self.offset_y + (self.crop_size - self.img.height() * self.scale) / 2
            ) * scale_factor

            final_img = QImage(self.final_size, self.final_size, QImage.Format_ARGB32)
            final_img.fill(QColor("#1E1E1E"))
            painter = QPainter(final_img)
            painter.drawPixmap(
                int(x), int(y), int(img_scaled_w), int(img_scaled_h), self.img
            )
            painter.end()

            result = QPixmap.fromImage(final_img)
            self.on_crop_complete(result)
            self.accept()
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to crop image: {str(e)}")

    def zoom_in(self):
        self.scale = min(self.scale * 1.25, 5.0)
        self.draw_image()

    def zoom_out(self):
        self.scale = max(self.scale / 1.25, 0.05)
        self.draw_image()

    def eventFilter(self, source, event):
        if source == self.canvas:
            if (
                event.type() == QEvent.MouseButtonPress
                and event.button() == Qt.LeftButton
            ):
                self.dragging = True
                self.last_mouse_pos = event.pos()
            elif event.type() == QEvent.MouseMove and self.dragging:
                delta = event.pos() - self.last_mouse_pos
                self.offset_x += delta.x()
                self.offset_y += delta.y()
                self.last_mouse_pos = event.pos()
                self.draw_image()
            elif event.type() == QEvent.MouseButtonRelease:
                self.dragging = False
            elif event.type() == QEvent.Wheel:
                angle = event.angleDelta().y()
                factor = 1.25 if angle > 0 else 0.8
                new_scale = self.scale * factor
                if 0.05 < new_scale < 10:
                    self.scale = new_scale
                    self.draw_image()
        return super().eventFilter(source, event)


class QProgressIndicator(QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.angle = 0
        self.timer = QTimer(self)
        self.timer.timeout.connect(self.rotate)
        self.setFixedSize(30, 30)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.hide()

    def start(self):
        self.timer.start(100)
        self.show()

    def stop(self):
        self.timer.stop()
        self.hide()

    def rotate(self):
        self.angle = (self.angle + 30) % 360
        self.update()

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.Antialiasing)
        center = self.rect().center()
        painter.translate(center)
        painter.rotate(self.angle)
        painter.setPen(Qt.NoPen)
        painter.setBrush(QColor(200, 200, 200))  # adjust for dark/light mode
        radius = min(self.width(), self.height()) / 3.8
        for i in range(12):
            painter.save()
            painter.rotate(i * 30.0)
            painter.setOpacity(1.0 - (i / 12.0))
            painter.drawRoundedRect(QRectF(radius, -2, 6, 4), 2, 2)
            painter.restore()


# -----------------------------------------------------------------------------
# Main Explorer widget
# -----------------------------------------------------------------------------
class MediaExplorer(QWidget):
    def __init__(self):
        super().__init__()
        self.current_directory = None

        # App and root directories
        if getattr(sys, 'frozen', False):
            base_dir = os.path.dirname(sys.executable)  # when frozen (.exe)
        else:
            base_dir = os.path.abspath(os.path.dirname(__file__))  # when running .py

        self.app_dir = base_dir
        self.root_dir = os.path.abspath(os.path.join(base_dir, ".."))
        self.current_dir = self.root_dir

        # where to store cached thumbs
        self.thumb_cache_dir = Path(self.app_dir) / ".thumbs_cache"
        self.thumb_cache_dir.mkdir(exist_ok=True)
        self.current_dir = self.root_dir

        # where to store cached thumbs (define early, before any use)
        self.thumb_cache_dir = Path(self.app_dir) / ".thumbs_cache"
        self.thumb_cache_dir.mkdir(exist_ok=True)
        # persistent map (path → cache filename)
        
        # Video metadata cache for faster loading
        self.video_metadata_cache = {}  # path → {duration, size, codec, etc}
        self.video_cache_file = os.path.join(self.app_dir, "video_cache.json")
        self._load_video_cache()

        # Restore Toolbar Button (only visible when toolbar is hidden)
        self.restore_toolbar_btn = QPushButton("Show Toolbar", self)
        self.restore_toolbar_btn.setFixedSize(120, 36)
        self.restore_toolbar_btn.setStyleSheet(
            """
            QPushButton {
                background-color: rgba(30, 30, 30, 200);
                color: white;
                border-radius: 6px;
                padding: 6px;
                font-size: 11pt;
            }
            QPushButton:hover {
                background-color: rgba(60, 60, 60, 220);
            }
        """
        )
        self.restore_toolbar_btn.clicked.connect(self._show_toolbar_from_button)
        self.restore_toolbar_btn.hide()  # Initially hidden
        self.restore_toolbar_btn.raise_()  # Ensure it's on top of other widgets

        # whether those labels are visible
        self.show_names = True

        self.settings_file = os.path.join(self.app_dir, "settings.json")
        self.settings = self._load_json(self.settings_file)

        # Pull or initialize all settings at once
        self.show_names = self.settings.get("show_names", True)
        self.show_tags = self.settings.get("show_tags", True)
        self.breadcrumb_visible = self.settings.get("breadcrumb_visible", True)
        self.toolbar_visible = self.settings.get("toolbar_visible", True)
        self.file_title_placement = self.settings.get("file_title_placement", "bottom")
        self.folder_title_placement = self.settings.get(
            "folder_title_placement", "bottom"
        )
        self.hide_folder_names = self.settings.get("hide_folder_names", False)
        self.hide_folder_overlay_icon = self.settings.get(
            "hide_folder_overlay_icon", False
        )
        self.folder_title_bg_mode = self.settings.get(
            "folder_title_bg_mode", "default"
        )  # "default", "short", "none"
        self.file_title_bg_mode = self.settings.get(
            "file_title_bg_mode", "default"
        )  # "default", "short", "none"

        # Add title placement defaults (use .get() so existing users get defaults)
        self.file_title_placement = self.settings.get("file_title_placement", "bottom")
        self.folder_title_placement = self.settings.get(
            "folder_title_placement", "bottom"
        )

        # Load maps
        self.thumb_map_file = os.path.join(
            self.app_dir, ".media_explorer_folder_thumbs.json"
        )
        self.launch_map_file = os.path.join(
            self.app_dir, ".media_explorer_folder_launch.json"
        )
        self.folder_thumb_map = self._load_json(self.thumb_map_file)
        self.folder_launch_map = self._load_json(self.launch_map_file)
        self.favorites_file = os.path.join(
            self.app_dir, ".media_explorer_favorites.json"
        )
        favorites_data = self._load_json(self.favorites_file)
        if isinstance(favorites_data, list):
            self.favorites = set(favorites_data)
        else:
            self.favorites = set()
        self.settings_file = os.path.join(self.app_dir, "settings.json")
        self.settings = self._load_json(self.settings_file)
        self.hide_folder_names = self.settings.get("hide_folder_names", False)
        self.hide_folder_overlay_icon = self.settings.get(
            "hide_folder_overlay_icon", False
        )
        self.show_folder_names = not self.hide_folder_names

        self.editMode = False
        self.slideshowActive = False
        self._lastInterval = None
        self.hide_unsupported = False
        self.show_tags = True
        self.hide_folders = self.settings.get("hide_folders", False)
        self.hide_launch_icon = False
        self.image_thumb_mode = self.settings.get(
            "image_thumb_mode", "zoom"
        )  # default: zoom

        # In-memory thumbnail cache
        self._thumb_cache = {}
        self.media_files = []
        self.sorted_files = []

        # track theme
        self.is_dark_mode = True  # Start in dark mode

        # Start fullscreen
        self.showFullScreen()
        self.setMouseTracking(True)

        # Main layout
        main = QVBoxLayout(self)
        main.setContentsMargins(0, 0, 0, 0)
        main.setSpacing(0)

        # Toolbar frame + fade effect
        self.toolbar = QFrame()
        self.toolbar.setObjectName("toolbar")

        self.toolbar.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self.toolbar.setVisible(True)

        # Optional shadow line under toolbar
        shadow_line = QFrame(self.toolbar)
        shadow_line.setFixedHeight(1)
        shadow_line.setStyleSheet("background-color: rgba(0, 0, 0, 50);")

        # Hint arrow
        self.hint = QLabel("▼", self)
        self.hint.setAlignment(Qt.AlignHCenter | Qt.AlignVCenter)
        self.hint.setStyleSheet("color: #888; font-size: 24px;")
        self.hint.setFixedHeight(24)
        self.hint.hide()
        main.addWidget(self.hint)

        # Toolbar contents
        tb = QHBoxLayout(self.toolbar)
        tb.setContentsMargins(12, 4, 12, 4)
        tb.setSpacing(16)

        # ── BACK BUTTON ─────────────────────
        self.back_btn = HoverToolButton()
        self.back_btn.setIcon(QIcon("_internal/icons/back.svg"))
        self.back_btn.setIconSize(QSize(28, 28))
        self.back_btn.setFixedSize(48, 48)  # Slightly smaller since it's icon-only
        self.back_btn.setToolButtonStyle(Qt.ToolButtonIconOnly)
        self.back_btn.setCursor(Qt.PointingHandCursor)
        self.back_btn.clicked.connect(self._navigate_up)
        tb.addWidget(self.back_btn)

        # Settings
        self.gear = HoverToolButton()
        self.gear.setIcon(QIcon("_internal/icons/settings.svg"))
        self.gear.setIconSize(QSize(28, 28))
        self.gear.setFixedSize(80, 72)
        self.gear.setStyleSheet(
            """
            QToolButton {
                font-size: 9pt;
                text-align: center;
                padding-top: 6px;
                padding-bottom: 2px;
            }
        
        QToolButton::menu-indicator {
            subcontrol-position: bottom center;
            subcontrol-origin: padding;
        }
        """
        )
        self.gear.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
        self.gear.setText("Settings")
        self.gear.setPopupMode(QToolButton.InstantPopup)
        menu = QMenu(self)
        self.settings_menu = menu
        menu.addAction("Change Resolution…", self.openResolutionDialog)
        menu.addAction("Clear File Thumbnail Cache…", self.clear_thumbnail_cache)
        self.theme_action = QAction("Light Mode", self)
        self.theme_action.triggered.connect(self.toggle_theme)
        menu.addAction(self.theme_action)
        menu.addAction("About", self.openAbout)
        menu.addAction("Exit Program", self.confirmExit)
        self.gear.setMenu(menu)
        tb.addWidget(self.gear)

        # ── VIEW BUTTON ─────────────────────────────────────
        self.view_btn = HoverToolButton()
        self.view_btn.setIcon(QIcon("_internal/icons/view.svg"))  # ← Add appropriate icon
        self.view_btn.setIconSize(QSize(28, 28))
        self.view_btn.setText("View")
        self.view_btn.setStyleSheet(
            """
            QToolButton {
                font-size: 9pt;
                text-align: center;
                padding-top: 6px;
                padding-bottom: 2px;
            }
            QToolButton::menu-indicator {
                subcontrol-position: bottom center;
                subcontrol-origin: padding;
            }
        """
        )
        self.view_btn.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
        self.view_btn.setPopupMode(QToolButton.InstantPopup)
        self.view_btn.setFixedSize(80, 72)

        self.view_menu = QMenu(self)

        # Thumbnail Size option
        thumb_size_action = QAction("Thumbnail Size…", self)
        thumb_size_action.triggered.connect(self.openThumbnailSizeDialog)
        self.view_menu.addAction(thumb_size_action)

        # Image thumbnail options
        image_thumb_options_action = QAction("Image Thumbnail Options", self)
        image_thumb_options_action.triggered.connect(
            self._show_image_thumb_options_dialog
        )
        self.view_menu.addAction(image_thumb_options_action)

        # Hide Folders toggle
        self.toggle_hide_folders_action = QAction("Hide Folders", self, checkable=True)
        self.toggle_hide_folders_action.setChecked(self.hide_folders)
        self.toggle_hide_folders_action.triggered.connect(self._toggle_hide_folders)
        self.view_menu.addAction(self.toggle_hide_folders_action)

        # Toggle breadcrumb visibility
        self.toggle_crumb_action = QAction("Show Breadcrumb Bar", self, checkable=True)
        self.toggle_crumb_action.setChecked(self.breadcrumb_visible)
        self.toggle_crumb_action.triggered.connect(self._toggle_breadcrumb_visibility)
        self.view_menu.addAction(self.toggle_crumb_action)

        # Hide Unsupported Files toggle
        self.hideUnsupportedAction = QAction("Hide Unsupported Files", self)
        self.hideUnsupportedAction.setCheckable(True)
        self.hideUnsupportedAction.setChecked(self.hide_unsupported)
        self.hideUnsupportedAction.toggled.connect(self.toggle_hide_unsupported)
        self.view_menu.addAction(self.hideUnsupportedAction)

        # Toggle Toolbar
        self.toggle_toolbar_action = QAction("Hide Toolbar", self)
        self.toggle_toolbar_action.setCheckable(True)
        self.toggle_toolbar_action.setChecked(False)
        self.toggle_toolbar_action.triggered.connect(self._toggle_toolbar)
        self.view_menu.addAction(self.toggle_toolbar_action)

        self.view_menu.addSeparator()

        # File title placement (overlay)
        self.file_title_placement_action = QAction(
            "File Title at Top", self, checkable=True
        )
        self.file_title_placement_action.setChecked(self.file_title_placement == "top")
        self.file_title_placement_action.triggered.connect(
            self.toggle_file_title_placement
        )

        # Folder title placement (overlay)
        self.folder_title_placement_action = QAction(
            "Folder Title at Top", self, checkable=True
        )
        self.folder_title_placement_action.setChecked(
            self.folder_title_placement == "top"
        )
        self.folder_title_placement_action.triggered.connect(
            self.toggle_folder_title_placement
        )

        self.view_menu.addSeparator()

        # Hide File Names toggle (show/hide button)
        self.hide_names_action = QAction("Hide File Names", self)
        self.hide_names_action.setCheckable(True)
        self.hide_names_action.setChecked(not self.show_names)
        self.hide_names_action.toggled.connect(self.toggle_filenames)

        self.view_btn.setMenu(self.view_menu)
        tb.addWidget(self.view_btn)

        # Hide folder names toggle (show/hide button)
        self.toggle_folder_names_action = QAction(
            "Hide Folder Names", self, checkable=True
        )
        self.toggle_folder_names_action.setChecked(self.hide_folder_names)
        self.toggle_folder_names_action.triggered.connect(self._toggle_folder_names)

        self.view_menu.addSeparator()

        # Hide folder overlay icon toggle (overlay button)
        self.folder_overlay_position = self.settings.get(
            "folder_overlay_position", "bottom-left"
        )

        overlay_menu = QMenu("Folder Overlay Options", self)
        positions = ["top-left", "top-right", "bottom-left", "bottom-right", "hidden"]
        self.overlay_position_actions = {}

        for pos in positions:
            action = QAction(pos.replace("-", " ").title(), self, checkable=True)
            action.triggered.connect(
                lambda _, p=pos: self._set_folder_overlay_position(p)
            )
            overlay_menu.addAction(action)
            self.overlay_position_actions[pos] = action

        # Mark the current one as checked
        if self.folder_overlay_position in self.overlay_position_actions:
            self.overlay_position_actions[self.folder_overlay_position].setChecked(True)

        # Hide file tags (show/hide button)
        self.hide_tags_action = QAction("Hide File Tags", self)
        self.hide_tags_action.setCheckable(True)
        self.hide_tags_action.setChecked(not self.show_tags)
        self.hide_tags_action.toggled.connect(self.toggle_file_tags)

        self._load_view_settings()

        # Hide launch mode icon (show/hide button)
        self.toggle_launch_icon_action = QAction(
            "Hide Launch Mode Icon", self, checkable=True
        )
        self.toggle_launch_icon_action.setChecked(self.hide_launch_icon)
        self.toggle_launch_icon_action.triggered.connect(
            self._toggle_launch_icon_visibility
        )

        # ── OVERLAY CONTROLS GROUP ─────────────────
        self.overlay_group_btn = HoverToolButton()
        self.overlay_group_btn.setIcon(QIcon("_internal/icons/overlay.svg"))
        self.overlay_group_btn.setIconSize(QSize(28, 28))
        self.overlay_group_btn.setText("Overlay\nToggles")
        self.overlay_group_btn.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
        self.overlay_group_btn.setFixedSize(80, 72)
        self.overlay_group_btn.setPopupMode(QToolButton.InstantPopup)

        # Add this stylesheet to create space for the arrow
        self.overlay_group_btn.setStyleSheet(
            """
            QToolButton::menu-button {
                margin-bottom: -4px;  /* Adjust this value as needed */
                font-size: 9pt;
                text-align: center;
                padding-top: 6px;
                padding-bottom: 2px
            }
            QToolButton {
                padding-bottom: 8px;  /* Creates space at the bottom for the arrow */
            }
            QToolButton::menu-indicator {
                subcontrol-position: bottom center;
                subcontrol-origin: padding;
            }
        """
        )

        overlay_menu = QMenu(self)
        overlay_menu.addAction(self.hide_names_action)
        overlay_menu.addAction(self.hide_tags_action)

        overlay_menu.addAction(self.toggle_folder_names_action)
        overlay_position_action = QAction("Set Folder Overlay Position…", self)
        overlay_position_action.triggered.connect(self._open_overlay_position_dialog)
        overlay_menu.addAction(overlay_position_action)

        overlay_menu.addAction(self.file_title_placement_action)
        overlay_menu.addAction(self.folder_title_placement_action)
        title_bg_action = QAction("File/Folder Title Background Options", self)
        title_bg_action.triggered.connect(self.show_title_background_options_dialog)
        self.view_menu.addAction(title_bg_action)

        overlay_menu.addAction(self.toggle_launch_icon_action)

        self.overlay_group_btn.setMenu(overlay_menu)
        tb.addWidget(self.overlay_group_btn)

        # Edit Mode
        self.edit_btn = HoverToolButton()
        self.edit_btn.setIcon(QIcon("_internal/icons/edit_mode.svg"))
        self.edit_btn.setIconSize(QSize(28, 28))
        self.edit_btn.setMinimumSize(80, 72)
        self.edit_btn.setStyleSheet(
            """
            QToolButton {
                font-size: 9pt;
                text-align: center;
                padding-top: 6px;
                padding-bottom: 2px;
            }
        """
        )
        self.edit_btn.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
        self.edit_btn.setText("Edit Mode")
        self.edit_btn.clicked.connect(self.toggle_edit_mode)
        tb.addWidget(self.edit_btn)

        # ── RELOAD THUMBNAILS BUTTON ─────────────────────
        self.reload_thumbs_btn = HoverToolButton()
        refresh_icon = (
            QIcon("_internal/icons/refresh_light.svg")
            if self.is_dark_mode
            else QIcon("_internal/icons/refresh_dark.svg")
        )
        self.reload_thumbs_btn.setIcon(refresh_icon)
        self.reload_thumbs_btn.setIconSize(QSize(28, 28))
        self.reload_thumbs_btn.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
        self.reload_thumbs_btn.setText("Update\nFile Thumbs")
        self.reload_thumbs_btn.setStyleSheet(
            """
            QToolButton {
                font-size: 9pt;
                text-align: center;
                padding-top: 6px;
                padding-bottom: 2px;
            }
        """
        )
        self.reload_thumbs_btn.setFixedSize(80, 72)
        self.reload_thumbs_btn.clicked.connect(self._reload_thumbnails)
        tb.addWidget(self.reload_thumbs_btn)

        # ── Home button ─────────────────────
        self.home_btn = HoverToolButton()
        self.home_btn.setIconSize(QSize(38, 38))
        self.home_btn.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
        self.home_btn.setText("Home")
        self.home_btn.setFixedSize(80, 72)
        self.home_btn.setStyleSheet(
            """
            QToolButton {
                font-size: 9pt;
                text-align: center;
                padding-top: 6px;
                padding-bottom: 2px;
            }
        """
        )
        self.home_btn.clicked.connect(lambda: self.load_directory(self.root_dir))
        tb.addWidget(self.home_btn)

        # Create a container for the spinner to reserve space
        self.spinner_container = QWidget(self)
        self.spinner_container.setStyleSheet("background-color: transparent;")
        spinner_layout = QHBoxLayout(self.spinner_container)
        spinner_layout.setContentsMargins(0, 0, 0, 0)
        spinner_layout.setSpacing(0)
        spinner_layout.setAlignment(Qt.AlignCenter)

        # Create the spinner
        self.spinner = QProgressIndicator(self.spinner_container)
        spinner_layout.addWidget(self.spinner)

        # Fix the container size to prevent layout shifting
        self.spinner_container.setFixedSize(36, 36)  # adjust if needed
        tb.addWidget(self.spinner_container)
        tb.addSpacing(90)

        # Logo (between sort buttons and exit button)
        self.logo_label = QLabel()
        self.logo_pixmap_dark = QPixmap("_internal/icons/logo_dark.png")  # Your dark mode logo
        self.logo_pixmap_light = QPixmap("_internal/icons/logo_light.png")  # Your light mode logo

        # Set initial logo based on current mode
        initial_logo = (
            self.logo_pixmap_dark if self.is_dark_mode else self.logo_pixmap_light
        )
        self.logo_label.setPixmap(
            initial_logo.scaled(280, 80, Qt.KeepAspectRatio, Qt.SmoothTransformation)
        )
        self.logo_label.setAlignment(Qt.AlignCenter)
        self.logo_label.setFixedSize(275, 70)

        # Insert the logo into the toolbar layout
        tb.addWidget(self.logo_label)
        tb.addSpacing(100)

        # Group: Search bar + breadcrumb in a vertical layout
        search_row = QHBoxLayout()
        search_row.setContentsMargins(0, 0, 0, 0)
        search_row.setSpacing(8)

        # Search bar - REMOVE setMaximumWidth()
        self.search = QLineEdit()
        self.search.setPlaceholderText("Search…")
        self.search.setClearButtonEnabled(True)
        self.search.setMinimumWidth(200)  # Minimum width instead of maximum
        self.search.setMaximumWidth(300)  # Set maximum width to prevent overflow
        self.search.setMaximumHeight(35)
        self.search.textChanged.connect(self._filterThumbnails)
        self.search.setStyleSheet(
            """
            QLineEdit {
                background-color: #FFFFFF;
                color: black;
                border: 1px solid rgba(255, 255, 255, 0.6);
                border-radius: 6px;
                padding: 4px 8px;
            }
            QLineEdit:focus {
                border: 1px solid rgba(255, 255, 255, 0.4);
            }
        """
        )
        search_row.addWidget(self.search, stretch=1)  # Add stretch factor

        # Small Sort Buttons (stacked inline, icon only)
        sort_btn_frame = QFrame()
        sort_btn_layout = QHBoxLayout(sort_btn_frame)
        sort_btn_layout.setContentsMargins(0, 0, 0, 0)
        sort_btn_layout.setSpacing(4)

        self.sort_buttons = {}

        for mode, icon_path in {
            "ascending": "_internal/icons/sort_asc.svg",
            "descending": "_internal/icons/sort_desc.svg",
            "random": "_internal/icons/sort_random.svg",
            "favorites": "_internal/icons/heart_filter.svg",
        }.items():
            btn = QToolButton()
            btn.setIcon(QIcon(icon_path))
            btn.setIconSize(QSize(20, 20))
            btn.setFixedSize(32, 32)
            btn.setStyleSheet(
                """
            QPushButton {
                background: rgba(50, 49, 48, 6);
                border-radius: 8px;
            }
            QPushButton:hover {
                background-color: rgba(255, 255, 255, 0.07);
            }
        """
            )
            btn.clicked.connect(lambda _, m=mode: self._set_sort_mode(m))
            sort_btn_layout.addWidget(btn)
            self.sort_buttons[mode] = btn

        # Add sort buttons inline
        search_row.addWidget(sort_btn_frame)
        search_row.addStretch()  # This will push everything left

        # Vertical layout: search row + breadcrumb
        search_block = QVBoxLayout()
        search_block.setContentsMargins(0, 0, 0, 0)
        search_block.setSpacing(2)
        search_block.addLayout(search_row)

        self.crumb = QLabel(self.current_dir)
        self.crumb.setStyleSheet(
            """
            QLabel {
                color: #bbb;
                font-size: 9pt;
                padding: 2px 6px;
                background-color: rgba(255, 255, 255, 0.04);
                border-radius: 4px;
            }
            QLabel {
                color: #bbb;
                font-size: 9pt;
                padding: 2px 6px;
                background-color: rgba(255, 255, 255, 0.04);
                border-radius: 4px;
            }
        """
        )
        self.crumb.setSizePolicy(QSizePolicy.Maximum, QSizePolicy.Fixed)
        self.crumb.adjustSize()
        self.crumb.setAlignment(Qt.AlignLeft | Qt.AlignVCenter)
        self.crumb.setVisible(self.breadcrumb_visible)
        search_block.addWidget(self.crumb)

        search_container = QWidget()
        search_container.setLayout(search_block)
        search_container.setStyleSheet("background-color: transparent;")
        search_container.setMaximumWidth(400)  # Limit width to prevent toolbar overflow
        search_container.setSizePolicy(QSizePolicy.Maximum, QSizePolicy.Fixed)

        tb.addWidget(search_container)
        tb.addStretch()  # Add stretch to push buttons to the right and prevent overflow

        # ── NEW FOLDER BUTTON ─────────────────────
        self.new_folder_btn = HoverToolButton()
        self.new_folder_btn.setIcon(QIcon("_internal/icons/folder_add.svg"))
        self.new_folder_btn.setIconSize(QSize(28, 28))
        self.new_folder_btn.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
        self.new_folder_btn.setText("New\nFolder")
        self.new_folder_btn.setStyleSheet(
            """
            QToolButton {
                font-size: 9pt;
                text-align: center;
                padding-top: 6px;
                padding-bottom: 2px;
            }
        """
        )
        self.new_folder_btn.setFixedSize(80, 72)
        self.new_folder_btn.clicked.connect(self._create_new_folder)
        tb.addWidget(self.new_folder_btn)

        # ── IMPORT FILES BUTTON ───────────────────
        self.import_files_btn = HoverToolButton()
        self.import_files_btn.setIcon(QIcon("_internal/icons/import.svg"))
        self.import_files_btn.setIconSize(QSize(28, 28))
        self.import_files_btn.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
        self.import_files_btn.setText("Import\nFiles")
        self.import_files_btn.setStyleSheet(
            """
            QToolButton {
                font-size: 9pt;
                text-align: center;
                padding-top: 6px;
                padding-bottom: 2px;
                min-height: 72px;
            }
        """
        )
        self.import_files_btn.setFixedSize(80, 72)
        self.import_files_btn.clicked.connect(self._import_files)
        tb.addWidget(self.import_files_btn)

        # Exit
        self.exit_btn = HoverToolButton()
        self.exit_btn.setIcon(QIcon("_internal/icons/exit.svg"))
        self.exit_btn.setIconSize(QSize(28, 28))
        self.exit_btn.setFixedSize(80, 72)
        self.exit_btn.setStyleSheet(
            """
            QToolButton {
                font-size: 9pt;
                text-align: center;
                padding-top: 6px;
                padding-bottom: 2px;
                min-height: 72px;
            }
        """
        )
        self.exit_btn.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
        self.exit_btn.setText("Exit")
        self.exit_btn.clicked.connect(self.confirmExit)
        tb.addWidget(self.exit_btn)

        # Create QListView to replace the flow layout
        self.listView = ClickableSmoothListView(self)
        QScroller.grabGesture(
            self.listView.viewport(), QScroller.LeftMouseButtonGesture
        )
        self.listView.setViewMode(SmoothListView.IconMode)
        self.listView.setResizeMode(SmoothListView.Adjust)
        self.listView.setMovement(SmoothListView.Static)
        self.listView.setSpacing(12)
        self.listView.setIconSize(
            QSize(128, 128)
        )  # Can update based on user preference
        self.listView.setUniformItemSizes(True)
        self.listView.setSelectionMode(QAbstractItemView.SingleSelection)
        self.listView.setWordWrap(True)
        self.listView.setMouseTracking(True)
        self.listView.setStyleSheet("SmoothListView { background: transparent; }")

        self.listView.viewport().installEventFilter(self)
        self.listView.verticalScrollBar().valueChanged.connect(
            self.update_edit_mode_buttons
        )
        self.listView.horizontalScrollBar().valueChanged.connect(
            self.update_edit_mode_buttons
        )

        main.addWidget(self.toolbar)

        # Set layout policy and add to main layout
        self.listView.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
        main.addWidget(self.listView)

        # Assign model
        self.thumb_model = ThumbnailListModel()
        self.listView.setModel(self.thumb_model)

        # Assign delegate for custom painting
        self.thumb_delegate = ThumbnailDelegate(self)
        self.listView.setItemDelegate(self.thumb_delegate)

        # Connect signals for handling clicks
        self.listView.clicked.connect(self._on_item_clicked)
        self.listView.doubleClicked.connect(self._on_item_double_clicked)
        self.listView.setContextMenuPolicy(Qt.CustomContextMenu)
        self.listView.customContextMenuRequested.connect(self._handle_right_click)
        self.listView.heartClicked.connect(self._toggle_favorite_from_index)

        # --- Force button layout refresh (fix icons too high on launch) ---
        for btn in self.findChildren(QToolButton):
            if btn.toolButtonStyle() == Qt.ToolButtonTextUnderIcon:
                btn.setToolButtonStyle(Qt.ToolButtonIconOnly)
                btn.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)

        # Empty folder message
        self.empty_label = QLabel("No files to display", self)
        self.empty_label.setAlignment(Qt.AlignCenter)
        self.empty_label.setStyleSheet(
            """
            QLabel {
                color: #aaa;
                font-size: 16pt;
                font-weight: bold;
                background-color: transparent;
            }
        """
        )
        self.empty_label.hide()

        # Apply global stylesheet
        self.set_dark_stylesheet()

        self.show_tags = True  # ← default value, changeable by user

        # — Thumbnail loader queue + workers
        self.exts = [
            ".jpg",
            ".jpeg",
            ".png",
            ".bmp",
            ".gif",
            ".webp",
            ".mp4",
            ".avi",
            ".mov",
            ".webm",
            ".pdf",
            ".exe",
        ]
        self._thumb_q = Queue(maxsize=100)  # must be > 0 so initial batch gets queued
        self._thumb_stop = [False]
        # spawn multiple workers
        num_workers = min(8, max(2, os.cpu_count() + 1))
        for _ in range(num_workers):
            worker = ThumbnailWorker(
                self._thumb_q,
                self._thumb_stop,
                show_tags=self.show_tags,
                image_thumb_mode=self.image_thumb_mode,
                thumb_cache_dir=str(self.thumb_cache_dir),
            )
            worker.thumbnailReady.connect(self._onThumb)
            Thread(target=worker.run, daemon=True).start()

        self._pending = []

        # Initial directory load
        self.current_sort_mode = "ascending"
        self.load_directory(self.current_dir)
        self._set_sort_mode("ascending")

        # where to store cached thumbs
        self.thumb_cache_dir = Path(self.app_dir) / ".thumbs_cache"
        self.thumb_cache_dir.mkdir(exist_ok=True)

        # Apply remembered view settings to UI
        self.show_tags = self._initial_show_tags
        self.show_names = self._initial_show_names
        crumb_visible = self._initial_crumb_visible

        self.hide_tags_action.setChecked(not self.show_tags)
        self.hide_names_action.setChecked(not self.show_names)
        self.toggle_crumb_action.setChecked(crumb_visible)

        if hasattr(self, "crumb"):
            self.crumb.setVisible(crumb_visible)

        # Load directory last, now that everything exists
        self.load_directory(self.current_dir)

        # Initialize toolbar visibility
        if not self.toolbar_visible:
            self.toolbar.hide()
            self.restore_toolbar_btn.show()
            self._reposition_restore_button()
            self.toggle_toolbar_action.setChecked(True)
            self.toggle_toolbar_action.setText("Show Toolbar")

    def load_directory(self, path, refresh=False, files=None):
        self.current_directory = path
        self.current_dir = path
        folder_name = os.path.basename(path)
        self.search.setPlaceholderText(f"Search {folder_name}")
        if not refresh:
            self.search.setText("")  # Clear only on full load

        if hasattr(self, "crumb"):
            self.crumb.setText(path)
        self._update_status_labels()

        self.spinner.start()
        self._spinner_timer = QTimer(self)
        self._spinner_timer.setSingleShot(True)
        self._spinner_timer.timeout.connect(self.spinner.stop)
        self._spinner_timer.start(2000)

        # Clear model and pending state
        self.thumb_model.clear()
        self._pending.clear()

        all_names = os.listdir(path)

        folders = [n for n in all_names if os.path.isdir(os.path.join(path, n))]
        if self.hide_folders or self.current_sort_mode == "favorites":
            folders = []

        files_in_dir = [
            n for n in all_names if not os.path.isdir(os.path.join(path, n))
        ]

        # Filter supported media files
        media_files = [
            n for n in files_in_dir if os.path.splitext(n)[1].lower() in self.exts
        ]
        self.media_files = [os.path.join(path, f) for f in media_files]

        # Files to show (including unsupported if allowed)
        files_to_show = media_files
        if not self.hide_unsupported:
            files_to_show = files_in_dir

        # Filtered input overrides normal files
        if files is not None:
            full_input_files = [os.path.basename(f) for f in files]
            files_to_show = [
                f for f in full_input_files if os.path.exists(os.path.join(path, f))
            ]

        # Apply sorting
        if self.current_sort_mode == "ascending":
            sorted_names = sorted(files_to_show, key=str.lower)
        elif self.current_sort_mode == "descending":
            sorted_names = sorted(files_to_show, key=str.lower, reverse=True)
        elif self.current_sort_mode == "random":
            sorted_names = files_to_show[:]
            random.shuffle(sorted_names)
        elif self.current_sort_mode == "favorites":
            sorted_names = [
                f for f in files_to_show if os.path.join(path, f) in self.favorites
            ]
        else:
            sorted_names = files_to_show

        names = folders + sorted_names

        # Final filter if hiding unsupported
        if self.hide_unsupported:
            names = [
                n
                for n in names
                if os.path.isdir(os.path.join(path, n))
                or os.path.splitext(n)[1].lower() in self.exts
            ]

        self.sorted_files = [
            os.path.join(self.current_dir, name)
            for name in names
            if os.path.splitext(name)[1].lower() in self.exts
            or os.path.isdir(os.path.join(path, name))
        ]

        # Clear old folder buttons
        for btns in getattr(self, "folder_buttons", {}).values():
            for btn in btns:
                btn.setParent(None)
        self.folder_buttons = {}

        # Add entries to model
        for name in names:
            full_path = os.path.join(path, name)
            if full_path == self.app_dir:
                continue

            icon = QIcon()
            is_favorite = full_path in self.favorites
            is_folder = os.path.isdir(full_path)

            if is_folder:
                thumb_path = self.folder_thumb_map.get(full_path)
                if thumb_path and os.path.exists(thumb_path):
                    icon = self._create_filled_thumbnail(thumb_path)
                else:
                    icon = self._create_filled_thumbnail(
                        self._get_default_folder_icon()
                    )
            else:
                ext_lower = os.path.splitext(name)[1].lower()
                cache_file = self._thumb_cache_path(full_path)

                if cache_file.exists():
                    icon = QIcon(str(cache_file))
                elif ext_lower == ".exe":
                    icon = self._create_filled_thumbnail("_internal/icons/exe_icon.png")
                elif ext_lower not in self.exts:
                    icon = self._create_filled_thumbnail("_internal/icons/unsupported.png")
                else:
                    self._pending.append(full_path)

            self.thumb_model.addItem(full_path, icon, is_favorite, is_folder)

        self.listView.scrollToTop()
        QTimer.singleShot(0, self._enqueue_next_batch)

        if not self._pending and not self._spinner_timer.isActive():
            self.spinner.stop()

        self._update_back_button()
        self._update_empty_label()

        if self.toolbar_visible:
            self.toolbar.show()
            self.restore_toolbar_btn.hide()
        else:
            self.toolbar.hide()
            self.restore_toolbar_btn.show()
            self._reposition_restore_button()

    def _onThumb(self, path, icon):
        # Save the thumbnail to cache if not already cached
        cache_file = self._thumb_cache_path(path)
        if not cache_file.exists() and not icon.isNull():
            pixmap = icon.pixmap(THUMB_SIZE, THUMB_SIZE)
            if not pixmap.isNull():
                pixmap.save(str(cache_file), "JPG")

        # Update the thumbnail icon in the model
        if not icon.isNull():
            self.thumb_model.update_icon(path, icon)

        # Load next thumbnail
        if self._pending:
            self._thumb_q.put(self._pending.pop(0))

        # If no more pending thumbnails, stop spinner
        if not self._pending:
            if (
                not hasattr(self, "_spinner_timer")
                or not self._spinner_timer.isActive()
            ):
                self.spinner.stop()
            self._update_empty_label()

    def _filterThumbnails(self, text):
        if not hasattr(self, "media_files"):
            return

        if text.strip():
            filtered = [
                f
                for f in self.media_files
                if text.lower() in os.path.basename(f).lower()
            ]
        else:
            filtered = self.media_files

        self.sorted_files = filtered
        self.load_directory(self.current_dir, refresh=True, files=filtered)

    def _on_item_clicked(self, index):
        """Handle single click on thumbnail item"""
        path = self.thumb_model.get_item_path(index)
        if not path:
            return

        if os.path.isdir(path):
            # Folder has a launch control
            if not self.editMode and path in self.folder_launch_map:
                target = self.folder_launch_map[path]
                nm = os.path.basename(target)
                resp = QMessageBox.question(
                    self,
                    "Launch Control",
                    f"Open '{nm}'?",
                    QMessageBox.Yes | QMessageBox.No,
                )
                if resp == QMessageBox.Yes:
                    QDesktopServices.openUrl(QUrl.fromLocalFile(target))
                    return  # Skip loading the folder
            # Otherwise: load the folder normally
            self.spinner.start()
            QTimer.singleShot(0, lambda: self.load_directory(path))
            self.editMode = False
            self.edit_btn.setText("Edit Mode")
            self._update_status_labels()

        else:
            # Handle file click - open in fullscreen viewer
            self.open_fullscreen(path)
            self.editMode = False
            self.edit_btn.setText("Edit Mode")
            self._update_status_labels()

    def _on_item_double_clicked(self, index):
        """Handle double-click: Only open unsupported files externally"""
        path = self.thumb_model.get_item_path(index)
        if not path:
            return

        if os.path.isdir(path):
            self.load_directory(path)
        else:
            ext = os.path.splitext(path)[1].lower()
            if ext not in self.exts:
                # Open unsupported file types externally
                QDesktopServices.openUrl(QUrl.fromLocalFile(path))
            else:
                # Supported file types (images/videos) should not open externally
                self.open_fullscreen(path)

    def _handle_right_click(self, position):
        """Handle right-click in the QListView: go up if clicked on empty space and not at root."""
        if self.current_dir != self.root_dir:
            self._navigate_up()

    def _load_json(self, path):
        try:
            with open(path, "r") as f:
                return json.load(f)
        except:
            return {}

    def _save_json(self, data, path):
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
        except Exception as e:
            print("Failed to save JSON:", e)
    
    def _load_video_cache(self):
        """Load video metadata cache from disk"""
        try:
            self.video_metadata_cache = self._load_json(self.video_cache_file)
        except:
            self.video_metadata_cache = {}
    
    def _save_video_cache(self):
        """Save video metadata cache to disk"""
        try:
            self._save_json(self.video_metadata_cache, self.video_cache_file)
        except Exception as e:
            print(f"Failed to save video cache: {e}")
    
    def _get_video_metadata(self, video_path):
        """Get cached video metadata or generate it"""
        if video_path in self.video_metadata_cache:
            return self.video_metadata_cache[video_path]
        
        # Generate metadata for new video
        try:
            stat = os.stat(video_path)
            metadata = {
                'size': stat.st_size,
                'modified': stat.st_mtime,
                'cached_at': time.time()
            }
            
            # Store in cache
            self.video_metadata_cache[video_path] = metadata
            self._save_video_cache()
            return metadata
        except Exception as e:
            print(f"Failed to get metadata for {video_path}: {e}")
            return {}

    def _on_folder_click(self, folder):
        if not self.editMode and folder in self.folder_launch_map:
            target = self.folder_launch_map[folder]
            nm = os.path.basename(target)
            resp = QMessageBox.question(
                self,
                "Launch Control",
                f"Open '{nm}'?",
                QMessageBox.Yes | QMessageBox.No,
            )
            if resp == QMessageBox.Yes:
                QDesktopServices.openUrl(QUrl.fromLocalFile(target))
        else:
            self.load_directory(folder)

    def _set_launch(self, folder):
        f, _ = QFileDialog.getOpenFileName(
            self, "Select Launch File", folder, "All Files (*)"
        )
        if f:
            self.folder_launch_map[folder] = f
            self._save_json(self.folder_launch_map, self.launch_map_file)
            self.editMode = False  # Exit Edit Mode
            self.edit_btn.setText("Edit Mode")
            self.load_directory(self.current_dir)

    def _remove_launch(self, folder):
        resp = QMessageBox.question(
            self,
            "Remove Launch Control",
            "Remove Launch Control from this folder?",
            QMessageBox.Yes | QMessageBox.No,
        )
        if resp == QMessageBox.Yes:
            self.folder_launch_map.pop(folder, None)
            self._save_json(self.folder_launch_map, self.launch_map_file)
            self.load_directory(self.current_dir)

    def _toggle_folder_launch(self, folder_path):
        if folder_path in self.folder_launch_map:
            self._remove_launch(folder_path)
        else:
            self._set_launch(folder_path)

    def _open_pdf(self, path):
        files = [
            os.path.join(self.current_dir, n)
            for n in sorted(os.listdir(self.current_dir), key=str.lower)
            if os.path.splitext(n)[1].lower() in self.exts
        ]

        self.viewer = FullscreenImageViewer(
            media_path=path,
            pdf_path=path,
            media_list=self.sorted_files,
            slideshowInterval=None,
            randomize=self.rand_btn.isChecked() if hasattr(self, "rand_btn") else False,
            toggle_slideshow_callback=self.toggle_slideshow_mode,
            close_callback=None,
        )
        self.viewer.showFullScreen()

    def toggle_edit_mode(self):
        self.editMode = not self.editMode
        self.edit_btn.setText("Exit Edit Mode" if self.editMode else "Edit Mode")

        # Refresh directory (optional if you want to redraw items, otherwise can skip)
        self.load_directory(self.current_dir)

        # Update folder overlay buttons
        self.update_edit_mode_buttons()

        self._update_status_labels()

    def open_fullscreen(self, path):
        # Use cached media files instead of rescanning directory
        # This eliminates the directory scanning overhead on every video open
        media_files = getattr(self, 'media_files', [])
        if not media_files:
            # Fallback to scanning if cache is empty
            media_files = [
                os.path.join(self.current_dir, n)
                for n in sorted(os.listdir(self.current_dir), key=str.lower)
                if os.path.splitext(n)[1].lower() in self.exts
            ]
        
        self.viewer = FullscreenImageViewer(
            media_path=path,
            pdf_path=path,
            media_list=media_files,  # Use cached media files for faster access
            slideshowInterval=self._lastInterval if self.slideshowActive else None,
            randomize=False,
            toggle_slideshow_callback=self.toggle_slideshow_mode,
            close_callback=self._on_viewer_closed,
        )
        self.viewer.showFullScreen()

    def _on_viewer_closed(self, refresh=False):
        # Ensure viewer is properly cleaned up
        if hasattr(self, 'viewer') and self.viewer:
            # Force stop any remaining media playback
            if hasattr(self.viewer, 'player') and self.viewer.player:
                self.viewer.player.stop()
                self.viewer.player.setMedia(QMediaContent())
            if hasattr(self.viewer, 'movie') and self.viewer.movie:
                self.viewer.movie.stop()
            self.viewer.deleteLater()
        
        self.viewer = None
        if refresh:
            self.load_directory(self.current_dir)

    def toggle_slideshow_mode(self):
        if not self.slideshowActive:
            secs, ok = QInputDialog.getInt(
                None, "Slideshow", "Seconds per slide:", 5, 1, 60
            )
            if not ok:
                return
            self._lastInterval = secs * 1000
            self.slideshowActive = True
            self.slideshow_btn.setText("Stop Slideshow")
        else:
            self.slideshowActive = False
            self.slideshow_btn.setText("Start Slideshow")
            if hasattr(self, "viewer") and self.viewer.slideshowTimer:
                self.viewer.slideshowTimer.stop()
        self._update_status_labels()

    def _show_thumb_choice(self, folder):
        dialog = QDialog(self)
        dialog.setWindowTitle("Change Thumbnail")
        dialog.setModal(True)
        layout = QVBoxLayout(dialog)

        label = QLabel("Choose source:")
        layout.addWidget(label)

        btn_layout = QHBoxLayout()
        layout.addLayout(btn_layout)

        btn_pick = QPushButton("Pick File…")
        btn_auto = QPushButton("Auto‑select First Image")
        btn_reset = QPushButton("Restore Default Thumbnail")
        btn_adjust = QPushButton("Adjust Current Image")
        btn_cancel = QPushButton("Cancel")

        # Add buttons in exact order
        btn_layout.addWidget(btn_pick)
        btn_layout.addWidget(btn_auto)
        btn_layout.addWidget(btn_reset)
        btn_layout.addWidget(btn_adjust)
        btn_layout.addWidget(btn_cancel)

        chosen = {}

        def choose(action):
            chosen["action"] = action
            dialog.accept()

        btn_pick.clicked.connect(lambda: choose("pick"))
        btn_auto.clicked.connect(lambda: choose("auto"))
        btn_reset.clicked.connect(lambda: choose("reset"))
        btn_adjust.clicked.connect(lambda: choose("adjust"))
        btn_cancel.clicked.connect(dialog.reject)

        dialog.exec_()

        if not dialog.result():
            return  # Cancel clicked

        action = chosen.get("action")
        image_path = None

        if action == "auto":
            for n in sorted(os.listdir(folder), key=str.lower):
                if os.path.splitext(n)[1].lower() in [
                    ".jpg",
                    ".jpeg",
                    ".png",
                    ".bmp",
                    ".gif",
                    "webp",
                ]:
                    image_path = os.path.join(folder, n)
                    break
            else:
                QMessageBox.warning(self, "No image", "No image found in that folder.")
                return

        elif action == "pick":
            image_path, _ = QFileDialog.getOpenFileName(
                self,
                "Select Thumbnail",
                "",
                "Images (*.png *.jpg *.jpeg *.bmp *.gif *.webp)",
            )
            if not image_path:
                return

        elif action == "adjust":
            image_path = self.folder_thumb_map.get(folder)
            if not image_path or not os.path.exists(image_path):
                QMessageBox.warning(self, "No Image", "No current image to adjust.")
                return

        elif action == "reset":
            if folder in self.folder_thumb_map:
                del self.folder_thumb_map[folder]
                self._save_thumb_map()
                self.editMode = False
                self.edit_btn.setText("Edit Mode")
                self.load_directory(self.current_dir)
            return

        # Proceed to cropping if image path was selected
        if image_path:

            def on_crop_complete(result_pixmap):
                self._apply_folder_thumbnail(folder, result_pixmap)

            cropper = ImageCropper(image_path, on_crop_complete, parent=self)
            cropper.exec_()

    def openResolutionDialog(self):
        dlg = QDialog(self)
        dlg.setWindowTitle("Select Resolution")
        layout = QVBoxLayout(dlg)
        lst = QListWidget()
        for name in ("Fullscreen (windowed)", "Fullscreen"):
            lst.addItem(name)
        layout.addWidget(lst)
        bb = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        bb.accepted.connect(dlg.accept)
        bb.rejected.connect(dlg.reject)
        layout.addWidget(bb)

        if dlg.exec_() == QDialog.Accepted:
            sel = lst.currentItem().text()
            if sel.startswith("Fullscreen (windowed)"):
                self.setMinimumSize(640, 480)
                self.setMaximumSize(16777215, 16777215)
                self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
                self.showNormal()
                self.showMaximized()
            else:
                self.showFullScreen()

    def confirmExit(self):
        if (
            QMessageBox.question(
                self, "Exit?", "Quit application?", QMessageBox.Yes | QMessageBox.No
            )
            == QMessageBox.Yes
        ):
            self.close()

    def openThumbnailSizeDialog(self):
        dlg = QDialog(self)
        dlg.setWindowTitle("Thumbnail Size")
        layout = QVBoxLayout(dlg)
        lst = QListWidget()
        size_options = {"Small": 175, "Medium": 250, "Large": 388, "Very Large": 450}
        for label in size_options:
            lst.addItem(label)
        layout.addWidget(lst)
        bb = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        bb.accepted.connect(dlg.accept)
        bb.rejected.connect(dlg.reject)
        layout.addWidget(bb)

        if dlg.exec_() == QDialog.Accepted:
            label = lst.currentItem().text()
            global THUMB_SIZE
            THUMB_SIZE = size_options[label]

            # Clear old thumbnail cache files so they regenerate at new size
            try:
                for f in self.thumb_cache_dir.glob("*.jpg"):
                    f.unlink()
            except Exception:
                pass

            self.load_directory(self.current_dir)

    def openAbout(self):
        QMessageBox.information(
            self,
            "About Media Explorer",
            "Media Explorer\n"
            "Version 1.0 · 2025\n"
            "Website: fastfiletools.com\n\n"
            "Media Explorer is a fast, lightweight desktop app for browsing, viewing, "
            "and organizing media files. It supports images, videos, GIFs, PDFs, and more — "
            "all with smooth thumbnail previews and fullscreen playback.\n\n"
            "Key features include:\n"
            "- Edit Mode for customizing folder names and thumbnails\n"
            "- Favorites with one-click heart tagging\n"
            "- Custom folder thumbnail support\n"
            "- Fullscreen viewing with zoom, pan, and arrow key navigation\n"
            "- Smart sorting and multiple view modes\n\n"
            "For updates, tools, and support, visit: fastfiletools.com"
        )

    def keyPressEvent(self, e):
        if e.key() == Qt.Key_Escape and self.current_dir != self.root_dir:
            self.load_directory(os.path.dirname(self.current_dir))
        else:
            super().keyPressEvent(e)

    def mousePressEvent(self, e):
        if e.button() == Qt.RightButton and self.current_dir != self.root_dir:
            self.load_directory(os.path.dirname(self.current_dir))
        else:
            super().mousePressEvent(e)

    def closeEvent(self, event):
        self.settings["show_names"] = self.show_names
        self.settings["show_tags"] = self.show_tags
        self.settings["breadcrumb_visible"] = self.breadcrumb_visible
        self.settings["toolbar_visible"] = self.toolbar_visible
        self._save_json(self.settings, self.settings_file)
        
        # Save video metadata cache
        self._save_video_cache()
        event.accept()

    def _thumb_cache_path(self, path: str) -> Path:
        h = hashlib.md5(path.encode("utf-8")).hexdigest()
        return self.thumb_cache_dir / f"{h}_hq.jpg"  # Note the _hq suffix

    def _toggleNameLabels(self, state):
        self.show_names = bool(state)
        for lbl in self._name_labels:
            lbl.setVisible(self.show_names)

    def _toggle_breadcrumb_visibility(self, checked):
        self.breadcrumb_visible = checked
        self.crumb.setVisible(checked)
        self.toggle_crumb_action.setText(
            "Show Breadcrumb Bar" if not checked else "Hide Breadcrumb Bar"
        )
        self._save_view_settings()

    def _default_file_icon(self, ext: str, filename: str = "") -> QIcon:
        """
        Draw a thumbnail for unsupported files using a custom icon that fills the entire thumbnail area,
        and overlays the filename at the top-center in white Impact font.
        """
        if ext.lower() == ".exe":
            return self._create_exe_thumbnail(filename)

        # Create a QPixmap for the thumbnail (transparent or dark background)
        pixmap = QPixmap(THUMB_SIZE, THUMB_SIZE)
        pixmap.fill(Qt.transparent)

        painter = QPainter(pixmap)
        painter.setRenderHint(QPainter.Antialiasing)

        # Load and scale the PNG icon to fill the entire thumbnail
        png_path = "_internal/icons/unsupported.png"
        icon_img = QPixmap(png_path).scaled(
            THUMB_SIZE,
            THUMB_SIZE,
            Qt.KeepAspectRatioByExpanding,
            Qt.SmoothTransformation,
        )
        # Draw the icon centered and fully sized
        painter.drawPixmap(0, 0, icon_img)

        # Draw the filename at the top-center
        if filename:
            font = QFont("Impact", 28)
            if not font.exactMatch():
                font = QFont()
                font.setBold(True)
                font.setPointSize(28)
            painter.setFont(font)
            metrics = painter.fontMetrics()
            text = os.path.basename(filename)
            max_width = THUMB_SIZE - 24
            # Truncate with ellipsis if too long
            if metrics.width(text) > max_width:
                text = metrics.elidedText(text, Qt.ElideRight, max_width)
            x = (THUMB_SIZE - metrics.width(text)) // 2
            y = metrics.ascent() + 10
            # Draw black outline for contrast
            painter.setPen(QPen(Qt.black, 4))
            painter.drawText(x, y, text)
            # Draw white text
            painter.setPen(Qt.white)
            painter.drawText(x, y, text)
        painter.end()
        return QIcon(pixmap)

    def _create_exe_thumbnail(self, filename: str) -> QIcon:
        """Create a full-size .exe thumbnail with the filename at the top-center in white Impact font."""
        exe_icon = QPixmap("_internal/icons/exe_icon.png").scaled(
            THUMB_SIZE,
            THUMB_SIZE,
            Qt.IgnoreAspectRatio,  # Force stretch to fill
            Qt.SmoothTransformation,
        )
        pixmap = QPixmap(THUMB_SIZE, THUMB_SIZE)
        pixmap.fill(Qt.transparent)
        painter = QPainter(pixmap)
        painter.setRenderHint(QPainter.Antialiasing)
        painter.drawPixmap(0, 0, exe_icon)
        # Draw the filename at the top-center
        if filename:
            font = QFont("Impact", 32)
            if not font.exactMatch():
                font = QFont()
                font.setBold(True)
                font.setPointSize(28)
            painter.setFont(font)
            metrics = painter.fontMetrics()
            text = os.path.basename(filename)
            max_width = THUMB_SIZE - 24
            if metrics.width(text) > max_width:
                text = metrics.elidedText(text, Qt.ElideRight, max_width)
            x = (THUMB_SIZE - metrics.width(text)) // 2
            y = metrics.ascent() + 10
            painter.setPen(QPen(Qt.black, 4))
            painter.drawText(x, y, text)
            painter.setPen(Qt.white)
            painter.drawText(x, y, text)
        painter.end()
        return QIcon(pixmap)

    def _update_random_mode_status(self, checked):
        self.rand_btn.setText("Disable Random" if checked else "Random")
        self._update_status_labels()

    def _update_status_labels(self):
        parts = []

        if self.slideshowActive:
            parts.append("Slideshow Mode Active")
        if self.editMode:
            parts.append("Edit Mode Active")

        text = " - " + " - ".join(parts) if parts else ""
        # self.slideshowLabel.setText(text)

    def clear_thumbnail_cache(self):
        reply = QMessageBox.question(
            self,
            "Clear Thumbnail Cache?",
            "Delete all file thumbnails from the thumbnail cache?\n"
            "This may increase the loading times of opening folders for the first time.",
            QMessageBox.Yes | QMessageBox.No,
            QMessageBox.No,
        )
        if reply == QMessageBox.Yes:
            # delete every .jpg in your cache folder
            try:
                for f in self.thumb_cache_dir.glob("*.jpg"):
                    f.unlink()
            except Exception as e:
                QMessageBox.warning(self, "Error", f"Could not clear cache:\n{e}")
            else:
                QMessageBox.information(
                    self,
                    "Thumbnail Cache Cleared",
                    "All file thumbnails have been deleted.",
                )

    def toggle_hide_unsupported(self, hide: bool):
        """
        Called when the user checks/unchecks "Hide Unsupported Files".
        We store the choice, swap the menu text, and refresh the view.
        """
        self.hide_unsupported = hide
        # Flip the menu wording
        self.hideUnsupportedAction.setText(
            "Unhide Unsupported Files" if hide else "Hide Unsupported Files"
        )
        # Reload to apply the new filter
        self.load_directory(self.current_dir)
        self.toolbar.repaint()
        self.repaint()

    def toggle_theme(self):
        self.is_dark_mode = not self.is_dark_mode  # ← add this line

        if self.is_dark_mode:
            self.set_dark_stylesheet()
            self.theme_action.setText("Light Mode")
        else:
            self.set_light_stylesheet()
            self.theme_action.setText("Dark Mode")

        self.load_directory(self.current_dir)

    def set_dark_stylesheet(self):
        """Set dark theme stylesheet"""
        self.setStyleSheet(
            """
            QWidget {
                background-color: #1e1e1e;
                color: White;
            }
            QToolButton {
                color: white;
                background: transparent;
                border: none;
            }
            QToolButton:hover {
                background-color: rgba(255, 255, 255, 10%);
            }
            QMenu {
                background-color: #2d2d2d;
                color: white;
            }
            QMenu::item:selected {
                background-color: #3d3d3d;
            }
            QLineEdit {
                background-color: #2d2d2d;
                color: white;
                border: 1px solid #3d3d3d;
                border-radius: 4px;
                padding: 4px;
            }
            QPushButton {
                background-color: #2d2d2d;
                color: white;
                border: 1px solid #3d3d3d;
                border-radius: 4px;
                padding: 4px;
            }
            QPushButton:hover {
                background-color: #3d3d3d;
            }
        """
        )

        # 🔄 Restore dark icons
        self.gear.setIcon(QIcon("_internal/icons/settings.svg"))
        self.view_btn.setIcon(QIcon("_internal/icons/view.svg"))
        self.edit_btn.setIcon(QIcon("_internal/icons/edit_mode.svg"))
        self.import_files_btn.setIcon(QIcon("_internal/icons/import.svg"))
        self.new_folder_btn.setIcon(QIcon("_internal/icons/folder_add.svg"))
        self.exit_btn.setIcon(QIcon("_internal/icons/exit.svg"))
        self.reload_thumbs_btn.setIcon(QIcon("_internal/icons/refresh_dark.svg"))
        self.overlay_group_btn.setIcon(QIcon("_internal/icons/overlay_dark.svg"))
        self.home_btn.setIcon(QIcon("_internal/icons/home_dark.svg"))

        # Update logo
        self.logo_label.setPixmap(
            self.logo_pixmap_dark.scaled(
                280, 80, Qt.KeepAspectRatio, Qt.SmoothTransformation
            )
        )

        self.sort_buttons["ascending"].setIcon(QIcon("_internal/icons/sort_asc.svg"))
        self.sort_buttons["descending"].setIcon(QIcon("_internal/icons/sort_desc.svg"))
        self.sort_buttons["random"].setIcon(QIcon("_internal/icons/sort_random.svg"))
        self.sort_buttons["favorites"].setIcon(QIcon("_internal/icons/heart_filter.svg"))
        self._update_back_button()
        self.update_toolbar_theme()

    def set_light_stylesheet(self):
        """Set light theme stylesheet"""
        self.setStyleSheet(
            """
            QWidget {
                background-color: #F2F4F7;
                color: black;
            }
            QToolButton {
                color: black;
                background: transparent;
                border: none;
            }
            QToolButton:hover {
                background-color: rgba(0, 0, 0, 10%);
            }
            QMenu {
                background-color: #ffffff;
                color: black;
            }
            QMenu::item:selected {
                background-color: #e0e0e0;
            }
            QLineEdit {
                background-color: #ffffff;
                color: black;
                border: 1px solid #cccccc;
                border-radius: 4px;
                padding: 4px;
            }
            QPushButton {
                background-color: #ffffff;
                color: black;
                border: 1px solid #cccccc;
                border-radius: 4px;
                padding: 4px;
            }
            QPushButton:hover {
                background-color: #e0e0e0;
            }
        """
        )
        # 🔄 Set light icons for toolbar buttons
        self.gear.setIcon(QIcon("_internal/icons/settings_light.svg"))
        self.view_btn.setIcon(QIcon("_internal/icons/view_light.svg"))
        self.edit_btn.setIcon(QIcon("_internal/icons/edit_mode_light.svg"))
        self.import_files_btn.setIcon(QIcon("_internal/icons/import_light.svg"))
        self.new_folder_btn.setIcon(QIcon("_internal/icons/folder_add_light.svg"))
        self.exit_btn.setIcon(QIcon("_internal/icons/exit_light.svg"))
        self.reload_thumbs_btn.setIcon(QIcon("_internal/icons/refresh_light.svg"))
        self.overlay_group_btn.setIcon(QIcon("_internal/icons/overlay_light.svg"))
        self.home_btn.setIcon(QIcon("_internal/icons/home_light.svg"))

        # Update logo
        self.logo_label.setPixmap(
            self.logo_pixmap_light.scaled(
                280, 80, Qt.KeepAspectRatio, Qt.SmoothTransformation
            )
        )

        self.sort_buttons["ascending"].setIcon(QIcon("_internal/icons/sort_asc_light.svg"))
        self.sort_buttons["descending"].setIcon(QIcon("_internal/icons/sort_desc_light.svg"))
        self.sort_buttons["random"].setIcon(QIcon("_internal/icons/sort_random_light.svg"))
        self.sort_buttons["favorites"].setIcon(
            QIcon("_internal/icons/heart_filter_light.svg")
        )  # Keep same icon for favorites
        self._update_back_button()
        self.back_btn.repaint()
        self.update_toolbar_theme()

    def _get_default_folder_icon(self):
        return "_internal/icons/default_folder_dark.png"

    def _set_sort_mode(self, mode):
        self.current_sort_mode = mode

        # Update sort button highlighting for all buttons
        for m, btn in self.sort_buttons.items():
            bg = "rgba(255, 255, 255, 60)" if m == mode else "rgba(255, 255, 255, 20)"
            btn.setStyleSheet(
                f"""
                QToolButton {{
                    background-color: {bg};
                    border: none;
                    border-radius: 4px;
                }}
                QToolButton:hover {{
                    background-color: rgba(255, 255, 255, 40);
                }}
            """
            )

        # Reload directory with new sort mode
        self.load_directory(self.current_dir)

    def toggle_filenames(self, checked):
        self.show_names = not checked
        # Reload to update the display
        self.load_directory(self.current_dir)

    def _rename_folder(self, folder_path):
        current_name = os.path.basename(folder_path)
        parent_dir = os.path.dirname(folder_path)

        new_name, ok = QInputDialog.getText(
            self, "Rename Folder", "Enter new folder name:", text=current_name
        )
        if ok and new_name and new_name != current_name:
            new_path = os.path.join(parent_dir, new_name)
            if os.path.exists(new_path):
                QMessageBox.warning(
                    self, "Error", "A folder with that name already exists."
                )
                return
            try:
                os.rename(folder_path, new_path)
                # Update thumbnail/launch mappings if they exist
                if folder_path in self.folder_thumb_map:
                    self.folder_thumb_map[new_path] = self.folder_thumb_map.pop(
                        folder_path
                    )
                if folder_path in self.folder_launch_map:
                    self.folder_launch_map[new_path] = self.folder_launch_map.pop(
                        folder_path
                    )

                self._save_json(self.thumb_map_file, self.folder_thumb_map)
                self._save_json(self.launch_map_file, self.folder_launch_map)
                self.load_directory(self.current_dir)  # Refresh view
                # Exit edit mode after rename
                self.editMode = False
                self.edit_btn.setText("Edit Mode")
            except Exception as e:
                QMessageBox.critical(
                    self, "Rename Failed", f"Could not rename folder:\n{str(e)}"
                )

    def _create_new_folder(self):
        """Prompt user to create a new folder in the current directory."""
        confirm = QMessageBox.question(
            self,
            "Create Folder",
            "Create New Folder?",
            QMessageBox.Yes | QMessageBox.No,
        )
        if confirm == QMessageBox.Yes:
            base_name = "New Folder"
            i = 1
            while True:
                folder_name = f"{base_name} {i}"
                folder_path = os.path.join(self.current_dir, folder_name)
                if not os.path.exists(folder_path):
                    try:
                        os.mkdir(folder_path)
                        self.load_directory(self.current_dir)
                    except Exception as e:
                        QMessageBox.critical(
                            self, "Error", f"Failed to create folder:\n{e}"
                        )
                    break
                i += 1

    def _import_files(self):
        """Allow user to import files into the current directory."""
        files, _ = QFileDialog.getOpenFileNames(
            self, "Import Files", "", "All Files (*)"
        )
        if files:
            for file_path in files:
                try:
                    dest_path = os.path.join(
                        self.current_dir, os.path.basename(file_path)
                    )
                    shutil.copy(file_path, dest_path)
                except Exception as e:
                    QMessageBox.critical(self, "Error", f"Failed to import file:\n{e}")
            self.load_directory(self.current_dir)

    def _delete_folder(self, folder_path):
        """Delete the given folder after confirmation."""
        folder_name = os.path.basename(folder_path)
        reply = QMessageBox.warning(
            self,
            "Delete Folder",
            f'This will delete "{folder_name}" from your computer.\n\n'
            "This cannot be undone.\n\nAre you sure you want to delete this folder?",
            QMessageBox.Yes | QMessageBox.No,
        )
        if reply == QMessageBox.Yes:
            try:
                shutil.rmtree(folder_path)
                self.load_directory(self.current_dir)
            except Exception as e:
                QMessageBox.critical(self, "Error", f"Failed to delete folder:\n{e}")

    def _get_sorted_files(self):
        return self.sorted_files if hasattr(self, "sorted_files") else self.media_files

    def _resort_items(self):
        self.sorted_files = self._sort_file_list(self.media_files)
        self._reload_thumbnails()

    def _reload_thumbnails(self):
        self.load_directory(self.current_dir)

    def _sort_file_list(self, files):
        if self.current_sort_mode == "ascending":
            return sorted(files, key=str.lower)
        elif self.current_sort_mode == "descending":
            return sorted(files, key=str.lower, reverse=True)
        elif self.current_sort_mode == "random":
            shuffled = list(files)
            random.shuffle(shuffled)
            return shuffled
        return files

    def _enqueue_next_batch(self, batch_size=8):
        for _ in range(batch_size):
            if self._pending:
                self._thumb_q.put(self._pending.pop(0))

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._reposition_restore_button()

        if hasattr(self, "edit_btn") and self.edit_btn.isVisible():
            # Map edit_btn position to main window coordinates
            global_pos = self.edit_btn.mapToGlobal(QPoint(0, 0))
            local_pos = self.mapFromGlobal(global_pos)

            x = local_pos.x() + self.edit_btn.width() + 10
            if hasattr(self, "spinner"):
                y = (
                    local_pos.y()
                    + (self.edit_btn.height() - self.spinner.height()) // 2
                )
                self.spinner.move(x, y)
            self.spinner.move(x, y)

        # Update empty label position when window is resized
        if hasattr(self, "empty_label") and hasattr(self, "current_dir"):
            self._update_empty_label()

    def _toggle_toolbar(self, checked):
        self.toolbar_visible = not checked
        self.toolbar.setVisible(self.toolbar_visible)
        self.restore_toolbar_btn.setVisible(checked)
        if checked:
            self._reposition_restore_button()
        # Save the setting
        self.settings["toolbar_visible"] = self.toolbar_visible
        self._save_json(self.settings, self.settings_file)

    # Sync checkmark with visibility if user toggles toolbar elsewhere
    def _update_toolbar_toggle_label(self):
        visible = self.toolbar.isVisible()
        self.toggle_toolbar_action.setChecked(not visible)
        self.toggle_toolbar_action.setText(
            "Show Toolbar" if not visible else "Hide Toolbar"
        )

    def _show_toolbar_from_button(self):
        self.toolbar_visible = True
        self.toolbar.setVisible(True)
        self.restore_toolbar_btn.hide()
        self.toggle_toolbar_action.setText("Hide Toolbar")
        self.toggle_toolbar_action.setChecked(False)
        # Save the setting
        self.settings["toolbar_visible"] = self.toolbar_visible
        self._save_json(self.settings, self.settings_file)

    def _reposition_restore_button(self):
        margin = 20
        x = self.width() - self.restore_toolbar_btn.width() - margin
        y = self.height() - self.restore_toolbar_btn.height() - margin
        self.restore_toolbar_btn.move(x, y)
        self.restore_toolbar_btn.raise_()  # Ensure it's on top after moving

    def _navigate_up(self):
        if self.current_dir != self.root_dir:
            parent = os.path.dirname(self.current_dir)
            self.load_directory(parent)
            self._set_sort_mode("ascending")
        self._update_back_button()

    def _update_back_button(self):
        """
        Updates the back button state and icon based on current directory and theme.
        """
        at_root = self.current_dir == self.root_dir

        if self.is_dark_mode:
            if at_root:
                self.back_btn.setIcon(QIcon("_internal/icons/back_disabled.svg"))
            else:
                self.back_btn.setIcon(QIcon("_internal/icons/back.svg"))
        else:
            if at_root:
                self.back_btn.setIcon(QIcon("_internal/icons/back_disabled.svg"))
            else:
                self.back_btn.setIcon(QIcon("_internal/icons/back_light.svg"))

        self.back_btn.setEnabled(not at_root)

    def toggle_file_tags(self, checked):
        self._show_spinner_for(2000)
        self.show_tags = not checked  # checkbox says "Hide", so inverse
        self.load_directory(self.current_dir)

        # Wait for threads to stop before recreating
        QTimer.singleShot(100, self._restart_thumbnail_workers)
        self.load_directory(self.current_dir)

    def _toggle_folder_names(self, checked):
        self._show_spinner_for(2000)
        self.hide_folder_names = checked
        self.show_folder_names = not checked
        self.settings["hide_folder_names"] = checked
        self._save_json(self.settings, self.settings_file)
        # Reload to update the display
        self.load_directory(self.current_dir)

    def _toggle_folder_overlay(self, checked):
        self._show_spinner_for(2000)
        self.hide_folder_overlay_icon = checked
        self.settings["hide_folder_overlay_icon"] = checked
        self._save_json(self.settings, self.settings_file)
        self.load_directory(self.current_dir)

    def _restart_thumbnail_workers(self):
        self._thumb_stop[0] = False
        for _ in range(3):
            worker = ThumbnailWorker(
                self._thumb_q,
                self._thumb_stop,
                show_tags=self.show_tags,
                image_thumb_mode=self.image_thumb_mode,
                thumb_cache_dir=str(self.thumb_cache_dir),
            )
            worker.thumbnailReady.connect(self._onThumb)
            Thread(target=worker.run, daemon=True).start()

    def _toggle_favorite(self, path, btn):
        if path in self.favorites:
            self.favorites.pop(path, None)
            new_state = False
        else:
            self.favorites[path] = True
            new_state = True
        
        # Update model if the item exists
        model = self.thumb_model
        for row in range(model.rowCount()):
            index = model.index(row, 0)
            item_data = index.data(Qt.UserRole)
            if item_data and item_data[0] == path:
                path, icon, is_favorite, is_folder = item_data
                model.setData(index, (path, icon, new_state, is_folder), Qt.UserRole)
                break
        
        self._save_json(self.favorites, self.favorites_file)
        
        if self.current_sort_mode == "favorites":
            self.load_directory(self.current_dir, refresh=True)

    def _toggle_favorite_from_index(self, index):
        if not index.isValid():
            return

        path, icon, is_favorite, is_folder = index.data(Qt.UserRole)
        
        # Toggle favorite status
        if path in self.favorites:
            self.favorites.discard(path)
            new_status = False
        else:
            self.favorites.add(path)
            new_status = True

        # Update the model
        self.thumb_model.update_favorite(path, new_status)
        
        # Save changes
        self._save_favorites()
        
        # Force immediate repaint of the item
        self.listView.viewport().update()

    def _save_favorites(self):
        try:
            with open(self.favorites_file, "w") as f:
                json.dump(list(self.favorites), f)
        except Exception as e:
            print(f"Error saving favorites: {e}")

    def _update_empty_label(self):
        """Update the empty label position and visibility"""
        # Check if there are any items in the model
        has_items = self.thumb_model.rowCount() > 0

        if not has_items and hasattr(self, "current_dir"):
            # Set appropriate text based on current sort mode
            if self.current_sort_mode == "favorites":
                self.empty_label.setText("No Favorites to Display")
            else:
                self.empty_label.setText("No Files to Display")

            # Position the empty label in the center of the list view
            self.empty_label.setParent(self.listView.viewport())
            self.empty_label.setGeometry(
                (self.listView.viewport().width() - 300) // 2,
                (self.listView.viewport().height() - 50) // 2,
                300,
                50,
            )
            self.empty_label.show()
        else:
            self.empty_label.hide()

    def _load_view_settings(self):
        try:
            with open(self.settings_file, "r") as f:
                settings = json.load(f)
        except Exception:
            settings = {}

        # Just store settings — don't trigger UI yet
        self._initial_show_tags = settings.get("show_tags", True)
        self._initial_show_names = settings.get("show_names", True)
        self._initial_crumb_visible = settings.get("breadcrumb_visible", False)

    def _save_view_settings(self):
        settings = {
            "show_tags": self.show_tags,
            "show_names": self.show_names,
            "breadcrumb_visible": self.toggle_crumb_action.isChecked(),
        }
        try:
            with open(self.settings_file, "w") as f:
                json.dump(settings, f, indent=2)
        except Exception as e:
            print("Failed to save view settings:", e)

    def _print_pdf(self):
        """Print the current PDF page using QPrinter and QPainter."""
        if not hasattr(self, "doc") or not self.doc:
            QMessageBox.warning(self, "Print PDF", "No PDF loaded.")
            return
        try:
            from PyQt5.QtPrintSupport import QPrinter, QPrintDialog
            from PyQt5.QtGui import QPainter, QImage
            import fitz
        except ImportError:
            QMessageBox.critical(
                self, "Print PDF", "Required modules for printing are missing."
            )
            return

        printer = QPrinter(QPrinter.HighResolution)
        dialog = QPrintDialog(printer, self)
        if dialog.exec_() != QPrintDialog.Accepted:
            return

        # Render the current page to a QImage
        page = self.doc[self.page_index] if hasattr(self, "page_index") else self.doc[0]
        rect = page.rect
        # Render at printer resolution
        dpi = printer.resolution()
        scale = dpi / 72.0  # PDF points are 1/72 inch
        mat = fitz.Matrix(scale, scale)
        pix = page.get_pixmap(matrix=mat, alpha=False)
        image = QImage(
            pix.samples, pix.width, pix.height, pix.stride, QImage.Format_RGB888
        )

        painter = QPainter(printer)
        # Center the image on the page
        page_rect = printer.pageRect()
        img_rect = image.rect()
        img_rect.moveCenter(page_rect.center())
        painter.drawImage(img_rect, image)
        painter.end()

    def _set_folder_overlay_position(self, position):
        self.folder_overlay_position = position
        self.settings["folder_overlay_position"] = position
        self._save_json(self.settings, self.settings_file)

        # Update checkmarks
        for p, act in self.overlay_position_actions.items():
            act.setChecked(p == position)

        self.load_directory(self.current_dir)

    def _toggle_hide_folders(self, checked):
        self._show_spinner_for(2000)
        self.hide_folders = checked
        self.settings["hide_folders"] = checked
        self._save_json(self.settings, self.settings_file)
        self.load_directory(self.current_dir)

    def _toggle_launch_icon_visibility(self):
        self._show_spinner_for(2000)
        self.hide_launch_icon = self.toggle_launch_icon_action.isChecked()
        self.load_directory(self.current_dir)  # Refresh to show/hide icons

    def _create_filled_thumbnail(self, path):
        """Create a thumbnail that fills the entire area while maintaining aspect ratio."""
        try:
            pix = QPixmap(path).scaled(
                THUMB_SIZE,
                THUMB_SIZE,
                Qt.KeepAspectRatioByExpanding,
                Qt.SmoothTransformation,
            )
            # Create a new pixmap and paint the scaled image centered
            final_pix = QPixmap(THUMB_SIZE, THUMB_SIZE)
            final_pix.fill(Qt.transparent)
            painter = QPainter(final_pix)
            painter.setRenderHint(QPainter.SmoothPixmapTransform)
            # Calculate position to center the image
            x = (THUMB_SIZE - pix.width()) // 2 if pix.width() < THUMB_SIZE else 0
            y = (THUMB_SIZE - pix.height()) // 2 if pix.height() < THUMB_SIZE else 0
            painter.drawPixmap(x, y, pix)
            painter.end()
            return QIcon(final_pix)
        except:
            # Fallback to empty icon if something goes wrong
            return QIcon()

    def _set_folder_thumbnail(self, folder: str, pixmap: QPixmap):
        thumb_path = os.path.join(
            self.thumb_cache_dir,
            f"folder_{hashlib.md5(pixmap.toImage().bits()).hexdigest()}.png",
        )
        pixmap.save(thumb_path)
        self.folder_thumb_map[folder] = thumb_path
        self._save_thumb_map()
        self.load_directory(self.current_dir)

    def _apply_folder_thumbnail(self, folder_path, pixmap):
        try:
            if not pixmap or pixmap.isNull():
                raise ValueError("Invalid or empty pixmap provided")

            dest_dir = Path(self.thumb_cache_dir)
            dest_dir.mkdir(parents=True, exist_ok=True)
            filename = f"thumb_{abs(hash(folder_path))}.png"
            dest_path = dest_dir / filename
            pixmap.save(str(dest_path), "PNG")

            self.folder_thumb_map[folder_path] = str(dest_path)
            self._save_thumb_map()
            self.load_directory(self.current_dir)
            self.editMode = False
            self.edit_btn.setText("Edit Mode")
            self._update_status_labels()
            self.update_edit_mode_buttons()
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to save thumbnail:\n{str(e)}")

    def _choose_folder_thumbnail(self, folder_path):
        image_path = self._show_thumb_choice(folder_path)

        if not image_path:
            return

        def on_crop_complete(result_pixmap):
            self._apply_folder_thumbnail(folder_path, result_pixmap)

        cropper = ImageCropper(image_path, on_crop_complete, parent=self)
        cropper.exec_()
        self.editMode = False

    def _save_thumb_map(self):
        """Save the folder thumbnail map to disk."""
        if hasattr(self, "folder_thumb_map") and hasattr(self, "thumb_map_file"):
            self._save_json(self.folder_thumb_map, self.thumb_map_file)

    def _reload_thumbnails(self):
        """Clear and reload all thumbnails in the current directory."""
        if not self.current_dir:
            return

        # Stop old workers
        self._thumb_stop[0] = True
        time.sleep(0.2)

        # Clear the cache folder to force regeneration
        try:
            for f in self.thumb_cache_dir.glob("*.jpg"):
                f.unlink()
        except Exception:
            pass

        # Reset queue and stop flag
        self._thumb_q = Queue(maxsize=500)
        self._thumb_stop = [False]

        # Start new workers
        for _ in range(3):
            worker = ThumbnailWorker(
                self._thumb_q,
                self._thumb_stop,
                show_tags=self.show_tags,
                image_thumb_mode=self.image_thumb_mode,
                thumb_cache_dir=str(self.thumb_cache_dir),
            )
            worker.thumbnailReady.connect(self._onThumb)
            Thread(target=worker.run, daemon=True).start()

        # Clear pending list
        self._pending.clear()

        # Reload directory content
        self.load_directory(self.current_dir)

    def _show_image_thumb_options_dialog(self):
        dialog = QDialog(self)
        dialog.setWindowTitle("Image Thumbnail Options")

        layout = QVBoxLayout(dialog)
        layout.setContentsMargins(15, 15, 15, 15)

        radio_group = QButtonGroup(dialog)
        zoom_radio = QRadioButton("Zoom Image Thumbnails")
        show_entire_radio = QRadioButton("Show Entire Image")
        stretch_radio = QRadioButton("Stretch Image to Fit")

        # Load saved setting
        mode = self.image_thumb_mode
        if mode == "stretch":
            stretch_radio.setChecked(True)
        elif mode == "fit":
            show_entire_radio.setChecked(True)
        else:
            zoom_radio.setChecked(True)

        radio_group.addButton(zoom_radio)
        radio_group.addButton(show_entire_radio)
        radio_group.addButton(stretch_radio)

        layout.addWidget(zoom_radio)
        layout.addWidget(show_entire_radio)
        layout.addWidget(stretch_radio)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        layout.addWidget(buttons)
        buttons.accepted.connect(dialog.accept)
        buttons.rejected.connect(dialog.reject)

        if dialog.exec_() == QDialog.Accepted:
            if zoom_radio.isChecked():
                self.image_thumb_mode = "zoom"
            elif show_entire_radio.isChecked():
                self.image_thumb_mode = "fit"
            elif stretch_radio.isChecked():
                self.image_thumb_mode = "stretch"

            # Save setting
            self.settings["image_thumb_mode"] = self.image_thumb_mode
            self._save_json(self.settings, self.settings_file)

            # Clear thumbnail cache and reload
            self._reload_thumbnails()

    def toggle_file_title_placement(self, checked):
        self._show_spinner_for(2000)
        self.file_title_placement = "top" if checked else "bottom"
        self.settings["file_title_placement"] = self.file_title_placement
        self._save_json(self.settings, self.settings_file)
        self.listView.viewport().update()

    def toggle_folder_title_placement(self, checked):
        self._show_spinner_for(2000)
        self.folder_title_placement = "top" if checked else "bottom"
        self.settings["folder_title_placement"] = self.folder_title_placement
        self._save_json(self.settings, self.settings_file)
        self.listView.viewport().update()

    def show_title_background_options_dialog(self):
        dialog = QDialog(self)
        dialog.setWindowTitle("Title Background Options")
        layout = QHBoxLayout(dialog)

        # Folder options
        folder_group = QGroupBox("Folder Titles")
        folder_layout = QVBoxLayout(folder_group)
        folder_buttons = {}

        for mode in ["default", "short", "none"]:
            label = mode.capitalize() + " Background"
            btn = QRadioButton(label)
            btn.setChecked(self.folder_title_bg_mode == mode)
            folder_buttons[mode] = btn
            folder_layout.addWidget(btn)

        # File options
        file_group = QGroupBox("File Titles")
        file_layout = QVBoxLayout(file_group)
        file_buttons = {}

        for mode in ["default", "short", "none"]:
            label = mode.capitalize() + " Background"
            btn = QRadioButton(label)
            btn.setChecked(self.file_title_bg_mode == mode)
            file_buttons[mode] = btn
            file_layout.addWidget(btn)

        layout.addWidget(folder_group)
        layout.addWidget(file_group)

        # Save + Cancel
        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        layout.addWidget(buttons)

        buttons.accepted.connect(dialog.accept)
        buttons.rejected.connect(dialog.reject)

        if dialog.exec_() == QDialog.Accepted:
            for mode, btn in folder_buttons.items():
                if btn.isChecked():
                    self.folder_title_bg_mode = mode
                    self.settings["folder_title_bg_mode"] = mode
                    break

            for mode, btn in file_buttons.items():
                if btn.isChecked():
                    self.file_title_bg_mode = mode
                    self.settings["file_title_bg_mode"] = mode
                    break

            self._save_json(self.settings, self.settings_file)
            self.listView.viewport().update()  # Trigger repaint

    def update_edit_mode_buttons(self):
        if not self.editMode:
            for btns in getattr(self, "folder_buttons", {}).values():
                for btn in btns:
                    btn.hide()
            return

        if not hasattr(self, "folder_buttons"):
            self.folder_buttons = {}

        viewport_rect = self.listView.viewport().rect()
        model = self.thumb_model

        for row in range(model.rowCount()):
            index = model.index(row)
            item_data = index.data(Qt.UserRole)
            if not item_data:
                continue

            path, icon, is_favorite, is_folder = item_data
            if not is_folder:
                continue

            rect = self.listView.visualRect(index)
            if not viewport_rect.intersects(rect):
                continue

            if path not in self.folder_buttons:
                btns = []

                def make_button(text, icon_path, callback, color="rgba(0, 0, 0, 180)"):
                    btn = QPushButton(text, self.listView.viewport())
                    btn.setStyleSheet(
                        f"""
                        QPushButton {{
                            background-color: {color};
                            color: white;
                            border: none;
                            padding-left: 28px; /* shift text right so it's centered overall */
                            font-weight: bold;
                            text-align: center;  /* center the text inside the button */
                        }}
                        QPushButton:hover {{
                            background-color: rgba(255, 255, 255, 30);
                        }}
                    """
                    )
                    btn.setCursor(Qt.PointingHandCursor)
                    btn.setIcon(QIcon(icon_path))
                    btn.setIconSize(QSize(18, 18))
                    btn.clicked.connect(callback)
                    btn.setFixedHeight(26)
                    return btn

                btn_thumb = make_button(
                    " Change Thumbnail",
                    "_internal/icons/image.svg",
                    lambda _, p=path: self._choose_folder_thumbnail(p),
                )
                btn_rename = make_button(
                    " Rename Folder",
                    "_internal/icons/edit.svg",
                    lambda _, p=path: self._rename_folder(p),
                )
                launch_text = (
                    " Remove Launch Control"
                    if path in self.folder_launch_map
                    else " Set Launch Control"
                )
                btn_launch = make_button(
                    launch_text,
                    "_internal/icons/launch_overlay.svg",
                    lambda _, p=path: self._toggle_folder_launch(p),
                )
                btn_delete = make_button(
                    " Delete Folder",
                    "_internal/icons/delete.svg",
                    lambda _, p=path: self._delete_folder(p),
                    color="rgba(200, 30, 30, 180)",
                )

                btns.extend([btn_thumb, btn_rename, btn_launch, btn_delete])
                self.folder_buttons[path] = btns

            # Position and show the buttons
            btns = self.folder_buttons[path]
            button_width = rect.width()
            spacing = 2
            total_height = sum(btn.height() for btn in btns) + spacing * (len(btns) - 1)
            start_y = rect.y() + (rect.height() - total_height) // 2

            for i, btn in enumerate(btns):
                btn.setFixedWidth(button_width)
                btn.move(rect.x(), start_y + i * (btn.height() + spacing))
                btn.show()

    def eventFilter(self, source, event):
        if event.type() == QEvent.Resize and source == self.listView.viewport():
            self.update_edit_mode_buttons()
        return super().eventFilter(source, event)

    def _show_spinner_for(self, duration_ms):
        self.spinner.start()
        QTimer.singleShot(duration_ms, self.spinner.stop)

    def _load_static_image(self, image_path):
        try:
            image = QImage(image_path)
            if image.isNull():
                raise ValueError("Image failed to load.")

            pixmap = QPixmap.fromImage(image)
            self.scene.clear()

            self.image_item = QGraphicsPixmapItem(pixmap)
            self.scene.addItem(self.image_item)
            self.graphics_view.setScene(self.scene)

            self.graphics_view.fitInView(self.image_item, Qt.KeepAspectRatio)
            self.graphics_view.setDragMode(QGraphicsView.ScrollHandDrag)
            self.graphics_view.setInteractive(True)

            self.graphics_view.viewport().update()
            self._current_pixmap = pixmap

            self._center_image()
        except Exception as e:
            self._show_error(f"Unable to load image: {e}")

    def update_toolbar_theme(self):
        if self.is_dark_mode:
            self.toolbar.setStyleSheet(
                """
                QFrame#toolbar {
                    background-color: rgba(37, 43, 48, 1);
                    border-bottom: 1px solid rgba(255,255,255,0.08);
                    backdrop-filter: blur(6px);
                }
            """
            )
        else:
            self.toolbar.setStyleSheet(
                """
                QFrame#toolbar {
                    background-color: rgba(220, 213, 206, 1);
                    border-bottom: 1px solid rgba(0,0,0,0.08);
                    backdrop-filter: blur(6px);
                }
            """
            )

    def _open_overlay_position_dialog(self):
        dialog = QDialog(self)
        dialog.setWindowTitle("Choose Folder Overlay Position")
        layout = QVBoxLayout(dialog)

        label = QLabel("Select where the folder overlay icon should appear:")
        layout.addWidget(label)

        positions = ["top-left", "top-right", "bottom-left", "bottom-right", "hidden"]
        button_group = QButtonGroup(dialog)
        for pos in positions:
            btn = QRadioButton(pos.replace("-", " ").title())
            layout.addWidget(btn)
            button_group.addButton(btn)
            btn.setChecked(self.folder_overlay_position == pos)

        ok_btn = QPushButton("OK")
        ok_btn.clicked.connect(
            lambda: self._set_folder_overlay_position(
                next(
                    pos
                    for btn, pos in zip(button_group.buttons(), positions)
                    if btn.isChecked()
                )
            )
            or dialog.accept()
        )
        layout.addWidget(ok_btn)

        dialog.setLayout(layout)
        dialog.exec_()


# -----------------------------------------------------------------------------
# Thumbnail Delegate for QListView
# -----------------------------------------------------------------------------
class ThumbnailDelegate(QStyledItemDelegate):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.parent = parent

    def paint(self, painter, option, index):
        painter.save()
        painter.setRenderHint(QPainter.Antialiasing)

        # Get item data
        item_data = index.data(Qt.UserRole)
        if not item_data:
            painter.restore()
            return

        path, icon, is_favorite, is_folder = item_data
        ext = os.path.splitext(path)[1].lower()
        name = os.path.basename(path)

        # Calculate item size
        item_size = THUMB_SIZE + 8
        x = option.rect.x()
        y = option.rect.y()

        # Draw background with shadow effect
        shadow_rect = QRect(x + 2, y + 2, item_size - 4, item_size - 4)
        painter.fillRect(shadow_rect, QColor(0, 0, 0, 50))

        # Draw main thumbnail area
        thumb_rect = QRect(x, y, item_size, item_size)
        painter.fillRect(thumb_rect, QColor(40, 40, 40, 200))

        # Draw icon with proper scaling
        if not icon.isNull():
            icon_pixmap = icon.pixmap(THUMB_SIZE, THUMB_SIZE)
            if not icon_pixmap.isNull():
                painter.drawPixmap(x + 4, y + 4, icon_pixmap)

        # Draw favorite heart overlay (always show empty heart, filled if favorited)
        if not is_folder:
            try:
                # Try to get the application directory
                app_dir = os.path.dirname(os.path.abspath(__file__))
                
                # Define possible icon paths
                icon_name = "heart_filled.svg" if is_favorite else "heart_empty.svg"
                possible_paths = [
                    os.path.join(app_dir, "_internal", "icons", icon_name),  # Try local _internal/icons folder
                    os.path.join(os.path.dirname(app_dir), "_internal", "icons", icon_name),  # Try parent/_internal/icons
                    os.path.join(os.path.expanduser("~"), "AppData", "Local", "MediaExplorer", "_internal", "icons", icon_name),  # Try AppData/_internal/icons
                ]
                
                heart_pixmap = None
                
                # Try each possible path
                for icon_path in possible_paths:
                    if os.path.exists(icon_path):
                        heart_icon = QIcon(icon_path)
                        heart_pixmap = heart_icon.pixmap(24, 24)
                        if not heart_pixmap.isNull():
                            break
                
                # If we have a valid pixmap, draw it
                if heart_pixmap and not heart_pixmap.isNull():
                    # Draw in top-right corner
                    heart_x = thumb_rect.right() - 32
                    heart_y = thumb_rect.top() + 8
                    painter.drawPixmap(heart_x, heart_y, heart_pixmap)
                else:
                    # Fallback drawing - draw a simple heart shape
                    painter.save()
                    painter.setRenderHint(QPainter.Antialiasing)
                    
                    # Set heart color (red for favorite, gray for not)
                    if is_favorite:
                        painter.setBrush(QColor(255, 0, 0, 200))
                    else:
                        painter.setBrush(QColor(180, 180, 180, 120))
                        
                    painter.setPen(Qt.NoPen)
                    
                    # Draw heart shape
                    heart_x = thumb_rect.right() - 32
                    heart_y = thumb_rect.top() + 8
                    size = 24
                    
                    # Draw heart shape using path
                    heart_path = QPainterPath()
                    # Create a more proportional heart shape
                    center_x = heart_x + size/2
                    center_y = heart_y + size/2
                    width = size * 0.8
                    height = size * 0.7
                    
                    # Start from the bottom point
                    heart_path.moveTo(center_x, center_y + height/2)
                    
                    # Left curve
                    heart_path.cubicTo(
                        center_x - width/3, center_y + height/4,
                        center_x - width/2, center_y - height/4,
                        center_x, center_y - height/2
                    )
                    
                    # Right curve
                    heart_path.cubicTo(
                        center_x + width/2, center_y - height/4,
                        center_x + width/3, center_y + height/4,
                        center_x, center_y + height/2
                    )
                    
                    painter.drawPath(heart_path)
                    painter.restore()
                    
            except Exception as e:
                print(f"Error drawing favorite heart: {e}")

        # Draw file type badge if enabled
        if self.parent.show_tags and not is_folder:
            if ext == ".gif":
                badge_text = "GIF"
            else:
                badge_text = ext.upper()[1:] if ext else "FILE"

            is_top = getattr(self.parent, "file_title_placement", "bottom") != "top"
            y_tag = y + 4 if is_top else y + item_size - 24

            badge_rect = QRect(x + 4, y_tag, 60, 20)
            painter.fillRect(badge_rect, QColor(0, 0, 0, 150))

            font = painter.font()
            font.setBold(True)
            font.setPointSize(10)
            painter.setFont(font)
            painter.setPen(Qt.white)
            painter.drawText(badge_rect, Qt.AlignCenter, badge_text)
            painter.fillRect(badge_rect, QColor(0, 0, 0, 150))

            # Draw badge text
            font = painter.font()
            font.setBold(True)
            font.setPointSize(10)
            painter.setFont(font)
            painter.setPen(Qt.white)
            painter.drawText(badge_rect, Qt.AlignCenter, badge_text)

        # Draw folder overlay icon if enabled
        if (
            is_folder
            and hasattr(self.parent, "folder_overlay_position")
            and self.parent.folder_overlay_position != "hidden"
        ):
            overlay_icon = QIcon(
                "_internal/icons/folder_overlay_dark.svg"
                if getattr(self.parent, "is_dark_mode", True)
                else "_internal/icons/folder_overlay_light.svg"
            )
            overlay_pixmap = overlay_icon.pixmap(24, 24)

            # Position based on user setting
            margin = 6
            if self.parent.folder_overlay_position == "top-left":
                ox = x + margin
                oy = y + margin
            elif self.parent.folder_overlay_position == "top-right":
                ox = x + item_size - 24 - margin
                oy = y + margin
            elif self.parent.folder_overlay_position == "bottom-left":
                ox = x + margin
                oy = y + item_size - 24 - margin
            elif self.parent.folder_overlay_position == "bottom-right":
                ox = x + item_size - 24 - margin
                oy = y + item_size - 24 - margin

            painter.drawPixmap(ox, oy, overlay_pixmap)

        # Draw launch control overlay if enabled
        if (
            hasattr(self.parent, "hide_launch_icon")
            and not self.parent.hide_launch_icon
            and hasattr(self.parent, "folder_launch_map")
            and path in self.parent.folder_launch_map
        ):
            launch_icon = QIcon("_internal/icons/launch_overlay.svg")
            launch_pixmap = launch_icon.pixmap(72, 72)
            painter.drawPixmap(x + item_size - 90, y + 12, launch_pixmap)

        # Draw filename if enabled
        if (
            hasattr(self.parent, "show_names")
            and self.parent.show_names
            and not is_folder
        ):
            font = painter.font()
            font.setBold(True)
            font.setPointSize(10)
            painter.setFont(font)

            text_flags = Qt.AlignCenter
            text_metrics = QFontMetrics(font)
            text_width = text_metrics.width(name)
            placement = getattr(self.parent, "file_title_placement", "bottom")
            name_y = y + 4 if placement == "top" else y + item_size - 24
            name_rect = QRect(x + 4, name_y, item_size - 8, 20)

            # Choose background based on mode
            bg_mode = getattr(self.parent, "file_title_bg_mode", "default")
            if bg_mode == "default":
                painter.fillRect(name_rect, QColor(0, 0, 0, 140))
            elif bg_mode == "short":
                short_rect = QRect(
                    name_rect.x() + (name_rect.width() - text_width - 10) // 2,
                    name_rect.y(),
                    text_width + 10,
                    name_rect.height(),
                )
                painter.setBrush(QColor(0, 0, 0, 140))  # <-- actual color
                painter.setPen(Qt.NoPen)
                painter.drawRoundedRect(short_rect, 6, 6)
            # else: no background

            pen = QPen(QColor(0, 0, 0), 2)
            painter.setPen(pen)
            for dx in (-1, 1):
                for dy in (-1, 1):
                    painter.drawText(name_rect.translated(dx, dy), text_flags, name)

            # Draw white text on top
            painter.setPen(Qt.white)
            painter.drawText(name_rect, text_flags, name)

        # Draw folder name if enabled
        if (
            hasattr(self.parent, "show_folder_names")
            and self.parent.show_folder_names
            and is_folder
        ):
            font = painter.font()
            font.setBold(True)
            font.setPointSize(11)
            painter.setFont(font)

            text_flags = Qt.AlignCenter
            text_metrics = QFontMetrics(font)
            text_width = text_metrics.width(name)
            placement = getattr(self.parent, "folder_title_placement", "bottom")
            name_y = y + 4 if placement == "top" else y + item_size - 24
            name_rect = QRect(x + 4, name_y, item_size - 8, 20)

            # Choose background based on mode
            bg_mode = getattr(self.parent, "folder_title_bg_mode", "default")
            if bg_mode == "default":
                painter.fillRect(name_rect, QColor(30, 30, 30, 140))
            elif bg_mode == "short":
                short_rect = QRect(
                    name_rect.x() + (name_rect.width() - text_width - 10) // 2,
                    name_rect.y(),
                    text_width + 10,
                    name_rect.height(),
                )
                painter.setBrush(QColor(30, 30, 30, 140))  # <-- actual color
                painter.setPen(Qt.NoPen)
                painter.drawRoundedRect(short_rect, 6, 6)
            # else: no background

            pen = QPen(QColor(0, 0, 0), 2)
            painter.setPen(pen)
            for dx in (-1, 1):
                for dy in (-1, 1):
                    painter.drawText(name_rect.translated(dx, dy), text_flags, name)

            # Draw white text on top
            painter.setPen(Qt.white)
            painter.drawText(name_rect, text_flags, name)

    def editorEvent(self, event, model, option, index):
        """Handle mouse clicks on favorite hearts"""
        if event.type() == QEvent.MouseButtonRelease and event.button() == Qt.LeftButton:
            # Get item data
            item_data = index.data(Qt.UserRole)
            if item_data:
                path, icon, is_favorite, is_folder = item_data
                
                # Calculate heart icon position (matches paint method)
                thumb_rect = option.rect
                heart_rect = QRect(
                    thumb_rect.right() - 32,  # x position
                    thumb_rect.top() + 8,     # y position
                    24,                       # width
                    24                        # height
                )
                
                # Check if click was within heart area
                if heart_rect.contains(event.pos()) and not is_folder:
                    # Toggle favorite state
                    new_favorite = not is_favorite
                    
                    # Update the model's internal state
                    if hasattr(model, 'update_favorite'):
                        model.update_favorite(path, new_favorite)
                    
                    # Update the parent's favorites dictionary
                    if hasattr(self.parent, 'favorites'):
                        if new_favorite:
                            self.parent.favorites[path] = True
                        else:
                            self.parent.favorites.pop(path, None)
                        
                        # Save favorites to disk if parent has the method
                        if hasattr(self.parent, '_save_json') and hasattr(self.parent, 'favorites_file'):
                            self.parent._save_json(self.parent.favorites, self.parent.favorites_file)
                    
                    # Force repaint of this item
                    model.dataChanged.emit(index, index, [Qt.UserRole])
                    
                    # Also update the view to reflect the change
                    if hasattr(self.parent, 'view'):
                        self.parent.view.viewport().update()
                    
                    return True
        
        return super().editorEvent(event, model, option, index)

    def sizeHint(self, option, index):
        return QSize(THUMB_SIZE + 8, THUMB_SIZE + 8)


# -----------------------------------------------------------------------------
# Thumbnail List Model
# -----------------------------------------------------------------------------
class ThumbnailListModel(QAbstractListModel):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.entries = []  # list of tuples: (path, QIcon, is_favorite, is_folder)
        self.parent = parent  # Needed to access favorites dynamically

    def rowCount(self, parent=QModelIndex()):
        return len(self.entries)

    def data(self, index, role=Qt.DisplayRole):
        if not index.isValid():
            return QVariant()

        if role == Qt.UserRole:
            path, icon, is_favorite, is_folder = self.entries[index.row()]
            # Ensure we're using the latest favorite status from the parent
            if self.parent and hasattr(self.parent, 'favorites'):
                is_favorite = path in self.parent.favorites
            return (path, icon, is_favorite, is_folder)

        return QVariant()

    def clear(self):
        self.beginResetModel()
        self.entries = []
        self.endResetModel()

    def update_favorite(self, path, is_favorite):
        """Update the favorite status of an item"""
        for i, (p, icon, fav, is_folder) in enumerate(self.entries):
            if p == path:
                self.entries[i] = (path, icon, is_favorite, is_folder)
                # Emit data changed signal for this index
                self.dataChanged.emit(
                    self.index(i), 
                    self.index(i),
                    [Qt.UserRole]
                )
                break

    def addItem(self, path, icon, is_favorite=False, is_folder=False):
        self.beginInsertRows(QModelIndex(), len(self.entries), len(self.entries))
        self.entries.append((path, icon, is_favorite, is_folder))
        self.endInsertRows()

    def update_icon(self, path, icon):
        for row, (p, _, fav, is_folder) in enumerate(self.entries):
            if p == path:
                self.entries[row] = (p, icon, fav, is_folder)
                index = self.index(row)
                self.dataChanged.emit(index, index, [Qt.DecorationRole])
                break

    def update_favorite(self, path, is_favorite):
        for row, (p, icon, _, is_folder) in enumerate(self.entries):
            if p == path:
                self.entries[row] = (p, icon, is_favorite, is_folder)
                index = self.index(row)
                self.dataChanged.emit(index, index, [Qt.UserRole])
                break

    def get_item_path(self, index):
        if index.isValid() and index.row() < len(self.entries):
            return self.entries[index.row()][0]
        return None



if __name__ == "__main__":
    import multiprocessing

    multiprocessing.set_start_method("spawn", True)

    app = QApplication(sys.argv)
    app.setOrganizationName("MediaExplorer")
    app.setApplicationName("MediaExplorer")
    app.settings = QSettings("MediaExplorer", "MediaExplorer")

    # Splash
    splash_pix = QPixmap("_internal/icons/logo_launch.png")
    splash = QSplashScreen(splash_pix, Qt.WindowStaysOnTopHint)
    splash.setStyleSheet("background-color: black;")
    splash.show()
    app.processEvents()

    # Build main window
    window = MediaExplorer()
    window.showFullScreen()

    # Close splash immediately once window is shown
    splash.finish(window)

    sys.exit(app.exec_())
