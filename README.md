MediaExplorer - Version 1.0 (2025)

MediaExplorer is a lightweight desktop app for browsing and managing media files. 
It supports images, videos, GIFs, PDFs, and more. Easily navigate folders, open 
files in fullscreen, favorite items, and customize folder thumbnails with a 
simple, fast, and intuitive interface.

------------------------------------------------------------
1. Dependencies
------------------------------------------------------------
if launching the program from the .py file, ensure "opencv_world480.dll" is saved in the "_internal" folder (OpenCV 4.8 (or compatible).)

------------------------------------------------------------
2. Installation
------------------------------------------------------------

To install:

a) Extract the downloaded MediaExplorer folder.

b) Place it in the top-level folder of your media collection.

This folder becomes the "root folder" and the starting point for the app.
You cannot navigate above the root folder. To change the root, move the 
MediaExplorer folder to a different location.

------------------------------------------------------------
3. File Viewing
------------------------------------------------------------

- Click a folder to enter it.
- Click an image, video, or PDF to open it in fullscreen.
- Double-click other files to open them in their default programs.
- Click the heart icon on thumbnails to favorite/unfavorite files.
- Right-click or press Escape to go back.
- You cannot go above the root folder.

You cannot go above the root folder (location of MediaExplorer installation folder). To go higher in your file path, move the MediaExplorer folder higher.

------------------------------------------------------------
4. Fullscreen Viewer
------------------------------------------------------------

- Use your mouse to zoom and pan.
- Left/Right Arrow keys move to the next/previous file.
- Down Arrow moves to the next PDF page; Up Arrow goes back.
- Click the arrow in the top-right corner for the mini menu:
  - Start slideshow mode
  - Toggle random navigation
  - Delete the current file
- Right-click or press Escape to exit fullscreen.

------------------------------------------------------------
5. Toolbar & Settings
------------------------------------------------------------

The toolbar appears at the top in folder view. Left to right:

a) Back Button - Go back to the previous folder.

b) Settings - Change resolution, clear thumbnail cache, toggle dark/light mode, view About info, exit program.

c) View - Adjust thumbnail size, image resolution, show/hide names, toolbar, and breadcrumb bar.

d) Overlay Toggles - Show/hide file and folder names, tags, title placement, and launch icons.

e) Edit Mode - Rename or delete folders, change folder thumbnail image, enable/disable Launch Mode for .exe files.

f) Update File Thumbs - Refresh thumbnails in the current folder.

g) Home - Return to the root folder.

h) Search Bar - Filter files by name or extension.

i) Sort Buttons - Sort files Ascending (default), Descending, Random, or show only Favorites.

j) New Folder - Create a new folder.

k) Import Files - Copy files into the current folder.

l) Exit - Exit the program.

------------------------------------------------------------
6. FAQ
------------------------------------------------------------

Q: The program starts in the wrong folder.

A: MediaExplorer uses its own folder as the root. Move the MediaExplorer folder to your preferred root location.

Q: My folder thumbnails are missing.

A: Thumbnails are saved in the 'folder_thumbs' folder. Do not delete or move it. Moving MediaExplorer to another location breaks thumbnail paths.

Q: Large folders load slowly.

A: Initial load may be slow. Thumbnails are cached for faster access next time.

Q: The program crashes while loading.

A: Wait for the spinner to stop before clicking. Heavy interaction during loading may cause instability. Reduce the size of your folder or split large folders
if crashing persists. Video files may take up to 30 seconds to load in very large folders.

Q: Some thumbnails didn't load.

A: Some files may have timed out. Click 'Update File Thumbs' or re-enter the folder. Some videos may appear black due to dark thumbnail frames.

------------------------------------------------------------
