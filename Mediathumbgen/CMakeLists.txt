cmake_minimum_required(VERSION 3.12)
project(mediathumbgen)

set(CMAKE_CXX_STANDARD 17)

# Set up Pybind11 include path (adjust this path if needed)
set(PYBIND11_PATH "${CMAKE_SOURCE_DIR}/include")

# Find Python
find_package(Python3 REQUIRED COMPONENTS Interpreter Development)

# Set up OpenCV
set(OpenCV_DIR "${CMAKE_SOURCE_DIR}/opencv/x64/vc16/lib")
find_package(OpenCV REQUIRED)

# Add main module first (important!)
add_library(mediathumbgen MODULE thumbgen.cpp)

# Windows-specific: avoid 'lib' prefix and '.dll' suffix
set_target_properties(mediathumbgen PROPERTIES PREFIX "" SUFFIX ".pyd")

# Include directories
target_include_directories(mediathumbgen PRIVATE
    ${PYBIND11_PATH}
    ${Python3_INCLUDE_DIRS}
    ${OpenCV_INCLUDE_DIRS}
)

# Link libraries
target_link_libraries(mediathumbgen PRIVATE
    Python3::Python
    ${OpenCV_LIBS}
)
