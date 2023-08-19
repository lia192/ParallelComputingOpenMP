cmake_minimum_required(VERSION 3.10)

project(sat VERSION 1.0)

# Enable OpenMP
find_package(OpenMP REQUIRED)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED True)

add_executable(${PROJECT_NAME}_seq sequential.cpp)
add_executable(${PROJECT_NAME}_par parallel.cpp)

# Set OpenMP flags
target_compile_options(${PROJECT_NAME}_par PRIVATE ${OpenMP_CXX_FLAGS})
# Link against OpenMP
target_link_libraries(${PROJECT_NAME}_par PRIVATE OpenMP::OpenMP_CXX)


set(CMAKE_CXX_FLAGS "-Wall -Wextra")
set(CMAKE_CXX_FLAGS_DEBUG "-g")
set(CMAKE_CXX_FLAGS_RELEASE "-O3")
