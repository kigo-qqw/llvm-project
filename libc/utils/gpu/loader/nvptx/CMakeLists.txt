set(LLVM_LINK_COMPONENTS
  BinaryFormat
  Object
  Option
  Support
  )

add_llvm_executable(nvptx-loader nvptx-loader.cpp)
target_link_libraries(nvptx-loader PRIVATE gpu_loader CUDA::cuda_driver)
