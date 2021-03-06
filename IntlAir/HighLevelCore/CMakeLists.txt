﻿#  Copyright (c) Microsoft Corporation. All rights reserved.
#  Licensed under the MIT License.

cmake_minimum_required (VERSION 3.10)

project (helloWorldAzureIoT_HighLevelCore C)

azsphere_configure_tools(TOOLS_REVISION "20.04")
azsphere_configure_api(TARGET_API_SET "5")

add_executable(${PROJECT_NAME} main.c eventloop_timer_utilities.c parson.c epoll_timerfd_utilities.c oled.c i2c.c lps22hh_reg.c lsm6dso_reg.c sd1306.c)
target_include_directories(${PROJECT_NAME} PUBLIC ${AZURE_SPHERE_API_SET_DIR}/usr/include/azureiot)
target_compile_definitions(${PROJECT_NAME} PUBLIC AZURE_IOT_HUB_CONFIGURED)
target_link_libraries(${PROJECT_NAME} m azureiot applibs pthread gcc_s c)

azsphere_target_add_image_package(${PROJECT_NAME})

azsphere_target_hardware_definition(${PROJECT_NAME} TARGET_DIRECTORY "Hardware/mt3620_rdb" TARGET_DEFINITION "sample_hardware.json")