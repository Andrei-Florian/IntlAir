/*
    IntlAir
    21/MAY/2020 | Andrei Florian
*/

// basic includes
#include <errno.h>
#include <signal.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <stdio.h>
#include <math.h>

//#include "epoll_timerfd_utilities.h"
#include <sys/time.h>

// applibs_versions.h defines the API struct versions to use for applibs APIs.
#include "applibs_versions.h"
#include <applibs/log.h>
#include <applibs/networking.h>
#include <applibs/gpio.h>
#include <applibs/storage.h>
#include <applibs/eventloop.h>
#include <hw/sample_hardware.h>
#include "eventloop_timer_utilities.h"

//// Air Quality Monitor
#include "applibs_versions.h"
#include "i2c.h"
#include "build_options.h"

// Azure IoT SDK
#include <iothub_client_core_common.h>
#include <iothub_device_client_ll.h>
#include <iothub_client_options.h>
#include <iothubtransportmqtt.h>
#include <iothub.h>
#include <azure_sphere_provisioning.h>

// atmospheric pressure
#include "lsm6dso_reg.h"
#include "lps22hh_reg.h"

// other
#include "parson.h" // used to parse Device Twin messages.
#include "universum_utilities.h"

// variables to store air quality
int co2 = 0;
int tvoc = 0;

// relay click
#define MIKROE_PWM  1   //click#1=GPIO0;  click#2=GPIO1
#define MIKROE_CS   35  //click#1=GPIO34; click#2=GPIO35

static int r1PinFd;  //relay #1
static GPIO_Value_Type relay1Pin;
static int r2PinFd;  //relay #2
static GPIO_Value_Type relay2Pin;

// app variables
int fd = -1; // initialise variable to hold button poll

int sleepTime = 120; // define the 120 seconds sleep time between reads
float pressure_hPa = 0; // variable to store the atmospheric pressure

char tbuf[32]; // holds the time

int loopNumberTvoc = 0;
int loopNumberCo2 = 0;

int co2_goodCount = 0;
int tvoc_goodCount = 0;

int co2_badCount = 0;
int tvoc_badCount = 0;

int tvocTreshold = 40; // turn purifier on if tvoc > 40ppb
int co2Treshold = 1000; // turn the fan on if co2 > 1,000ppb

bool isRelayCo2 = false;
bool isRelayTvoc = false;

bool isRelayCo2Blocked = false;
bool isRelayTvocBlocked = false;

int timeZone = 1; // timezone (from GMT)

// EDITABLE VARIABLES
static const int AzureIoTDefaultPollPeriodSeconds = 1; // time to wait before loop restarts
const char JSONBuffer[] = "{\"%s\":%d, \"%s\":%d, \"%s\":%f, \"%s\":%d, \"%s\":%d, \"%s\":\"%s\"}"; // the format of the data to send

// I2C migrated variables - PS. Compile fails if the I2C.c file is included, unknown reason, had to transfer contents to main.c
static axis3bit16_t data_raw_acceleration;
static axis3bit16_t data_raw_angular_rate;
static axis3bit16_t raw_angular_rate_calibration;
static axis1bit32_t data_raw_pressure;
static axis1bit16_t data_raw_temperature;
static float acceleration_mg[3];
static float angular_rate_dps[3];
static float lsm6dsoTemperature_degC;
static float lps22hhTemperature_degC;

static uint8_t whoamI, rst;
int accelTimerFd;
const uint8_t lsm6dsOAddress = LSM6DSO_ADDRESS;     // Addr = 0x6A
const uint8_t sgp30 = 0x58;
lsm6dso_ctx_t dev_ctx;
lps22hh_ctx_t pressure_ctx;
bool lps22hhDetected;

float altitude;

typedef enum // exit codes
{
	ExitCode_Success = 0,

	ExitCode_TermHandler_SigTerm = 1,

	ExitCode_Main_EventLoopFail = 2,

	ExitCode_ButtonTimer_Consume = 3,

	ExitCode_AzureTimer_Consume = 4,

	ExitCode_Init_EventLoop = 5,
	ExitCode_Init_MessageButton = 6,
	ExitCode_Init_OrientationButton = 7,
	ExitCode_Init_TwinStatusLed = 8,
	ExitCode_Init_ButtonPollTimer = 9,
	ExitCode_Init_AzureTimer = 10,

	ExitCode_IsButtonPressed_GetValue = 11
} ExitCode;

static volatile sig_atomic_t exitCode = ExitCode_Success;

// Azure IoT Hub/Central defines.
#define SCOPEID_LENGTH 20
static char scopeId[SCOPEID_LENGTH];

static IOTHUB_DEVICE_CLIENT_LL_HANDLE iothubClientHandle = NULL;
static const int keepalivePeriodSeconds = 20;
static bool iothubAuthenticated = false;
static void SendMessageCallback(IOTHUB_CLIENT_CONFIRMATION_RESULT result, void* context);
static void TwinCallback(DEVICE_TWIN_UPDATE_STATE updateState, const unsigned char* payload, size_t payloadSize, void* userContextCallback);
static void TwinReportBoolState(const char* propertyName, bool propertyValue);
static void ReportStatusCallback(int result, void* context);
static const char* GetReasonString(IOTHUB_CLIENT_CONNECTION_STATUS_REASON reason);
static const char* getAzureSphereProvisioningResultString(AZURE_SPHERE_PROV_RETURN_VALUE provisioningResult);
static void SetupAzureClient(void);

// Initialization/Cleanup
static ExitCode InitPeripheralsAndHandlers(void);
static void CloseFdAndPrintError(int fd, const char* fdName);
static void ClosePeripheralsAndHandlers(void);

// Timer / polling
static EventLoop* eventLoop = NULL;
static EventLoopTimer* buttonPollTimer = NULL;
static EventLoopTimer* azureTimer = NULL;
static int azureIoTPollPeriodSeconds = -1;

static const int AzureIoTMinReconnectPeriodSeconds = 60; // when to start reconnecting to Azure IoT
static const int AzureIoTMaxReconnectPeriodSeconds = 10 * 60; // max time to try reconnecting for

// LED
void errorLED(void);
void blinkLED(void);

// Status variables
uint8_t lsm6dso_status = 1;
uint8_t lps22hh_status = 1;
uint8_t RTCore_status = 1;

//Extern variables
int i2cFd = -1;
extern int epollFd;
extern volatile sig_atomic_t terminationRequired;

// Routines to read/write to the LSM6DSO device
static int32_t platform_write(int* fD, uint8_t reg, uint8_t* bufp, uint16_t len);
static int32_t platform_read(int* fD, uint8_t reg, uint8_t* bufp, uint16_t len);

// Routines to read/write to the LPS22HH device connected to the LSM6DSO sensor hub
static int32_t lsm6dso_write_lps22hh_cx(void* ctx, uint8_t reg, uint8_t* data, uint16_t len);
static int32_t lsm6dso_read_lps22hh_cx(void* ctx, uint8_t reg, uint8_t* data, uint16_t len);

// File descriptors - initialized to invalid value
int epollFd = -1;
static int buttonPollTimerFd = -1;
static int buttonAGpioFd = -1;
static int buttonBGpioFd = -1;

int userLedRedFd = -1;
int userLedGreenFd = -1;
int userLedBlueFd = -1;
int appLedFd = -1;
int wifiLedFd = -1;
int clickSocket1Relay1Fd = -1;
int clickSocket1Relay2Fd = -1;

// Termination state
volatile sig_atomic_t terminationRequired = false;

int initI2c(void)
{
	// Begin MT3620 I2C init 

	i2cFd = I2CMaster_Open(MT3620_RDB_HEADER4_ISU2_I2C);
	if (i2cFd < 0) {
		Log_Debug("[setup] ERROR: I2CMaster_Open: errno=%d (%s)\n", errno, strerror(errno));
		return -1;
	}

	int result = I2CMaster_SetBusSpeed(i2cFd, I2C_BUS_SPEED_STANDARD);
	if (result != 0) {
		Log_Debug("[setup] ERROR: I2CMaster_SetBusSpeed: errno=%d (%s)\n", errno, strerror(errno));
		return -1;
	}

	result = I2CMaster_SetTimeout(i2cFd, 100);
	if (result != 0) {
		Log_Debug("[setup] ERROR: I2CMaster_SetTimeout: errno=%d (%s)\n", errno, strerror(errno));
		return -1;
	}

	uint8_t buff[2];
	int32_t retVal;
	uint8_t sgp30_buffer[6];

	buff[0] = 0x20;
	buff[1] = 0x03;
	Log_Debug("[setup] INIT [%d] 0x%02x ", 0, buff[0]);
	Log_Debug("[setup] [%d] 0x%02x \n", 1, buff[1]);
	retVal = I2CMaster_Write(i2cFd, 0x58, buff, 16);

	// Initialize lsm6dso mems driver interface
	dev_ctx.write_reg = platform_write;
	dev_ctx.read_reg = platform_read;
	dev_ctx.handle = &i2cFd;

	// Check device ID
	delay(5000); //pf

	// Check device ID
	lsm6dso_device_id_get(&dev_ctx, &whoamI);
	if (whoamI != LSM6DSO_ID) {
		Log_Debug("[setup] LSM6DSO not found!\n");
		// OLED update
		lsm6dso_status = 1;
		oled_i2c_bus_status(1);
		return -1;
	}
	else {
		Log_Debug("[setup] LSM6DSO Found!\n");

		// OLED update
		lsm6dso_status = 0;
		oled_i2c_bus_status(1);
	}

	// Restore default configuration
	lsm6dso_reset_set(&dev_ctx, PROPERTY_ENABLE);
	do {
		lsm6dso_reset_get(&dev_ctx, &rst);
	} while (rst);

	// Disable I3C interface
	lsm6dso_i3c_disable_set(&dev_ctx, LSM6DSO_I3C_DISABLE);

	// Enable Block Data Update
	lsm6dso_block_data_update_set(&dev_ctx, PROPERTY_ENABLE);

	// Set Output Data Rate
	lsm6dso_xl_data_rate_set(&dev_ctx, LSM6DSO_XL_ODR_12Hz5);
	lsm6dso_gy_data_rate_set(&dev_ctx, LSM6DSO_GY_ODR_12Hz5);

	// Set full scale
	lsm6dso_xl_full_scale_set(&dev_ctx, LSM6DSO_4g);
	lsm6dso_gy_full_scale_set(&dev_ctx, LSM6DSO_2000dps);

	// Configure filtering chain(No aux interface)
   // Accelerometer - LPF1 + LPF2 path	
	lsm6dso_xl_hp_path_on_out_set(&dev_ctx, LSM6DSO_LP_ODR_DIV_100);
	lsm6dso_xl_filter_lp2_set(&dev_ctx, PROPERTY_ENABLE);

	// lps22hh specific init

	// Default the flag to false.  If we fail to communicate with the LPS22HH device, this flag
	// will cause application execution to skip over LPS22HH specific code.
	lps22hhDetected = false;

	// Initialize lps22hh mems driver interface
	pressure_ctx.read_reg = lsm6dso_read_lps22hh_cx;
	pressure_ctx.write_reg = lsm6dso_write_lps22hh_cx;
	pressure_ctx.handle = &i2cFd;

	int failCount = 10;

	while (!lps22hhDetected) {

		// Enable pull up on master I2C interface.
		lsm6dso_sh_pin_mode_set(&dev_ctx, LSM6DSO_INTERNAL_PULL_UP);

		// Check if LPS22HH is connected to Sensor Hub
		lps22hh_device_id_get(&pressure_ctx, &whoamI);
		if (whoamI != LPS22HH_ID) {
			Log_Debug("[setup] LPS22HH not found!\n");

			// OLED update
			lps22hh_status = 1;
			oled_i2c_bus_status(2);

		}
		else {
			lps22hhDetected = true;
			Log_Debug("[setup] LPS22HH Found!\n");

			// OLED update
			lps22hh_status = 0;
			oled_i2c_bus_status(2);
		}

		// Restore the default configuration
		lps22hh_reset_set(&pressure_ctx, PROPERTY_ENABLE);
		do {
			lps22hh_reset_get(&pressure_ctx, &rst);
		} while (rst);

		// Enable Block Data Update
		lps22hh_block_data_update_set(&pressure_ctx, PROPERTY_ENABLE);

		//Set Output Data Rate
		lps22hh_data_rate_set(&pressure_ctx, LPS22HH_10_Hz_LOW_NOISE);

		// If we failed to detect the lps22hh device, then pause before trying again.
		if (!lps22hhDetected) {
			delay(100);
		}

		if (failCount-- == 0) {
			bool lps22hhDetected = false;
			Log_Debug("[setup] Failed to read LPS22HH device ID, disabling all access to LPS22HH device!\n");
			Log_Debug("[setup] Usually a power cycle will correct this issue\n");
			break;
		}
	}

	// Read the raw angular rate data from the device to use as offsets.  We're making the assumption that the device
	// is stationary.

	uint8_t reg;

	Log_Debug("[setup] LSM6DSO: Calibrating angular rate . . .\n");
	Log_Debug("[setup] LSM6DSO: Please make sure the device is stationary.\n");

	do {

		// Delay and read the device until we have data!
		do {
			// Read the calibration values
			delay(5000);
			lsm6dso_gy_flag_data_ready_get(&dev_ctx, &reg);
		} while (!reg);

		if (reg)
		{
			// Read angular rate field data to use for calibration offsets
			memset(data_raw_angular_rate.u8bit, 0x00, 3 * sizeof(int16_t));
			lsm6dso_angular_rate_raw_get(&dev_ctx, raw_angular_rate_calibration.u8bit);
		}

		// Delay and read the device until we have data!
		do {
			// Read the calibration values
			delay(5000);
			lsm6dso_gy_flag_data_ready_get(&dev_ctx, &reg);
		} while (!reg);

		// Read the angular data rate again and verify that after applying the calibration, we have 0 angular rate in all directions
		if (reg)
		{

			// Read angular rate field data
			memset(data_raw_angular_rate.u8bit, 0x00, 3 * sizeof(int16_t));
			lsm6dso_angular_rate_raw_get(&dev_ctx, data_raw_angular_rate.u8bit);

			// Before we store the mdps values subtract the calibration data we captured at startup.
			angular_rate_dps[0] = lsm6dso_from_fs2000_to_mdps(data_raw_angular_rate.i16bit[0] - raw_angular_rate_calibration.i16bit[0]);
			angular_rate_dps[1] = lsm6dso_from_fs2000_to_mdps(data_raw_angular_rate.i16bit[1] - raw_angular_rate_calibration.i16bit[1]);
			angular_rate_dps[2] = lsm6dso_from_fs2000_to_mdps(data_raw_angular_rate.i16bit[2] - raw_angular_rate_calibration.i16bit[2]);

		}

		// If the angular values after applying the offset are not all 0.0s, then do it again!
	} while ((angular_rate_dps[0] != 0.0) || (angular_rate_dps[1] != 0.0) || (angular_rate_dps[2] != 0.0));

	Log_Debug("[setup] LSM6DSO: Calibrating angular rate complete!\n");

	return 0;
}

static int32_t platform_write(int* fD, uint8_t reg, uint8_t* bufp, uint16_t len)
{
	// Construct a new command buffer that contains the register to write to, then the data to write
	uint8_t cmdBuffer[len + 1];
	cmdBuffer[0] = reg;
	for (int i = 0; i < len; i++) {
		cmdBuffer[i + 1] = bufp[i];
	}

	// Write the data to the device
	int32_t retVal = I2CMaster_Write(*fD, lsm6dsOAddress, cmdBuffer, (size_t)len + 1);
	if (retVal < 0) {
		Log_Debug("ERROR: platform_write: errno=%d (%s)\n", errno, strerror(errno));
		return -1;
	}

	return 0;
}

static int32_t platform_read(int* fD, uint8_t reg, uint8_t* bufp, uint16_t len)
{
	// Set the register address to read
	int32_t retVal = I2CMaster_Write(i2cFd, lsm6dsOAddress, &reg, 1);
	if (retVal < 0) {
		Log_Debug("ERROR: platform_read(write step): errno=%d (%s)\n", errno, strerror(errno));
		return -1;
	}

	// Read the data into the provided buffer
	retVal = I2CMaster_Read(i2cFd, lsm6dsOAddress, bufp, len);
	if (retVal < 0) {
		Log_Debug("ERROR: platform_read(read step): errno=%d (%s)\n", errno, strerror(errno));
		return -1;
	}

	return 0;
}

static int32_t lsm6dso_write_lps22hh_cx(void* ctx, uint8_t reg, uint8_t* data, uint16_t len)
{
	axis3bit16_t data_raw_acceleration;
	int32_t ret;
	uint8_t drdy;
	lsm6dso_status_master_t master_status;
	lsm6dso_sh_cfg_write_t sh_cfg_write;

	// Configure Sensor Hub to write to the LPS22HH, and send the write data
	sh_cfg_write.slv0_add = (LPS22HH_I2C_ADD_L & 0xFEU) >> 1; // 7bit I2C address
	sh_cfg_write.slv0_subadd = reg,
		sh_cfg_write.slv0_data = *data,
		ret = lsm6dso_sh_cfg_write(&dev_ctx, &sh_cfg_write);

	/* Disable accelerometer. */
	lsm6dso_xl_data_rate_set(&dev_ctx, LSM6DSO_XL_ODR_OFF);

	/* Enable I2C Master. */
	lsm6dso_sh_master_set(&dev_ctx, PROPERTY_ENABLE);

	/* Enable accelerometer to trigger Sensor Hub operation. */
	lsm6dso_xl_data_rate_set(&dev_ctx, LSM6DSO_XL_ODR_104Hz);

	/* Wait Sensor Hub operation flag set. */
	lsm6dso_acceleration_raw_get(&dev_ctx, data_raw_acceleration.u8bit);
	do
	{
		delay(20);
		lsm6dso_xl_flag_data_ready_get(&dev_ctx, &drdy);
	} while (!drdy);

	do
	{
		delay(20);
		lsm6dso_sh_status_get(&dev_ctx, &master_status);
	} while (!master_status.sens_hub_endop);

	/* Disable I2C master and XL (trigger). */
	lsm6dso_sh_master_set(&dev_ctx, PROPERTY_DISABLE);
	lsm6dso_xl_data_rate_set(&dev_ctx, LSM6DSO_XL_ODR_OFF);

	return ret;
}

static int32_t lsm6dso_read_lps22hh_cx(void* ctx, uint8_t reg, uint8_t* data, uint16_t len)
{
	lsm6dso_sh_cfg_read_t sh_cfg_read;
	uint8_t buf_raw[6];
	int32_t ret;
	uint8_t drdy;
	lsm6dso_status_master_t master_status;

	/* Disable accelerometer. */
	lsm6dso_xl_data_rate_set(&dev_ctx, LSM6DSO_XL_ODR_OFF);

	/* Configure Sensor Hub to read LPS22HH. */
	sh_cfg_read.slv_add = (LPS22HH_I2C_ADD_L & 0xFEU) >> 1; /* 7bit I2C address */
	sh_cfg_read.slv_subadd = reg;
	sh_cfg_read.slv_len = (uint8_t)len;

	// Call the command to read the data from the sensor hub.
	// This data will be read from the device connected to the 
	// sensor hub, and saved into a register for us to read.
	ret = lsm6dso_sh_slv0_cfg_read(&dev_ctx, &sh_cfg_read);

	// Using slave 0 only
	lsm6dso_sh_slave_connected_set(&dev_ctx, LSM6DSO_SLV_0);

	/* Enable I2C Master */
	lsm6dso_sh_master_set(&dev_ctx, PROPERTY_ENABLE);

	/* Enable accelerometer to trigger Sensor Hub operation. */
	lsm6dso_xl_data_rate_set(&dev_ctx, LSM6DSO_XL_ODR_104Hz);

	/* Wait Sensor Hub operation flag set. */
	lsm6dso_acceleration_raw_get(&dev_ctx, buf_raw);
	do {
		delay(20);
		lsm6dso_xl_flag_data_ready_get(&dev_ctx, &drdy);
	} while (!drdy);

	do {
		delay(20);
		lsm6dso_sh_status_get(&dev_ctx, &master_status);
	} while (!master_status.sens_hub_endop);

	/* Disable I2C master and XL(trigger). */
	lsm6dso_sh_master_set(&dev_ctx, PROPERTY_DISABLE);
	lsm6dso_xl_data_rate_set(&dev_ctx, LSM6DSO_XL_ODR_OFF);

	// Read the data from the device
	lsm6dso_sh_read_data_raw_get(&dev_ctx, data, (uint8_t)len);

	/* Re-enable accelerometer */
	lsm6dso_xl_data_rate_set(&dev_ctx, LSM6DSO_XL_ODR_104Hz);

	return ret;
}

static void TerminationHandler(int signalNumber)
{
	// Don't use Log_Debug here, as it is not guaranteed to be async-signal-safe.
	terminationRequired = true;
}

// end I2C

static void AzureTimerEventHandler(EventLoopTimer* timer) // checkup on IoT Hub
{
	if (ConsumeEventLoopTimerEvent(timer) != 0) {
		exitCode = ExitCode_AzureTimer_Consume;
		return;
	}

	bool isNetworkReady = false;
	if (Networking_IsNetworkingReady(&isNetworkReady) != -1) {
		if (isNetworkReady && !iothubAuthenticated) {
			SetupAzureClient();
		}
	}
	else {
		Log_Debug("Failed to get Network state\n");
	}

	if (iothubAuthenticated) {
		//SendSimulatedTemperature();
		IoTHubDeviceClient_LL_DoWork(iothubClientHandle);
	}
}

static void CheckTimeSyncState(void) // check if the time is synched on the device to the cloud
{
	bool isTimeSyncEnabled = false;
	int result = Networking_TimeSync_GetEnabled(&isTimeSyncEnabled);
	if (result != 0)
	{
		Log_Debug("[setup] ERROR: Networking_TimeSync_GetEnabled failed: %s (%d).\n", strerror(errno), errno);
		return;
	}

	// If time sync is enabled, NTP can reset the time
	if (isTimeSyncEnabled)
	{
		println("[setup] RTC online synch is enabled");
	}
	else
	{
		println("[setup] RTC online synch is disabled");
	}
}

void processTime(void) // get the current time
{
	int result = setenv("TZ", "PST-1", timeZone); // check if time zone is appropriately set CHANGE
	if (result == -1)
	{
		Log_Debug("[loop] ERROR: setenv failed with error code: %s (%d).\n", strerror(errno), errno);
		errorLED();
		exit(EXIT_FAILURE);
	}
	else
	{
		tzset(); // call this to synch time
		
		// setup for getting time
		time_t     now;
		struct tm  ts;
		memset(tbuf, 0, 32);

		// Get current time
		time(&now);

		// Format time, "ddd yyyy-mm-dd hh:mm:ss zzz"
		ts = *localtime(&now);
		strftime(tbuf, sizeof(tbuf), "%Y-%m-%dT%H:%M:%S.0Z", &ts); // Power Bi standard format

		Log_Debug("[loop] Time Local  %s \n", tbuf);
	}
}

static void SendTelemetry(int val1, int val2, float val3, int bool1, int bool2, char* time) // send telemetry to IoT Hub
{
	static char eventBuffer[110] = { 0 };
	static const char* EventMsgTemplate = JSONBuffer;
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, "co2", val1, "tvoc", val2, "pressure", val3, "purifier", bool1, "fan", bool2, "time", time);
	if (len < 0)
		return;

	Log_Debug("[loop] Sending IoT Hub Message: %s\n", eventBuffer);

	bool isNetworkingReady = false;
	if ((Networking_IsNetworkingReady(&isNetworkingReady) == -1) || !isNetworkingReady) {
		Log_Debug("[loop] WARNING: Cannot send IoTHubMessage because network is not up.\n");
		return;
	}

	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("[loop] WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("[loop] WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
		Log_Debug("[loop] INFO: IoTHubClient accepted the message for delivery\n");
	}

	println("");
	IoTHubMessage_Destroy(messageHandle);
}

int getAirQuality(void) // get the air quality reading from the module
{
	// variables to store readings in
	int co2temp = 0;
	int tvoctemp = 0;

	println("[loop] Getting Air Quality");
	println("[loop] Calibrating sensor");

	// warm up the sensor by reading 5 times but not storing
	for (int i = 0; i < 5; i++)
	{
		// initialise variables to work with
		uint8_t buff[2] = {};
		int32_t retVal = 0;
		uint8_t sgp30_buffer[6] = {};

		buff[0] = 0x20;
		buff[1] = 0x08;

		// communicate with module
		retVal = I2CMaster_Write(i2cFd, 0x58, buff, 16);
		sleep(1);

		retVal = I2CMaster_Read(i2cFd, 0x58, sgp30_buffer, 6);
		delay(600);
		blinkLED();
	}

	println("[loop] Getting Air Quality");

	// get the values
	for (int i = 0; i < 5; i++)
	{
		// initialise variables to work with
		uint8_t buff[2] = {};
		int32_t retVal = 0;
		uint8_t sgp30_buffer[6] = {};

		buff[0] = 0x20;
		buff[1] = 0x08;

		// communicate with module
		retVal = I2CMaster_Write(i2cFd, 0x58, buff, 16);
		sleep(1);

		retVal = I2CMaster_Read(i2cFd, 0x58, sgp30_buffer, 6);
		co2temp += (sgp30_buffer[0] << 8) | sgp30_buffer[1];
		tvoctemp += (sgp30_buffer[3] << 8) | sgp30_buffer[4];

		Log_Debug("[loop] Values Read: CO2 %d, TVOC %d  \n", co2temp, tvoctemp);

		if (retVal < 0)
		{
			Log_Debug("[loop] ERROR at getAirQuality(): : errno=%d (%s)\n", errno, strerror(errno));
		}

		blinkLED();
		delay(600); // a delay between reads
	}
    
	// find the average
	co2 = (co2temp / 5); // divide by 5 because read 5 times
	tvoc = (tvoctemp / 5); // divide by 5 because read 5 times

	println("");
	Log_Debug("[loop] Final co2 %d \n", co2);
	Log_Debug("[loop] Final tvoc %d \n", tvoc);
	println("");
}

void getPressure(void) // get the barometric pressure from the onboard sensor
{
	uint8_t reg;
	lps22hh_reg_t lps22hhReg;

	println("[loop] Getting Atmospheric Pressure");

	// Initialize the data structures to 0s.
	memset(data_raw_pressure.u8bit, 0x00, sizeof(int32_t));
	memset(data_raw_temperature.u8bit, 0x00, sizeof(int16_t));

	if (lps22hhDetected)
	{
		lps22hh_read_reg(&pressure_ctx, LPS22HH_STATUS, (uint8_t*)&lps22hhReg, 1);

		//Read output only if new value is available
		if ((lps22hhReg.status.p_da == 1) && (lps22hhReg.status.t_da == 1))
		{
			lps22hh_pressure_raw_get(&pressure_ctx, data_raw_pressure.u8bit);

			pressure_hPa = lps22hh_from_lsb_to_hpa(data_raw_pressure.i32bit);
			Log_Debug("[loop] Atmospheric Pressure: %.2f hpa\n", pressure_hPa);
		}
	}
	// LPS22HH was not detected
	else
	{
		println("[loop] ERROR: LPS22hh Module responded with an error");
		errorLED();
		exit(EXIT_FAILURE);
	}

	println("");
}

void sendDataToAzure(void) // our interface to send data to Azure IoT (calls sendTelemetry)
{
	// send the data
	SendTelemetry(co2, tvoc, pressure_hPa, isRelayTvoc, isRelayCo2, tbuf);
	println("");
}

void resetVars(void) // resets the variables once they reach 1000
{
	if (tvoc_goodCount > 1000)
	{
		tvoc_goodCount = 0;
	}

	if (tvoc_badCount > 1000)
	{
		tvoc_badCount = 0;
	}

	if (co2_goodCount > 1000)
	{
		co2_goodCount = 0;
	}

	if (co2_badCount > 1000)
	{
		co2_badCount = 0;
	}
}

int checkData(void) // keep track of the variables and increment them accordingly
{
	// check the values against tresholds
	if (tvoc > tvocTreshold)
	{
		tvoc_badCount++;
		tvoc_goodCount = 0;
	}
	else
	{
		tvoc_goodCount++;
		tvoc_badCount = 0;
	}

	if (co2 > co2Treshold)
	{
		co2_badCount++;
		co2_goodCount = 0;
	}
	else
	{
		co2_goodCount++;
		co2_badCount = 0;
	}

	resetVars();

	println("");
	Log_Debug("tvoc bad      %d \n", tvoc_badCount);
	Log_Debug("tvoc good     %d \n", tvoc_goodCount);
	Log_Debug("co2 bad       %d \n", co2_badCount);
	Log_Debug("co2 good      %d \n", co2_goodCount);
	println("");
}

void relayTvoc(bool on) // toggle relay 1
{
	if (on)
	{
		GPIO_SetValue(r1PinFd, GPIO_Value_High);
	}
	else
	{
		GPIO_SetValue(r1PinFd, GPIO_Value_Low);
	}
}

void relayCo2(bool on) // toggle relay 2
{
	if (on)
	{
		GPIO_SetValue(r2PinFd, GPIO_Value_High);
	}
	else
	{
		GPIO_SetValue(r2PinFd, GPIO_Value_Low);
	}
}

int controlRelays(void) // code to turn relays on and off
{
	if (isRelayTvoc) // if the relay is on
	{
		loopNumberTvoc++;
		Log_Debug("loop tvoc %d \n", loopNumberTvoc);

		if (loopNumberTvoc > 29) // if 1 hour passed since the relay was on
		{
			loopNumberTvoc = 0;
			isRelayTvoc = false;
			isRelayTvocBlocked = true; // block for 1 hour

			// turn relay off
			relayTvoc(false);
		}

		if (tvoc_goodCount > 4) // if air was clean for 10 mins
		{
			loopNumberTvoc = 0;
			isRelayTvoc = false;
			isRelayTvocBlocked = true; // block for 1 hour

			// turn relay off
			relayTvoc(false);
		}
	}
	else
	{
		if (tvoc_badCount > 4) // if air was dirty for 10 minutes
		{
			if (isRelayTvocBlocked)
			{
				loopNumberTvoc++;

				if (loopNumberTvoc > 29) // blocked for 1 hour
				{
					isRelayTvocBlocked = false; // unblock
				}
			}
			else
			{
				isRelayTvoc = true;
				loopNumberTvoc = 0;

				// turn relay on
				relayTvoc(true);
			}
		}
	}

	if (isRelayCo2) // if the relay is on
	{
		loopNumberCo2++;
		Log_Debug("loop co2  %d \n", loopNumberCo2);

		if (loopNumberCo2 > 29) // if 1 hour passed since the relay was on
		{
			loopNumberCo2 = 0;
			isRelayCo2 = false;
			isRelayCo2Blocked = true; // block for 1 hour

			// turn relay off
			relayCo2(false);
		}

		if (co2_goodCount > 4) // if air was clean for 10 mins
		{
			loopNumberCo2 = 0;
			isRelayCo2 = false;
			isRelayCo2Blocked = true; // block for 1 hour

			// turn relay off
			relayCo2(false);
		}
	}
	else
	{
		if (co2_badCount > 4) // if air was dirty for 10 minutes
		{
			if (isRelayCo2Blocked)
			{
				loopNumberCo2++;

				if (loopNumberCo2 > 29) // blocked for 1 hour
				{
					isRelayCo2Blocked = false; // unblock
				}
			}
			else
			{
				isRelayCo2 = true;
				loopNumberCo2 = 0;

				// turn relay on
				relayCo2(true);
			}
		}
	}
}

void blinkLED(void)
{
	GPIO_SetValue(fd, GPIO_Value_Low);
	delay(1000);

	GPIO_SetValue(fd, GPIO_Value_High);
	delay(1000);
}

void errorLED(void)
{
	GPIO_SetValue(fd, GPIO_Value_High);
}

static ExitCode InitPeripheralsAndHandlers(void) // initialise the code for the program
{
	struct sigaction action;
	memset(&action, 0, sizeof(struct sigaction));
	action.sa_handler = TerminationHandler;
	sigaction(SIGTERM, &action, NULL);

	eventLoop = EventLoop_Create();
	if (eventLoop == NULL)
	{
		Log_Debug("[setup] Could not create event loop.\n");
		return ExitCode_Init_EventLoop;
	}

	Log_Debug("[setup] Setting Up GPIOs \n");
	Log_Debug("[setup] Opening GPIO 9 \n");
	fd = GPIO_OpenAsOutput(9, GPIO_OutputMode_PushPull, GPIO_Value_High); // open the GPIO pin as an output

	// check if the pin was opened successfully
	if (fd < 0)
	{
		Log_Debug("[setup] ERROR: GPIO Failed to Open \n");
		return -1;
	}

	Log_Debug("[setup] GPIO 9 is Open \n");

	println("[setup] Initialising Relay Click Pins");
	r1PinFd = GPIO_OpenAsOutput(MIKROE_PWM, relay1Pin, GPIO_Value_Low);
	r2PinFd = GPIO_OpenAsOutput(MIKROE_CS, relay2Pin, GPIO_Value_Low);

	println("[setup] Setting up RTC");
	CheckTimeSyncState();
	println("[setup] RTC is up and running");

	if (r1PinFd < 0 || r2PinFd < 0)
	{
		Log_Debug("[Setup] ERROR: Pins not opened successfully");
		Log_Debug("[Setup] Check app manifest and reflash app");
		exit(EXIT_FAILURE); // exit app
	}

	println("[setup] Relay is connected");
	println("[setup] Initialising I2C interface");
	if (initI2c() == -1)
	{
		return -1;
	}

	println("[setup] I2C Online");

	println("[setup] setting up connection to Azure IoT Hub");
	azureIoTPollPeriodSeconds = AzureIoTDefaultPollPeriodSeconds;
	struct timespec azureTelemetryPeriod = { .tv_sec = azureIoTPollPeriodSeconds, .tv_nsec = 0 };
	azureTimer = CreateEventLoopPeriodicTimer(eventLoop, &AzureTimerEventHandler, &azureTelemetryPeriod);

	if (azureTimer == NULL)
	{
		println("[setup] ERROR: Setup Failed");
		return ExitCode_Init_AzureTimer;
	}

	println("[setup] IoT Hub Ready");
	return ExitCode_Success;
}

int main(int argc, char *argv[])
{
    logoStart("IntlAir");

    // check if connected and everything is online
    bool isNetworkingReady = false;
    if ((Networking_IsNetworkingReady(&isNetworkingReady) == -1) || !isNetworkingReady) 
    {
        Log_Debug("[setup] WARNING: Network is not ready. Device cannot connect until network is ready.\n");
    }

    if (argc == 2) {
        Log_Debug("[setup] Setting Azure Scope ID %s\n", argv[1]);
        strncpy(scopeId, argv[1], SCOPEID_LENGTH);
    } else {
        Log_Debug("[setup] ERROR: ScopeId needs to be set in the app_manifest CmdArgs\n");
        return -1;
    }

    exitCode = InitPeripheralsAndHandlers(); // prepare the program
    println("");
    println("");

    // Main loop
    while (exitCode == ExitCode_Success) 
    {
		// get the time
		processTime();
		blinkLED();

		// get the air quality and pressure
		getAirQuality();
		getPressure();
		blinkLED();

		// check to see if the values are ok
		checkData();
		blinkLED();

		// control the relays
		controlRelays();
		blinkLED();

		// send telemetry to Azure IoT
		sendDataToAzure();
		blinkLED();

		println("");

		// sleep for 2 minutes between reads, keep live connection with Azure
		struct timeval time_start, time_now;

		gettimeofday(&time_start, NULL); // setup timer
		time_now = time_start;

		while (difftime(time_now.tv_sec, time_start.tv_sec) < sleepTime)
		{
			EventLoop_Run_Result result = EventLoop_Run(eventLoop, -1, true);
			// Continue if interrupted by signal, e.g. due to breakpoint being set.
			if (result == EventLoop_Run_Failed && errno != EINTR)
			{
				exitCode = ExitCode_Main_EventLoopFail;
			}

			gettimeofday(&time_now, NULL); // get the time
			print(".");
			delay(1000);
		}

		println("");
    }

	// runs if error
    ClosePeripheralsAndHandlers(); // prepare shutdown
	errorLED();
    println("[loop] Application closing");
    return exitCode;
}

// others - from AzureIoT sample
static void CloseFdAndPrintError(int fd, const char *fdName)
{
    if (fd >= 0) {
        int result = close(fd);
        if (result != 0) {
            Log_Debug("[loop] ERROR: Could not close fd %s: %s (%d).\n", fdName, strerror(errno), errno);
        }
    }
}

static void ClosePeripheralsAndHandlers(void)
{
    DisposeEventLoopTimer(buttonPollTimer);
    DisposeEventLoopTimer(azureTimer);
    EventLoop_Close(eventLoop);

    Log_Debug("[loop] Closing file descriptors\n");
}

static void HubConnectionStatusCallback(IOTHUB_CLIENT_CONNECTION_STATUS result,
                                        IOTHUB_CLIENT_CONNECTION_STATUS_REASON reason,
                                        void *userContextCallback)
{
    iothubAuthenticated = (result == IOTHUB_CLIENT_CONNECTION_AUTHENTICATED);
    Log_Debug("[setup] IoT Hub Authenticated: %s\n", GetReasonString(reason));
}

static void SetupAzureClient(void)
{
    if (iothubClientHandle != NULL) {
        IoTHubDeviceClient_LL_Destroy(iothubClientHandle);
    }

    AZURE_SPHERE_PROV_RETURN_VALUE provResult =
        IoTHubDeviceClient_LL_CreateWithAzureSphereDeviceAuthProvisioning(scopeId, 10000,
                                                                          &iothubClientHandle);
    Log_Debug("[loop] IoTHubDeviceClient_LL_CreateWithAzureSphereDeviceAuthProvisioning returned '%s'.\n",
              getAzureSphereProvisioningResultString(provResult));

    if (provResult.result != AZURE_SPHERE_PROV_RESULT_OK) {

        // If we fail to connect, reduce the polling frequency, starting at
        // AzureIoTMinReconnectPeriodSeconds and with a backoff up to
        // AzureIoTMaxReconnectPeriodSeconds
        if (azureIoTPollPeriodSeconds == AzureIoTDefaultPollPeriodSeconds) {
            azureIoTPollPeriodSeconds = AzureIoTMinReconnectPeriodSeconds;
        } else {
            azureIoTPollPeriodSeconds *= 2;
            if (azureIoTPollPeriodSeconds > AzureIoTMaxReconnectPeriodSeconds) {
                azureIoTPollPeriodSeconds = AzureIoTMaxReconnectPeriodSeconds;
            }
        }

        struct timespec azureTelemetryPeriod = {azureIoTPollPeriodSeconds, 0};
        SetEventLoopTimerPeriod(azureTimer, &azureTelemetryPeriod);

        Log_Debug("[setup] ERROR: failure to create IoTHub Handle - will retry in %i seconds.\n",
                  azureIoTPollPeriodSeconds);
        return;
    }

    // Successfully connected, so make sure the polling frequency is back to the default
    azureIoTPollPeriodSeconds = AzureIoTDefaultPollPeriodSeconds;
    struct timespec azureTelemetryPeriod = {.tv_sec = azureIoTPollPeriodSeconds, .tv_nsec = 0};
    SetEventLoopTimerPeriod(azureTimer, &azureTelemetryPeriod);

    iothubAuthenticated = true;

    if (IoTHubDeviceClient_LL_SetOption(iothubClientHandle, OPTION_KEEP_ALIVE,
                                        &keepalivePeriodSeconds) != IOTHUB_CLIENT_OK) {
        Log_Debug("[setup] ERROR: failure setting option \"%s\"\n", OPTION_KEEP_ALIVE);
        return;
    }

    IoTHubDeviceClient_LL_SetDeviceTwinCallback(iothubClientHandle, TwinCallback, NULL);
    IoTHubDeviceClient_LL_SetConnectionStatusCallback(iothubClientHandle,
                                                      HubConnectionStatusCallback, NULL);
}

static void TwinCallback(DEVICE_TWIN_UPDATE_STATE updateState, const unsigned char *payload,
                         size_t payloadSize, void *userContextCallback)
{
    size_t nullTerminatedJsonSize = payloadSize + 1;
    char *nullTerminatedJsonString = (char *)malloc(nullTerminatedJsonSize);
    if (nullTerminatedJsonString == NULL) {
        Log_Debug("[setup] ERROR: Could not allocate buffer for twin update payload.\n");
        abort();
    }

    // Copy the provided buffer to a null terminated buffer.
    memcpy(nullTerminatedJsonString, payload, payloadSize);
    // Add the null terminator at the end.
    nullTerminatedJsonString[nullTerminatedJsonSize - 1] = 0;

    JSON_Value *rootProperties = NULL;
    rootProperties = json_parse_string(nullTerminatedJsonString);
    if (rootProperties == NULL) {
        Log_Debug("[setup] WARNING: Cannot parse the string as JSON content.\n");
        goto cleanup;
    }

    JSON_Object *rootObject = json_value_get_object(rootProperties);
    JSON_Object *desiredProperties = json_object_dotget_object(rootObject, "desired");
    if (desiredProperties == NULL) {
        desiredProperties = rootObject;
    }

cleanup:
    // Release the allocated memory.
    json_value_free(rootProperties);
    free(nullTerminatedJsonString);
}

static const char *GetReasonString(IOTHUB_CLIENT_CONNECTION_STATUS_REASON reason)
{
    static char *reasonString = "unknown reason";
    switch (reason) {
    case IOTHUB_CLIENT_CONNECTION_EXPIRED_SAS_TOKEN:
        reasonString = "IOTHUB_CLIENT_CONNECTION_EXPIRED_SAS_TOKEN";
        break;
    case IOTHUB_CLIENT_CONNECTION_DEVICE_DISABLED:
        reasonString = "IOTHUB_CLIENT_CONNECTION_DEVICE_DISABLED";
        break;
    case IOTHUB_CLIENT_CONNECTION_BAD_CREDENTIAL:
        reasonString = "IOTHUB_CLIENT_CONNECTION_BAD_CREDENTIAL";
        break;
    case IOTHUB_CLIENT_CONNECTION_RETRY_EXPIRED:
        reasonString = "IOTHUB_CLIENT_CONNECTION_RETRY_EXPIRED";
        break;
    case IOTHUB_CLIENT_CONNECTION_NO_NETWORK:
        reasonString = "IOTHUB_CLIENT_CONNECTION_NO_NETWORK";
        break;
    case IOTHUB_CLIENT_CONNECTION_COMMUNICATION_ERROR:
        reasonString = "IOTHUB_CLIENT_CONNECTION_COMMUNICATION_ERROR";
        break;
    case IOTHUB_CLIENT_CONNECTION_OK:
        reasonString = "IOTHUB_CLIENT_CONNECTION_OK";
        break;
    }
    return reasonString;
}

static const char *getAzureSphereProvisioningResultString(
    AZURE_SPHERE_PROV_RETURN_VALUE provisioningResult)
{
    switch (provisioningResult.result) {
    case AZURE_SPHERE_PROV_RESULT_OK:
        return "AZURE_SPHERE_PROV_RESULT_OK";
    case AZURE_SPHERE_PROV_RESULT_INVALID_PARAM:
        return "AZURE_SPHERE_PROV_RESULT_INVALID_PARAM";
    case AZURE_SPHERE_PROV_RESULT_NETWORK_NOT_READY:
        return "AZURE_SPHERE_PROV_RESULT_NETWORK_NOT_READY";
    case AZURE_SPHERE_PROV_RESULT_DEVICEAUTH_NOT_READY:
        return "AZURE_SPHERE_PROV_RESULT_DEVICEAUTH_NOT_READY";
    case AZURE_SPHERE_PROV_RESULT_PROV_DEVICE_ERROR:
        return "AZURE_SPHERE_PROV_RESULT_PROV_DEVICE_ERROR";
    case AZURE_SPHERE_PROV_RESULT_GENERIC_ERROR:
        return "AZURE_SPHERE_PROV_RESULT_GENERIC_ERROR";
    default:
        return "UNKNOWN_RETURN_VALUE";
    }
}

static void SendMessageCallback(IOTHUB_CLIENT_CONFIRMATION_RESULT result, void *context)
{
    Log_Debug("[loop] INFO: Message received by IoT Hub. Result is: %d\n", result);
}

static void TwinReportBoolState(const char *propertyName, bool propertyValue)
{
    if (iothubClientHandle == NULL) {
        Log_Debug("[loop] ERROR: client not initialized\n");
    } else {
        static char reportedPropertiesString[30] = {0};
        int len = snprintf(reportedPropertiesString, 30, "{\"%s\":%s}", propertyName,
                           (propertyValue == true ? "true" : "false"));
        if (len < 0)
            return;

        if (IoTHubDeviceClient_LL_SendReportedState(
                iothubClientHandle, (unsigned char *)reportedPropertiesString,
                strlen(reportedPropertiesString), ReportStatusCallback, 0) != IOTHUB_CLIENT_OK) {
            Log_Debug("[loop] ERROR: failed to set reported state for '%s'.\n", propertyName);
        } else {
            Log_Debug("[loop] INFO: Reported state for '%s' to value '%s'.\n", propertyName,
                      (propertyValue == true ? "true" : "false"));
        }
    }
}

static void ReportStatusCallback(int result, void *context)
{
    Log_Debug("INFO: Device Twin reported properties update result: HTTP status code %d\n", result);
}
