/*
	universum_utilities
	13/OCT/2019 | Andrei Florian
*/

#pragma once

#include <errno.h>
#include <signal.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h> 
#include <time.h>
#include <unistd.h>
#include <stdio.h>
#include <math.h>

#include "applibs_versions.h"
#include <applibs/log.h>

// utility to simply put the device to sleep for an amount of time
// timeToSleep - time to sleep in MILLISECONDS
void delay(float timeToSleep)
{
    struct timespec ts;
    ts.tv_sec = 0;
    ts.tv_nsec = timeToSleep * 10000;
    nanosleep(&ts, NULL);
}



void println(char dataToPrint[])
{
	Log_Debug(dataToPrint);
	Log_Debug("\n");
}

void print(char dataToPrint[])
{
	Log_Debug(dataToPrint);
}

void logoStart(char projectName[])
{
	delay(200);
    Log_Debug("\n");
    
    delay(100);
    Log_Debug("    / /          / /    \n");
    Log_Debug("    / /          / /    \n");
    Log_Debug("    / /          / /    \n");
    Log_Debug("    / /          / /    \n");
    Log_Debug("    / /          / /    \n");
    Log_Debug("    / /          / /    \n");
    Log_Debug("    / /          / /    \n");
    Log_Debug("        / / / /         \n");
    
    Log_Debug("\n");
    Log_Debug("       Universum\n");
    Log_Debug("  Expanding Boundaries\n");
    Log_Debug("\n");
    
    delay(200);
    Log_Debug(projectName);
    
    Log_Debug("\n");
    Log_Debug("\n");
}