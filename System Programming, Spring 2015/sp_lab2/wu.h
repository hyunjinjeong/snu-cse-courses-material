#ifndef WU_H
#define WU_H

#include <linux/ioctl.h>

#define MAJOR_NUM 2013
#define IOCTL_GET_MSG _IOR(MAJOR_NUM, 0, char *)

#define DEVICE_NAME "Warming_Up"

#endif
