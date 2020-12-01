#include "wu.h"
#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/ioctl.h>

ioctl_get_msg(int file_desc) {
	int ret_val;
	char message[1000];
	int i;
	int temp = 0;

	ret_val = ioctl(file_desc, IOCTL_GET_MSG, message);
	if(ret_val < 0) {
		printf("ioctl_get_pid failed:%d\n", ret_val);
		exit(-1);
	}

	printf("%s", message);
}

main() {
	int fd, ret_val;
	fd = open(DEVICE_NAME, 0);
	if(fd < 0) {
		printf("Can't open file device: %s\n", DEVICE_NAME);
		exit(-1);
	}
	ioctl_get_msg(fd);
	close(fd);
}
