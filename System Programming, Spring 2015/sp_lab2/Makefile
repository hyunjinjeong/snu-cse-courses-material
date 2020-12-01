obj-m += msrdrv.o
obj-m += wu.o

all: wu_ioctl msrtest
	make -C /lib/modules/$(shell uname -r)/build M=$(PWD) -I. modules
	sudo mknod /dev/msrdrv c 223 0
	sudo mknod ./Warming_Up c 2013 0
	sudo chmod 666 /dev/msrdrv
	sudo insmod -f msrdrv.ko
	sudo insmod -f wu.ko

wu_ioctl: wu_ioctl.o
	gcc -o wu_ioctl wu_ioctl.o

wu_ioctl.o: wu_ioctl.c
	gcc -c wu_ioctl.c

msrtest: msrtest.o
	gcc -g -I. -o msrtest msrtest.o

msrtest.o: msrtest.c
	gcc -c msrtest.c

run1:
	./wu_ioctl

run2:
	./msrtest

submission:
	tar cvf 2013-11431_HyunjinJeong.tar Makefile msrtest.c msrdrv.c msrdrv.h wu.c wu.h wu_ioctl.c

clean:
	rm -f *.ko *.o *.order *.symvers msrdrv.mod.c wu_ioctl wu.mod.c msrtest *.tar
	sudo rmmod msrdrv
	sudo rmmod wu
	sudo rm /dev/msrdrv
	sudo rm ./Warming_Up
