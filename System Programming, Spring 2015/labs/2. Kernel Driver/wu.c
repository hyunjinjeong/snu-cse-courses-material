#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/sched.h>
#include <linux/fs.h>
#include <linux/string.h>
#include "wu.h"

MODULE_LICENSE("GPL");

#define SUCCESS 0
#define DEVICE_NAME "Warming_Up"
#define BUF_LEN 1000

static int Device_Open = 0;
struct task_struct *task;

static int device_open(struct inode *inode, struct file *filp) {
	if(Device_Open) return -EBUSY;
	Device_Open++;
	try_module_get(THIS_MODULE);
	return SUCCESS;
}

static int device_release(struct inode *inode, struct file *filp) {
	Device_Open--;
	module_put(THIS_MODULE);
	return SUCCESS;
}

static ssize_t device_read(struct file *filp, char __user *buffer, size_t length, loff_t *offset) {
	return NULL;
}

static ssize_t device_write(struct file *filp, char __user *buffer, size_t length, loff_t *offset) {
	return NULL;
}

static long device_ioctl(struct file *filp, unsigned int cmd, unsigned long args) {
	int i;
	char pid[50];
	char args2[1000];
	task = current;

	switch(cmd) {
		case IOCTL_GET_MSG:

			sprintf(pid, "%d", task->pid);
			strcpy((char *)args, "-/");
			strcat((char *)args, task->comm);
			strcat((char *)args, "(");
			strcat((char *)args, pid);
			strcat((char *)args, ")\n");
			
			do {
				task = task->parent;
				
				sprintf(pid, "%d", task->pid);
				strcpy(args2, "");
				if(task->pid != 0)strcat(args2, "-/");
				strcat(args2, task->comm);
				strcat(args2, "(");
				strcat(args2, pid);
				strcat(args2, ")\n  ");
				strcat(args2, (char *)args);
				strcpy((char *)args, args2);
			
				} while (task->pid != 0);

				i = device_read(filp, (char *)args, 999, 0);
				put_user('\0', (char *)args + 999);

			break;
			}
	return SUCCESS;
}

struct file_operations Fops = {
	.read = device_read,
	.write = device_write,
	.unlocked_ioctl = device_ioctl,
	.open = device_open,
	.release = device_release
};

int init_module() {
	int ret_val;
	ret_val = register_chrdev(MAJOR_NUM, DEVICE_NAME, &Fops);
	if(ret_val < 0) {
		printk(KERN_ALERT "%s failed with %d\n",
			"Sorry, registering the character device", ret_val);
		return ret_val;
	}
	return SUCCESS;
}

void cleanup_module() {
	printk("Bye Bye!\n");
	unregister_chrdev(MAJOR_NUM, DEVICE_NAME);
}
