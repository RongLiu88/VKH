KERNEL_MODULE_NAME := vmx-switch
KERNELDIR:=/lib/modules/$(shell uname -r)/build
PWD=$(shell pwd)

INCLUDES = -I.

ccflags-y += $(INCLUDES) -ggdb -O0
#ccflags-y += $(INCLUDES) -ggdb

obj-m += vmx-switch.o

vmx-switch-y := cpu_switch.o  vmexit.o ptable.o kernelhardening.o

all:
	$(MAKE) -C $(KERNELDIR) M=$(PWD)

clean:
	$(MAKE) -C $(KERNELDIR) M=$(PWD) clean

install:
	$(MAKE) -C $(KERNELDIR) M=$(PWD) modules_install
