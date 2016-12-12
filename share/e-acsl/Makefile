obj-m += e_acsl.o
EXTRA_CFLAGS := -Wno-attributes

all:
	 make -C /lib/modules/$(shell uname -r)/build M=$(PWD) modules

clean:
	 make -C /lib/modules/$(shell uname -r)/build M=$(PWD) clean
