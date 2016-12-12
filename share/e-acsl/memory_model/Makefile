obj-m += e_acsl_memory_model.o
e_acsl_memory_model-objs := e_acsl_mmodel.o e_acsl_bittree.o
EXTRA_CFLAGS := -Wno-attributes -Wno-undef

all:
	 make -C /lib/modules/$(shell uname -r)/build M=$(PWD) modules

clean:
	 make -C /lib/modules/$(shell uname -r)/build M=$(PWD) clean
