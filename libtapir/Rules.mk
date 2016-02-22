d := $(dir $(lastword $(MAKEFILE_LIST)))

$(d)libtapir.so: $(patsubst %.o,%-pic.o, $(OBJS-all-clients))
LDFLAGS-$(d)libtapir.so += -shared

BINS += $(d)libtapir.so
