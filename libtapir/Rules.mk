d := $(dir $(lastword $(MAKEFILE_LIST)))

$(d)libtapir.so: $(patsubst %.o,%-pic.o, $(OBJS-or-client) $(OBJS-span-client) $(OBJS-qw-client))
LDFLAGS-$(d)libtapir.so += -shared

BINS += $(d)libtapir.so
