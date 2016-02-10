d := $(dir $(lastword $(MAKEFILE_LIST)))

$(d)libtapir.so: $(patsubst %.o,%-pic.o, $(LIB-message) $(LIB-store-common) $(LIB-store-frontend) $(LIB-udptransport) $(OBJS-tapir-client))
LDFLAGS-$(d)libtapir.so += -shared

BINS += $(d)libtapir.so
