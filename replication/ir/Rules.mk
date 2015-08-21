d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), \
	record.cc)

PROTOS += $(addprefix $(d), \
	    ir-proto.proto)

OBJS-ir-client :=  $(o)ir-proto.o \
                   $(OBJS-client) $(LIB-message) \
                   $(LIB-configuration)

OBJS-ir-replica := $(o)record.o $(o)ir-proto.o \
                   $(OBJS-replica) $(LIB-message) \
                   $(LIB-configuration)

#include $(d)tests/Rules.mk

