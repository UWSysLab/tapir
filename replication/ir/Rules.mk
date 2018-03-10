d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), \
		record.cc client.cc replica.cc)

PROTOS += $(addprefix $(d), \
	    ir-proto.proto)

OBJS-ir-client :=  $(o)ir-proto.o $(o)client.o \
                   $(OBJS-client) $(LIB-message) \
                   $(LIB-configuration)

OBJS-ir-replica := $(o)record.o $(o)replica.o $(o)ir-proto.o \
                   $(OBJS-replica) $(LIB-message) \
                   $(LIB-configuration) $(LIB-persistent_register)

include $(d)tests/Rules.mk

