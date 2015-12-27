d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), \
	client.cc replica.cc log.cc)

PROTOS += $(addprefix $(d), \
	    request.proto)

LIB-request := $(o)request.o

OBJS-client := $(o)client.o \
               $(LIB-message) $(LIB-configuration) \
               $(LIB-transport) $(LIB-request)

OBJS-replica := $(o)replica.o $(o)log.o \
                $(LIB-message) $(LIB-request) \
                $(LIB-configuration) $(LIB-udptransport)

include $(d)tests/Rules.mk
