d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), server.cc client.cc)

PROTOS += $(addprefix $(d), locks-proto.proto)

$(d)server: $(LIB-udptransport) $(OBJS-ir-replica) $(o)locks-proto.o $(o)server.o

$(d)client: $(LIB-udptransport) $(OBJS-ir-client) $(LIB-common) $(o)locks-proto.o $(o)client.o

BINS += $(d)server $(d)client
