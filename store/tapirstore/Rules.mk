d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), client.cc shardclient.cc \
	server.cc store.cc)

PROTOS += $(addprefix $(d), tapir-proto.proto)

OBJS-tapir-store := $(LIB-message) $(LIB-store-common) $(LIB-store-backend) \
	$(o)tapir-proto.o $(o)store.o 

OBJS-tapir-client := $(OBJS-ir-client)  $(LIB-udptransport) $(LIB-store-frontend) $(LIB-store-common) $(o)tapir-proto.o \
		$(o)shardclient.o $(o)client.o

$(d)server: $(LIB-udptransport) $(OBJS-ir-replica) \
		$(OBJS-tapir-store) $(o)server.o

BINS += $(d)server
