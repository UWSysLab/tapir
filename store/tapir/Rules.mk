d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), client.cc shardclient.cc \
													server.cc tapirstore.cc)

PROTOS += $(addprefix $(d), tapir-proto.proto)


OBJS-tapir-store := $(LIB-message) $(LIB-store-common) $(LIB-store-backend) \
										$(o)tapir-proto.o $(o)tapirstore.o 

OBJS-tapir-client := $(o)tapir-proto.o $(o)shardclient.o $(o)client.o

$(d)client: $(LIB-udptransport) $(LIB-request) $(LIB-store-common) \
  					$(LIB-latency) $(OBJS-ir-client) $(OBJS-tapir-client)

$(d)server: $(LIB-udptransport) $(OBJS-ir-replica) \
						$(OBJS-tapir-store) $(o)server.o

BINS += $(d)server
