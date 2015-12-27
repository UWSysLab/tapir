d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), client.cc shardclient.cc qwstore.cc server.cc)

PROTOS += $(addprefix $(d), qw-proto.proto)

OBJS-qw-server := $(LIB-message) $(LIB-udptransport) $(LIB-request) \
									$(LIB-store-common) $(LIB-store-backend) \
									$(o)qw-proto.o $(o)qwstore.o $(o)server.o

OBJS-qw-client := $(LIB-message) $(LIB-udptransport) $(LIB-request) $(LIB-store-frontend) \
									$(o)qw-proto.o $(o)shardclient.o $(o)client.o 

$(d)server: $(OBJS-qw-server)

BINS += $(d)server
