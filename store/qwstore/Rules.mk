d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), client.cc shardclient.cc qwstore.cc server.cc)

PROTOS += $(addprefix $(d), qw-proto.proto)

OBJS-qw-server := $(LIB-backend) $(o)qw-proto.o $(o)qwstore.o $(o)server.o

OBJS-qw-client := $(LIB-message) $(LIB-udptransport) $(LIB-request) $(LIB-common) \
  $(LIB-frontend) $(o)qw-proto.o $(o)shardclient.o $(o)client.o 

$(d)server: $(LIB-message) $(LIB-udptransport) $(LIB-request) $(LIB-common) $(OBJS-qw-server)

BINS += $(d)server
