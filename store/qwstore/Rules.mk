d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), \
  client.cc qwclient.cc \
  qwstore.cc replica.cc server.cc )

PROTOS += $(addprefix $(d), qw-proto.proto)

OBJS-qw-store := $(LIB-store) $(o)qw-proto.o $(o)qwstore.o $(o)server.o

OBJS-qw-client := $(LIB-message) $(LIB-udptransport) $(LIB-request) $(LIB-common) \
  $(LIB-client) $(o)qw-proto.o $(o)qwclient.o $(o)client.o 

$(d)server: $(LIB-message) $(LIB-udptransport) $(LIB-request) \
	$(LIB-common) $(OBJS-qw-store) $(o)replica.o

BINS += $(d)server
