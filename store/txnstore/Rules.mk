d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), \
	client.cc spanclient.cc lockserver.cc \
	occstore.cc lockstore.cc server.cc)

PROTOS += $(addprefix $(d), span-proto.proto)

OBJS-span-store := $(LIB-message) $(LIB-store) $(LIB-common) $(o)server.o \
  $(o)occstore.o $(o)lockstore.o $(o)lockserver.o $(o)span-proto.o

OBJS-span-client := $(LIB-udptransport) $(LIB-request) $(LIB-common) \
  $(LIB-latency) $(OBJS-vr-client) $(o)span-proto.o $(o)spanclient.o $(o)client.o

$(d)server: $(LIB-udptransport) $(OBJS-span-store) \
  $(OBJS-vr-replica) $(OBJS-span-store)

BINS += $(d)server
