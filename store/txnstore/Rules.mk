d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), \
	client.cc shardclient.cc server.cc)

PROTOS += $(addprefix $(d), txn-proto.proto)

OBJS-txn-store := $(LIB-message) $(LIB-common) \
$(LIB-backend) $(o)server.o \
$(o)txn-proto.o

OBJS-txn-client := $(o)txn-proto.o $(o)shardclient.o $(o)client.o

include $(d)lib/Rules.mk

$(d)client: $(LIB-udptransport) $(LIB-request) $(LIB-common) \
  $(LIB-latency) $(OBJS-vr-client) $(OBJS-txn-client)

$(d)server: $(LIB-udptransport) $(LIB-txnstore) \
  $(OBJS-vr-replica) $(OBJS-txn-store)

BINS += $(d)server
