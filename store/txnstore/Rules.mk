d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), occstore.cc lockstore.cc server.cc \
					client.cc shardclient.cc)

PROTOS += $(addprefix $(d), txn-proto.proto)

LIB-txnstore := $(o)occstore.o $(o)lockstore.o

OBJS-txn-store := $(LIB-message) $(LIB-txnstore) $(LIB-store-common) \
									$(LIB-store-backend) $(o)txn-proto.o $(o)server.o

OBJS-txn-client := $(o)txn-proto.o $(o)shardclient.o $(o)client.o

$(d)server: $(LIB-udptransport) $(OBJS-vr-replica) $(OBJS-txn-store)

BINS += $(d)server
