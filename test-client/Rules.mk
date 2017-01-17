d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), test-client.cc)

PROTOS += $(addprefix $(d), test-client-proto.proto)

$(d)test-client: $(LIB-message) $(LIB-tcptransport) $(LIB-udptransport) $(o)test-client-proto.o $(o)test-client.o

BINS += $(d)test-client
