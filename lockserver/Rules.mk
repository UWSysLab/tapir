d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), \
			server.cc client.cc server-main.cc client-main.cc \
			lockserver-repl.cc)

PROTOS += $(addprefix $(d), locks-proto.proto)

$(d)server-main: $(o)server-main.o \
	$(o)locks-proto.o \
	$(o)server.o \
	$(LIB-udptransport) \
	$(OBJS-ir-replica)

$(d)client-main: $(o)client-main.o \
	$(o)locks-proto.o \
	$(o)client.o \
	$(LIB-udptransport) \
   	$(OBJS-ir-client) \
   	$(LIB-store-common)

$(d)lockserver-repl: $(o)lockserver-repl.o \
	$(o)locks-proto.o \
	$(o)server.o \
	$(o)client.o \
	$(OBJS-ir-replica) \
	$(OBJS-ir-client) \
	$(LIB-configuration) \
	$(LIB-repltransport) \
   	$(LIB-store-common) \
	$(GTEST_MAIN)

BINS += $(d)server-main $(d)client-main $(d)lockserver-repl

include $(d)tests/Rules.mk
