d := $(dir $(lastword $(MAKEFILE_LIST)))

GTEST_SRCS += $(addprefix $(d), lockserver-test.cc)

$(d)lockserver-test: $(o)lockserver-test.o \
	$(o)../locks-proto.o \
	$(o)../server.o \
	$(o)../client.o \
	$(OBJS-ir-replica) \
	$(OBJS-ir-client) \
	$(LIB-configuration) \
	$(LIB-repltransport) \
   	$(LIB-store-common) \
	$(GTEST_MAIN)

TEST_BINS += $(d)lockserver-test
