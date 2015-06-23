d := $(dir $(lastword $(MAKEFILE_LIST)))

GTEST_SRCS += $(d)vr-test.cc

$(d)vr-test: $(o)vr-test.o \
	$(OBJS-vr-replica) $(OBJS-vr-client) \
	$(LIB-simtransport) \
	$(GTEST_MAIN)

TEST_BINS += $(d)vr-test
