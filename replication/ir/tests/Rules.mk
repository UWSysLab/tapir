d := $(dir $(lastword $(MAKEFILE_LIST)))

GTEST_SRCS += $(d)ir-test.cc

$(d)ir-test: $(o)ir-test.o \
	$(OBJS-ir-replica) $(OBJS-ir-client) \
	$(LIB-simtransport) \
	$(GTEST_MAIN)

TEST_BINS += $(d)ir-test
