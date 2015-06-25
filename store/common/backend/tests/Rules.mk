d := $(dir $(lastword $(MAKEFILE_LIST)))

#
# gtest-based tests
#
GTEST_SRCS += $(addprefix $(d), \
		kvstore-test.cc)

$(d)kvstore-test: $(o)kvstore-test.o $(LIB-transport) $(LIB-common) $(LIB-backend) $(GTEST_MAIN)

TEST_BINS += $(d)kvstore-test