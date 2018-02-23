d := $(dir $(lastword $(MAKEFILE_LIST)))

#
# gtest-based tests
#
GTEST_SRCS += $(addprefix $(d), \
		kvstore-test.cc \
		versionstore-test.cc \
		lockserver-test.cc)

$(d)kvstore-test: $(o)kvstore-test.o $(LIB-transport) $(LIB-store-common) $(LIB-store-backend) $(GTEST_MAIN)

TEST_BINS += $(d)kvstore-test

$(d)versionstore-test: $(o)versionstore-test.o $(LIB-transport) $(LIB-store-common) $(LIB-store-backend) $(GTEST_MAIN)

TEST_BINS += $(d)versionstore-test

$(d)lockserver-test: $(o)lockserver-test.o $(LIB-transport) $(LIB-store-common) $(LIB-store-backend) $(GTEST_MAIN)

TEST_BINS += $(d)lockserver-test
