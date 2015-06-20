d := $(dir $(lastword $(MAKEFILE_LIST)))

#
# gtest-based tests
#
GTEST_SRCS += $(addprefix $(d), \
		configuration-test.cc \
	        simtransport-test.cc)

PROTOS += $(d)simtransport-testmessage.proto

$(d)configuration-test: $(o)configuration-test.o $(LIB-configuration) $(GTEST_MAIN)

TEST_BINS += $(d)configuration-test

$(d)simtransport-test: $(o)simtransport-test.o $(LIB-simtransport) $(o)simtransport-testmessage.o $(GTEST_MAIN)

TEST_BINS += $(d)simtransport-test
