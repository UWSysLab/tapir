d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), timeserver.cc)

$(d)timeserver: $(o)timeserver.o $(OBJS-vr-replica) $(LIB-rdmatransport) $(LIB-zeustransport) $(LIB-tcptransport) $(LIB-udptransport)

BINS += $(d)timeserver
