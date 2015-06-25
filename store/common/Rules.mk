d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), \
	timestamp.cc transaction.cc promise.cc tracer.cc truetime.cc)

PROTOS += $(addprefix $(d), common-proto.proto)

LIB-common := $(o)timestamp.o $(o)transaction.o $(o)promise.o $(o)truetime.o $(o)common-proto.o $(o)tracer.o

include store/common/frontend/Rules.mk
include store/common/backend/Rules.mk
