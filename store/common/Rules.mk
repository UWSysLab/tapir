d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), promise.cc timestamp.cc tracer.cc \
				transaction.cc truetime.cc)

PROTOS += $(addprefix $(d), common-proto.proto)

LIB-store-common := $(o)common-proto.o $(o)promise.o $(o)timestamp.o \
							$(o)tracer.o $(o)transaction.o $(o)truetime.o

include $(d)backend/Rules.mk $(d)frontend/Rules.mk
