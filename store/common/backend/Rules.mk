d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), \
	kvstore.cc lockserver.cc versionstore.cc)

LIB-backend := $(o)kvstore.o $(o)versionstore.o $(o)lockserver.o

include $(d)tests/Rules.mk