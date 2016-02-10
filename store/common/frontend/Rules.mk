d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), bufferclient.cc)

LIB-store-frontend := $(o)bufferclient.o
