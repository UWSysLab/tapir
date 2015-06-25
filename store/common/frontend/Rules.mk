d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), \
	bufferclient.cc client.cc shardclient.cc)

LIB-frontend := $(o)bufferclient.o $(o)txnclient.o $(o)client.o
