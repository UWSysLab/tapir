d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), bufferclient.cc shardclient.cc client.cc)

LIB-store-frontend := $(o)bufferclient.o $(o)shardclient.o $(o)client.o
