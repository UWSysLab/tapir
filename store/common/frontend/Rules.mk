d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), bufferclient.cc txnclient.cc client.cc)

LIB-store-frontend := $(o)bufferclient.o $(o)txnclient.o $(o)client.o
