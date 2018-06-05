d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), \
	lookup3.cc message.cc memory.cc \
	latency.cc configuration.cc transport.cc \
	udptransport.cc tcptransport.cc simtransport.cc \
        repltransport.cc zeustransport.cc \
	persistent_register.cc)

TARGETOS := $(shell uname -s)

ifneq ($(TARGETOS), Darwin)
	SRCS += $(addprefix $(d), rdmatransport.cc)
endif

PROTOS += $(addprefix $(d), \
          latency-format.proto)

LIB-hash := $(o)lookup3.o

LIB-message := $(o)message.o $(LIB-hash)

LIB-hashtable := $(LIB-hash) $(LIB-message)

LIB-memory := $(o)memory.o

LIB-latency := $(o)latency.o $(o)latency-format.o $(LIB-message)

LIB-configuration := $(o)configuration.o $(LIB-message)

LIB-transport := $(o)transport.o $(LIB-message) $(LIB-configuration)

LIB-transport-all := $(o)udptransport.o $(o)tcptransport.o $(o)zeustransport.o $(LIB-transport)

ifneq ($(TARGETOS), Darwin)
LIB-transport-all := $(o)udptransport.o $(o)tcptransport.o LIB-transport-all := $(o)udptransport.o $(o)tcptransport.o $(o)zeustransport.o $(LIB-transport)$(o)zeustransport.o $(LIB-transport)
endif

LIB-simtransport := $(o)simtransport.o $(LIB-transport)

LIB-repltransport := $(o)repltransport.o $(LIB-transport)

LIB-udptransport := $(o)udptransport.o $(LIB-transport)

LIB-tcptransport := $(o)tcptransport.o $(LIB-transport)

LIB-zeustransport := $(o)zeustransport.o $(LIB-transport)

LIB-persistent_register := $(o)persistent_register.o $(LIB-message)

ifneq ($(TARGETOS), Darwin)
	LIB-rdmatransport := $(o)rdmatransport.o $(LIB-transport)
endif

include $(d)tests/Rules.mk

