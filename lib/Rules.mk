d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), \
	lookup3.cc message.cc memory.cc \
	latency.cc configuration.cc transport.cc \
	udptransport.cc tcptransport.cc simtransport.cc repltransport.cc \
	persistent_register.cc)

PROTOS += $(addprefix $(d), \
          latency-format.proto)

LIB-hash := $(o)lookup3.o

LIB-message := $(o)message.o $(LIB-hash)

LIB-hashtable := $(LIB-hash) $(LIB-message)

LIB-memory := $(o)memory.o

LIB-latency := $(o)latency.o $(o)latency-format.o $(LIB-message)

LIB-configuration := $(o)configuration.o $(LIB-message)

LIB-transport := $(o)transport.o $(LIB-message) $(LIB-configuration)

LIB-simtransport := $(o)simtransport.o $(LIB-transport)

LIB-repltransport := $(o)repltransport.o $(LIB-transport)

LIB-udptransport := $(o)udptransport.o $(LIB-transport)

LIB-tcptransport := $(o)tcptransport.o $(LIB-transport)

LIB-persistent_register := $(o)persistent_register.o $(LIB-message)

include $(d)tests/Rules.mk

