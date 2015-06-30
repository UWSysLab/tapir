d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), \
	txnstore.cc occstore.cc lockstore.cc)

LIB-txnstore := $(o)txnstore.o $(o)occstore.o $(o)lockstore.o