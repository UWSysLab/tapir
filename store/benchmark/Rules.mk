d := $(dir $(lastword $(MAKEFILE_LIST)))

SRCS += $(addprefix $(d), benchClient.cc retwisClient.cc terminalClient.cc)

OBJS-all-clients := $(OBJS-strong-client) $(OBJS-weak-client) $(OBJS-tapir-client)

$(d)benchClient: $(LIB-store-common) $(OBJS-all-clients) $(o)benchClient.o

$(d)retwisClient: $(LIB-store-common) $(OBJS-all-clients) $(o)retwisClient.o

$(d)terminalClient: $(LIB-store-common) $(OBJS-all-clients) $(o)terminalClient.o

BINS += $(d)benchClient $(d)retwisClient $(d)terminalClient
