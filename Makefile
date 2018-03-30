#
# Top-level makefile for IR and TAPIR
#

CC = gcc
CXX = g++
LD = g++
EXPAND = lib/tmpl/expand

CFLAGS := -g -Wall -pthread -iquote.obj/gen -Wno-uninitialized -O2 -DNASSERT
#CFLAGS := -g -Wall -pthread -iquote.obj/gen -Wno-uninitialized 
CXXFLAGS := -g -std=c++0x
LDFLAGS := -levent_pthreads
## Debian package: check
#CHECK_CFLAGS := $(shell pkg-config --cflags check)
#CHECK_LDFLAGS := $(shell pkg-config --cflags --libs check)
# Debian package: libprotobuf-dev
PROTOBUF_CFLAGS := $(shell pkg-config --cflags protobuf)
PROTOBUF_LDFLAGS := $(shell pkg-config --cflags --libs protobuf)
CFLAGS += $(PROTOBUF_CFLAGS)
LDFLAGS += $(PROTOBUF_LDFLAGS)
PROTOC := protoc
# Debian package: libevent-dev
LIBEVENT_CFLAGS := $(shell pkg-config --cflags libevent)
LIBEVENT_LDFLAGS := $(shell pkg-config --libs libevent)
CFLAGS += $(LIBEVENT_CFLAGS)
LDFLAGS += $(LIBEVENT_LDFLAGS)
# Debian package: libssl-dev
LIBSSL_CFLAGS := $(shell pkg-config --cflags openssl)
LIBSSL_LDFLAGS := $(shell pkg-config --libs openssl)
CFLAGS += $(LIBSSL_CFLAGS)
LDFLAGS += $(LIBSSL_LDFLAGS)


# Google test framework. This doesn't use pkgconfig
GTEST_DIR := /usr/src/gtest

# Additional flags
PARANOID = 1
ifneq ($(PARANOID),0)
override CFLAGS += -DPARANOID=1
$(info WARNING: Paranoid mode enabled)
endif

PERFTOOLS = 0
ifneq ($(PERFTOOLS),0)
override CFLAGS += -DPPROF=1
override LDFLAGS += -lprofiler
endif

# Make sure all is the default
.DEFAULT_GOAL := all

# Eliminate default suffix rules
.SUFFIXES:

# Delete target files if there is an error (or make is interrupted)
.DELETE_ON_ERROR:

# make it so that no intermediate .o files are ever deleted
.PRECIOUS: %.o

##################################################################
# Tracing
#

ifeq ($(V),1)
trace = $(3)
Q =
else
trace = @printf "+ %-6s " $(1) ; echo $(2) ; $(3)
Q = @
endif
GTEST := .obj/gtest/gtest.a
GTEST_MAIN := .obj/gtest/gtest_main.a

##################################################################
# Sub-directories
#

# The directory of the current make fragment.  Each file should
# redefine this at the very top with
#  d := $(dir $(lastword $(MAKEFILE_LIST)))
d :=

# The object directory corresponding to the $(d)
o = .obj/$(d)

# SRCS is the list of all non-test-related source files.
SRCS :=
# TEST_SRCS is just like SRCS, but these source files will be compiled
# with testing related flags.
TEST_SRCS :=
# GTEST_SRCS is tests that use Google's testing framework
GTEST_SRCS :=

# PROTOS is the list of protobuf *.proto files
PROTOS :=

# BINS is a list of target names for non-test binaries.  These targets
# should depend on the appropriate object files, but should not
# contain any commands.
BINS :=
# TEST_BINS is like BINS, but for test binaries.  They will be linked
# using the appropriate flags.  This is also used as the list of tests
# to run for the `test' target.
TEST_BINS :=

# add-CFLAGS is a utility macro that takes a space-separated list of
# sources and a set of CFLAGS.  It sets the CFLAGS for each provided
# source.  This should be used like
#
#  $(call add-CFLAGS,$(d)a.c $(d)b.c,$(PG_CFLAGS))
define add-CFLAGS
$(foreach src,$(1),$(eval CFLAGS-$(src) += $(2)))
endef

# Like add-CFLAGS, but for LDFLAGS.  This should be given a list of
# binaries.
define add-LDFLAGS
$(foreach bin,$(1),$(eval LDFLAGS-$(bin) += $(2)))
endef

include lib/Rules.mk
include replication/common/Rules.mk
include replication/vr/Rules.mk
include replication/ir/Rules.mk
include store/common/Rules.mk
include store/tapirstore/Rules.mk
include store/strongstore/Rules.mk
include store/weakstore/Rules.mk
include store/benchmark/Rules.mk
include lockserver/Rules.mk
include timeserver/Rules.mk
include libtapir/Rules.mk
##################################################################
# General rules
#

#
# Protocols
# 
PROTOOBJS := $(PROTOS:%.proto=.obj/%.o)
PROTOSRCS := $(PROTOS:%.proto=.obj/gen/%.pb.cc)
PROTOHEADERS := $(PROTOS:%.proto=%.pb.h)

$(PROTOSRCS) : .obj/gen/%.pb.cc: %.proto
	@mkdir -p .obj/gen
	$(call trace,PROTOC,$^,$(PROTOC) --cpp_out=.obj/gen $^)

#
# Compilation
#

# -MD Enable dependency generation and compilation and output to the
# .obj directory.  -MP Add phony targets so make doesn't complain if
# a header file is removed.  -MT Explicitly set the target in the
# generated rule to the object file we're generating.
DEPFLAGS = -M -MF ${@:.o=.d} -MP -MT $@ -MG

# $(call add-CFLAGS,$(TEST_SRCS),$(CHECK_CFLAGS))
OBJS := $(SRCS:%.cc=.obj/%.o) $(TEST_SRCS:%.cc=.obj/%.o) $(GTEST_SRCS:%.cc=.obj/%.o)

define compile
	@mkdir -p $(dir $@)
	$(call trace,$(1),$<,\
	  $(CC) -iquote. $(CFLAGS) $(CFLAGS-$<) $(2) $(DEPFLAGS) -E $<)
	$(Q)$(CC) -iquote. $(CFLAGS) $(CFLAGS-$<) $(2) -E -o .obj/$*.t $<
	$(Q)$(EXPAND) $(EXPANDARGS) -o .obj/$*.i .obj/$*.t
	$(Q)$(CC) $(CFLAGS) $(CFLAGS-$<) $(2) -c -o $@ .obj/$*.i
endef

define compilecxx
	@mkdir -p $(dir $@)
	$(call trace,$(1),$<,\
	  $(CXX) -iquote. $(CFLAGS) $(CXXFLAGS) $(CFLAGS-$<) $(2) $(DEPFLAGS) -E $<)
	$(Q)$(CXX) -iquote. $(CFLAGS) $(CXXFLAGS) $(CFLAGS-$<) $(2) -c -o $@ $<
endef

# All object files come in two flavors: regular and
# position-independent.  PIC objects end in -pic.o instead of just .o.
# Link targets that build shared objects must depend on the -pic.o
# versions.
# Slightly different rules for protobuf object files
# because their source files have different locations.

$(OBJS): .obj/%.o: %.cc $(PROTOSRCS)
	$(call compilecxx,CC,)

$(OBJS:%.o=%-pic.o): .obj/%-pic.o: %.cc $(PROTOSRCS)
	$(call compilecxx,CCPIC,-fPIC)

$(PROTOOBJS): .obj/%.o: .obj/gen/%.pb.cc
	$(call compilecxx,CC,)

$(PROTOOBJS:%.o=%-pic.o): .obj/%-pic.o: .obj/gen/%.pb.cc $(PROTOSRCS)
	$(call compilecxx,CCPIC,-fPIC)

#
# Linking
#

$(call add-LDFLAGS,$(TEST_BINS),$(CHECK_LDFLAGS))

$(BINS) $(TEST_BINS): %:
	$(call trace,LD,$@,$(LD) -o $@ $^ $(LDFLAGS) $(LDFLAGS-$@))

#
# Automatic dependencies
#

DEPS := $(OBJS:.o=.d) $(OBJS:.o=-pic.d)

-include $(DEPS)

#
# Testing
#
GTEST_INTERNAL_SRCS := $(wildcard $(GTEST_DIR)/src/*.cc)
GTEST_OBJS := $(patsubst %.cc,.obj/gtest/%.o,$(notdir $(GTEST_INTERNAL_SRCS)))

$(GTEST_OBJS): .obj/gtest/%.o: $(GTEST_DIR)/src/%.cc
	$(call compilecxx,CC,-I$(GTEST_DIR) -Wno-missing-field-initializers)

$(GTEST) : .obj/gtest/gtest-all.o
	$(call trace,AR,$@,$(AR) $(ARFLAGS) $@ $^)

$(GTEST_MAIN) : .obj/gtest/gtest-all.o .obj/gtest/gtest_main.o
	$(call trace,AR,$@,$(AR) $(ARFLAGS) $@ $^)

#
# Cleaning
#

.PHONY: clean
clean:
	$(call trace,RM,binaries,rm -f $(BINS) $(TEST_BINS))
	$(call trace,RM,objects,rm -rf .obj)

#
# Debugging
#
print-%:
	@echo '$*=$($*)'

##################################################################
# Targets
#

.PHONY: all
all: $(BINS)

$(TEST_BINS:%=run-%): run-%: %
	$(call trace,RUN,$<,$<)

$(TEST_BINS:%=gdb-%): gdb-%: %
	$(call trace,GDB,$<,CK_FORK=no gdb $<)

.PHONY: test
test: $(TEST_BINS:%=run-%)
.PHONY: check
check: test

.PHONY: TAGS
TAGS:
	$(Q)rm -f $@
	$(call trace,ETAGS,sources,\
	  etags $(SRCS) $(TEST_SRCS))
	$(call trace,ETAGS,headers,\
	  etags -a $(foreach dir,$(sort $(dir $(SRCS) $(TEST_SRCS))),\
		     $(wildcard $(dir)*.h)))
