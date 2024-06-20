# set compiler and linker here
CC		:= g++
LD		:= g++

# set main target name here (name of executeable/shared object
TARGET		:= vlog2veriFormal

# set name of test executeable executing ALL tests
TESTTARGET	:= runTests

# dir config
BUILDDIR	:= build
SRCDIR		:= src
DEPDIR		:= .deps
LIBDIR		:= lib
TESTDIR		:= test

# set this to the file ending of your sources
SRCTYPE		:= cpp

# set this to anything other than "" to enable on-demand search of srcs
# (i.e. for code-generating targets) WILL DECREASE PERFORMANCE
ONDEMAND	:=

# tool config
DEBUGFLAGS	:= -g3
INCLUDES	:=
LINKS		:=
CFLAGS		:= $(DEBUGFLAGS) -Wall -Wextra -O2
LDFLAGS		:=
MEMTESTOPTS	:= --tool=memcheck --leak-check=yes

# tool cmds
RM		:= rm -rf
CP		:= cp
VALGRIND	:= valgrind

# ADD TARGETS TO DEFAULT TARGETS
# TARGETS ADDED TO CLEAN WILL BE MARKED AS PHONY
BUILD_TARGETADD	:=
CLEAN_TARGETADD	:=

# PROJECT SPECIFIC CONFIG

################################################################################
###################### END OF CONFIGURATION SECTION ############################
################################################################################

# FUNCTIONS
# Make does not offer a recursive wildcard function, so here's one:
rwildcard=$(wildcard $1$2) $(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2))

################################################################################
##################### START OF USERSPECIFIED TARGETS ###########################
################ set USRDIRS for directory creation rules ######################
################################################################################

################################################################################
####################### END OF USERSPECIFIC TARGETS ############################
################################################################################
######################### START OF SYSTEM TARGETS ##############################
################################################################################

.PHONY: all clean clear dep-clean test test-clean test-leak echo $(CLEAN_TARGETADD) $(TARGET)_BUILD
.DEFAULT_GOAL := all

# generate correct cmd-options
INCLUDES := $(addprefix -I,$(INCLUDES))
LINKS := $(addprefix -l,$(LINKS))

# creates depfiles to be included
DEPFLAGS = -MT $@ -MMD -MP -MF $(DEPDIR)/$*.d
DEPFLAGSSO = -E -M -MT $(@:$(DEPDIR)/%.d=$(BUILDDIR)/%.o) -MG -MP -MF $@

# commands for build/link
BUILD = $(CC) $(DEPFLAGS) $(CFLAGS) $(INCLUDES) -c -o
LINK := $(LD) $(CFLAGS) $(LDFLAGS) $(LINKS) -o

# command needed when autogenerating code for dep-generation
MKDEP = $(CC) $(DEPFLAGSSO) $(INCLUDES)

# testcommands
MEMTEST := $(VALGRIND) $(MEMTESTOPTS)

# cwd
PROJECTROOT := $(dir $(abspath $(MAKEFILE_LIST)))

ifeq (strip $(ONDEMAND),)
	# list of sources
	SRCS := $(call rwildcard,$(SRCDIR),*.$(SRCTYPE))

	# generate list of objects and deps
	OBJS := $(patsubst $(SRCDIR)/%.$(SRCTYPE),$(BUILDDIR)/%.o,$(SRCS))
	DEPS := $(patsubst $(SRCDIR)/%.$(SRCTYPE),$(DEPDIR)/%.d,$(SRCS))

	DEPDIRS := $(sort $(dir $(DEPS)))
	OBJDIRS := $(sort $(dir $(OBJS)))
else
	# list of sources
	SRCS := $(call rwildcard,$(SRCDIR),*.$(SRCTYPE))

	# generate list of objects and deps
	OBJS := $(patsubst $(SRCDIR)/%.$(SRCTYPE),$(BUILDDIR)/%.o,$(SRCS))
	DEPS := $(patsubst $(SRCDIR)/%.$(SRCTYPE),$(DEPDIR)/%.d,$(SRCS))

	DEPDIRS := $(sort $(dir $(DEPS)))
	OBJDIRS := $(sort $(dir $(OBJS)))
endif

# main (and default) build target
all: $(TARGET)_BUILD
	@echo reached target all

clean clear: test-clean dep-clean $(CLEAN_TARGETADD)
	$(RM) $(TARGET) $(BUILDDIR)

echo:
	@echo "SRCS = {" $(SRCS) "}"
	@echo "DEPS = {" $(DEPS) "}"
	@echo "GENDIRS = {" $(GENDIRS) "}"
	@echo
	@echo "DEPDIR = " $(DEPDIR)

dep-clean:
	$(RM) $(DEPDIR)
$(TARGET)_BUILD: $(TARGET) $(BUILD_TARGETADD)
$(TARGET): $(OBJS)
	@echo build $@
	$(LINK) $@ $^

$(OBJS): $(BUILDDIR)/%.o: $(SRCDIR)/%.$(SRCTYPE) | $(OBJDIRS)
$(OBJS): $(BUILDDIR)/%.o: $(SRCDIR)/%.$(SRCTYPE) $(DEPDIR)/%.d | $(DEPDIRS)
	$(BUILD) $@ $<

GENDIRS = $(DEPDIRS) $(USRDIRS) $(OBJDIRS)

$(GENDIRS):
	@mkdir -p $@

# testing
test-clean:
	$(RM) $(TESTTARGET)

test: all $(TESTTARGET)
	@echo running all tests
	@./$(TESTTARGET)

$(TESTTARGET): $(call rwildcard,$(TESTDIR),*.$(SRCTYPE)) $(OBJS)
	$(CC) $(INCLUDES) $(DEBUGFLAGS) $(LINKS) -o $@ $^

test-leak: $(TESTTARGET)
	$(MEMTEST) ./test.testexe 2>&1 | less

#deps
$(DEPS):
include $(DEPS)
