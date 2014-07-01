DIR          := models/NE6SSM
MODNAME      := NE6SSM
SARAH_MODEL  := NE6SSM

NE6SSM_INSTALL_DIR := $(INSTALL_DIR)/$(DIR)

NE6SSM_MK     := \
		$(DIR)/module.mk

NE6SSM_TWO_SCALE_MK := \
		$(DIR)/two_scale_susy.mk \
		$(DIR)/two_scale_soft.mk

NE6SSM_SLHA_INPUT := \
		$(DIR)/LesHouches.in.NSSM

NE6SSM_GNUPLOT := \
		$(DIR)/NE6SSM_plot_rgflow.gnuplot \
		$(DIR)/NE6SSM_plot_spectrum.gnuplot

LIBNE6SSM_SRC :=
EXENE6SSM_SRC :=

LIBNE6SSM_HDR :=

ifneq ($(findstring two_scale,$(ALGORITHMS)),)
LIBNE6SSM_SRC += \
		$(DIR)/NE6SSM_info.cpp \
		$(DIR)/NE6SSM_slha_io.cpp \
		$(DIR)/NE6SSM_physical.cpp \
		$(DIR)/NE6SSM_utilities.cpp \
		$(DIR)/NE6SSM_two_scale_convergence_tester.cpp \
		$(DIR)/NE6SSM_two_scale_high_scale_constraint.cpp \
		$(DIR)/NE6SSM_two_scale_initial_guesser.cpp \
		$(DIR)/NE6SSM_two_scale_low_scale_constraint.cpp \
		$(DIR)/NE6SSM_two_scale_model.cpp \
		$(DIR)/NE6SSM_two_scale_susy_parameters.cpp \
		$(DIR)/NE6SSM_two_scale_soft_parameters.cpp \
		$(DIR)/NE6SSM_two_scale_susy_scale_constraint.cpp
EXENE6SSM_SRC += \
		$(DIR)/run_NE6SSM.cpp \
		$(DIR)/scan_NE6SSM.cpp
LIBNE6SSM_HDR += \
		$(DIR)/NE6SSM_convergence_tester.hpp \
		$(DIR)/NE6SSM_high_scale_constraint.hpp \
		$(DIR)/NE6SSM_info.hpp \
		$(DIR)/NE6SSM_initial_guesser.hpp \
		$(DIR)/NE6SSM_input_parameters.hpp \
		$(DIR)/NE6SSM_low_scale_constraint.hpp \
		$(DIR)/NE6SSM_model.hpp \
		$(DIR)/NE6SSM_physical.hpp \
		$(DIR)/NE6SSM_slha_io.hpp \
		$(DIR)/NE6SSM_spectrum_generator.hpp \
		$(DIR)/NE6SSM_susy_scale_constraint.hpp \
		$(DIR)/NE6SSM_utilities.hpp \
		$(DIR)/NE6SSM_two_scale_convergence_tester.hpp \
		$(DIR)/NE6SSM_two_scale_high_scale_constraint.hpp \
		$(DIR)/NE6SSM_two_scale_initial_guesser.hpp \
		$(DIR)/NE6SSM_two_scale_low_scale_constraint.hpp \
		$(DIR)/NE6SSM_two_scale_model.hpp \
		$(DIR)/NE6SSM_two_scale_soft_parameters.hpp \
		$(DIR)/NE6SSM_two_scale_susy_parameters.hpp \
		$(DIR)/NE6SSM_two_scale_susy_scale_constraint.hpp

ifneq ($(MAKECMDGOALS),showbuild)
ifneq ($(MAKECMDGOALS),tag)
ifneq ($(MAKECMDGOALS),release)
ifneq ($(MAKECMDGOALS),doc)
-include $(DIR)/two_scale_susy.mk
-include $(DIR)/two_scale_soft.mk
ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),distclean)
ifeq ($(findstring clean-,$(MAKECMDGOALS)),)
ifeq ($(findstring distclean-,$(MAKECMDGOALS)),)
ifeq ($(findstring doc-,$(MAKECMDGOALS)),)
$(DIR)/two_scale_susy.mk: run-metacode-$(MODNAME)
		@true
$(DIR)/two_scale_soft.mk: run-metacode-$(MODNAME)
		@true
endif
endif
endif
endif
endif
endif
endif
endif
endif

endif

# remove duplicates in case all algorithms are used
LIBNE6SSM_SRC := $(sort $(LIBNE6SSM_SRC))
EXENE6SSM_SRC := $(sort $(EXENE6SSM_SRC))

LIBNE6SSM_OBJ := \
		$(patsubst %.cpp, %.o, $(filter %.cpp, $(LIBNE6SSM_SRC))) \
		$(patsubst %.f, %.o, $(filter %.f, $(LIBNE6SSM_SRC)))

EXENE6SSM_OBJ := \
		$(patsubst %.cpp, %.o, $(filter %.cpp, $(EXENE6SSM_SRC))) \
		$(patsubst %.f, %.o, $(filter %.f, $(EXENE6SSM_SRC)))

LIBNE6SSM_DEP := \
		$(LIBNE6SSM_OBJ:.o=.d)

EXENE6SSM_DEP := \
		$(EXENE6SSM_OBJ:.o=.d)

LIBNE6SSM     := $(DIR)/lib$(MODNAME)$(LIBEXT)

RUN_NE6SSM_OBJ := $(DIR)/run_NE6SSM.o
RUN_NE6SSM_EXE := $(DIR)/run_NE6SSM.x

SCAN_NE6SSM_OBJ := $(DIR)/scan_NE6SSM.o
SCAN_NE6SSM_EXE := $(DIR)/scan_NE6SSM.x

METACODE_STAMP_NE6SSM := $(DIR)/00_DELETE_ME_TO_RERUN_METACODE

SARAH_MODEL_FILES_NE6SSM := \
		$(shell $(SARAH_DEP_GEN) $(SARAH_MODEL))

.PHONY:         all-$(MODNAME) clean-$(MODNAME) clean-$(MODNAME)-src \
		distclean-$(MODNAME) run-metacode-$(MODNAME)

all-$(MODNAME): $(LIBNE6SSM)

ifneq ($(INSTALL_DIR),)
install-src::
		install -d $(NE6SSM_INSTALL_DIR)
		install -m u=rw,g=r,o=r $(LIBNE6SSM_SRC) $(NE6SSM_INSTALL_DIR)
		install -m u=rw,g=r,o=r $(LIBNE6SSM_HDR) $(NE6SSM_INSTALL_DIR)
		install -m u=rw,g=r,o=r $(EXENE6SSM_SRC) $(NE6SSM_INSTALL_DIR)
		$(INSTALL_STRIPPED) $(NE6SSM_MK) $(NE6SSM_INSTALL_DIR) -m u=rw,g=r,o=r
		install -m u=rw,g=r,o=r $(NE6SSM_TWO_SCALE_MK) $(NE6SSM_INSTALL_DIR)
ifneq ($(NE6SSM_SLHA_INPUT),)
		install -m u=rw,g=r,o=r $(NE6SSM_SLHA_INPUT) $(NE6SSM_INSTALL_DIR)
endif
		install -m u=rw,g=r,o=r $(NE6SSM_GNUPLOT) $(NE6SSM_INSTALL_DIR)
endif

clean-$(MODNAME)-dep:
		-rm -f $(LIBNE6SSM_DEP)
		-rm -f $(EXENE6SSM_DEP)

clean-$(MODNAME)-obj:
		-rm -f $(LIBNE6SSM_OBJ)
		-rm -f $(EXENE6SSM_OBJ)

# BEGIN: NOT EXPORTED ##########################################
clean-$(MODNAME)-src:
		-rm -f $(LIBNE6SSM_SRC)
		-rm -f $(LIBNE6SSM_HDR)
		-rm -f $(EXENE6SSM_SRC)
		-rm -f $(METACODE_STAMP_NE6SSM)
		-rm -f $(NE6SSM_TWO_SCALE_MK)
		-rm -f $(NE6SSM_GNUPLOT)

clean-$(MODNAME): clean-$(MODNAME)-src
# END:   NOT EXPORTED ##########################################

clean-$(MODNAME): clean-$(MODNAME)-dep clean-$(MODNAME)-obj
		-rm -f $(LIBNE6SSM)
		-rm -f $(RUN_NE6SSM_EXE)
		-rm -f $(SCAN_NE6SSM_EXE)

distclean-$(MODNAME): clean-$(MODNAME)

clean::         clean-$(MODNAME)

distclean::     distclean-$(MODNAME)

$(LIBNE6SSM_SRC) $(LIBNE6SSM_HDR) $(EXENE6SSM_SRC) \
: run-metacode-$(MODNAME)
		@true

run-metacode-$(MODNAME): $(METACODE_STAMP_NE6SSM)
		@true

ifeq ($(ENABLE_META),yes)
$(METACODE_STAMP_NE6SSM): $(DIR)/start.m $(DIR)/FlexibleSUSY.m $(META_SRC) $(TEMPLATES) $(SARAH_MODEL_FILES_NE6SSM)
		$(MATH) -run "Get[\"$<\"]; Quit[]"
		@touch "$(METACODE_STAMP_NE6SSM)"
		@echo "Note: to regenerate NE6SSM source files," \
		      "please remove the file "
		@echo "\"$(METACODE_STAMP_NE6SSM)\" and run make"
		@echo "---------------------------------"
else
$(METACODE_STAMP_NE6SSM):
		@true
endif

$(LIBNE6SSM_DEP) $(EXENE6SSM_DEP) $(LIBNE6SSM_OBJ) $(EXENE6SSM_OBJ): CPPFLAGS += $(GSLFLAGS) $(EIGENFLAGS) $(BOOSTFLAGS)

ifneq (,$(findstring yes,$(ENABLE_LOOPTOOLS)$(ENABLE_FFLITE)))
$(LIBNE6SSM_DEP) $(EXENE6SSM_DEP) $(LIBNE6SSM_OBJ) $(EXENE6SSM_OBJ): CPPFLAGS += $(LOOPFUNCFLAGS)
endif

$(LIBNE6SSM): $(LIBNE6SSM_OBJ)
		$(MAKELIB) $@ $^

$(RUN_NE6SSM_EXE): $(RUN_NE6SSM_OBJ) $(LIBNE6SSM) $(LIBFLEXI) $(LIBLEGACY) $(filter-out -%,$(LOOPFUNCLIBS))
		$(CXX) -o $@ $(call abspathx,$^) $(filter -%,$(LOOPFUNCLIBS)) $(GSLLIBS) $(BOOSTTHREADLIBS) $(THREADLIBS) $(LAPACKLIBS) $(FLIBS)

$(SCAN_NE6SSM_EXE): $(SCAN_NE6SSM_OBJ) $(LIBNE6SSM) $(LIBFLEXI) $(LIBLEGACY) $(filter-out -%,$(LOOPFUNCLIBS))
		$(CXX) -o $@ $(call abspathx,$^) $(filter -%,$(LOOPFUNCLIBS)) $(GSLLIBS) $(BOOSTTHREADLIBS) $(THREADLIBS) $(LAPACKLIBS) $(FLIBS)

ALLDEP += $(LIBNE6SSM_DEP) $(EXENE6SSM_DEP)
ALLSRC += $(LIBNE6SSM_SRC) $(EXENE6SSM_SRC)
ALLLIB += $(LIBNE6SSM)
ALLEXE += $(RUN_NE6SSM_EXE) $(SCAN_NE6SSM_EXE)
