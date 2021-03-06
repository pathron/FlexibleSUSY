DIR          := models/fmssmn
MODNAME      := fmssmn

LIBFMSSMN_SRC  :=
LIBFMSSMN_GENERATED_SRC :=
LIBFMSSMN_INC  :=

ifneq ($(findstring lattice,$(ALGORITHMS)),)
LIBFMSSMN_GENERATED_SRC += \
		$(DIR)/fmssmn_lattice_rge.f \
		$(DIR)/fmssmn_lattice_constraints.f \
		$(DIR)/fmssmn_lattice_numerical_constraints_functions.f \
		$(DIR)/fmssmn_lattice_numerical_constraints_dependence.cpp \
		$(DIR)/fmssm_fmssmn_lattice_matchings.f \
		$(DIR)/fmssm_fmssmn_lattice_numerical_matchings_functions.f \
		$(DIR)/fmssm_fmssmn_lattice_numerical_matchings_dependence.cpp

LIBFMSSMN_INC  += \
		$(DIR)/fmssmn_lattice_translator.inc

LIBFMSSMN_SRC  += \
		$(DIR)/fmssmn_lattice.cpp \
		$(DIR)/fmssmn_lattice_mz_constraint.cpp \
		$(DIR)/fmssmn_lattice_msusy_constraint.cpp \
		$(DIR)/fmssmn_lattice_mx_constraint.cpp \
		$(DIR)/fmssmn_lattice_numerical_constraints.cpp \
		$(DIR)/fmssm_fmssmn_lattice_numerical_matchings.cpp \
		$(LIBFMSSMN_GENERATED_SRC)
endif

LIBFMSSMN_OBJ  := \
		$(patsubst %.cpp, %.o, $(filter %.cpp, $(LIBFMSSMN_SRC))) \
		$(patsubst %.f, %.o, $(filter %.f, $(LIBFMSSMN_SRC)))

LIBFMSSMN_DEP  := \
		$(LIBFMSSMN_OBJ:.o=.d)

LIBFMSSMN      := $(DIR)/lib$(MODNAME)$(LIBEXT)

.PHONY:         all-$(MODNAME) clean-$(MODNAME) distclean-$(MODNAME)

all-$(MODNAME): $(LIBFMSSMN)

clean-$(MODNAME)-dep:
		-rm -f $(LIBFMSSMN_DEP)

clean-$(MODNAME)-obj:
		-rm -f $(LIBFMSSMN_OBJ)

clean-$(MODNAME): clean-$(MODNAME)-dep clean-$(MODNAME)-obj
		-rm -f $(LIBFMSSMN)

distclean-$(MODNAME): clean-$(MODNAME)
		-rm -f $(LIBFMSSMN_GENERATED_SRC)
		-rm -f $(LIBFMSSMN_INC)

clean::         clean-$(MODNAME)

distclean::     distclean-$(MODNAME)

$(DIR)/%.cpp : $(DIR)/%.cpp.m
	$(MATH) -run 'filename="$@"; << $<; Quit[]'

$(DIR)/%.f : $(DIR)/%.f.m
	$(MATH) -run 'filename="$@"; << $<; Quit[]'

$(DIR)/%.inc : $(DIR)/%.inc.m
	$(MATH) -run 'filename="$@"; << $<; Quit[]'

ifneq ($(findstring lattice,$(ALGORITHMS)),)
$(LIBFMSSMN_DEP) $(LIBFMSSMN_OBJ): CPPFLAGS += $(EIGENFLAGS) $(GSLFLAGS) $(BOOSTFLAGS)
endif

$(LIBFMSSMN): $(LIBFMSSMN_OBJ)
		$(MAKELIB) $@ $^

ALLDEP += $(LIBFMSSMN_DEP)
ALLLIB += $(LIBFMSSMN)
