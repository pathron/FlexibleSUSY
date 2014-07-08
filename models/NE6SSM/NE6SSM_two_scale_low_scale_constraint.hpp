// ====================================================================
// This file is part of FlexibleSUSY.
//
// FlexibleSUSY is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License,
// or (at your option) any later version.
//
// FlexibleSUSY is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with FlexibleSUSY.  If not, see
// <http://www.gnu.org/licenses/>.
// ====================================================================

// File generated at Tue 8 Jul 2014 14:47:12

#ifndef NE6SSM_TWO_SCALE_LOW_SCALE_CONSTRAINT_H
#define NE6SSM_TWO_SCALE_LOW_SCALE_CONSTRAINT_H

#include "NE6SSM_low_scale_constraint.hpp"
#include "NE6SSM_input_parameters.hpp"
#include "two_scale_constraint.hpp"
#include "lowe.h"
#include <Eigen/Core>

namespace flexiblesusy {

template <class T>
class NE6SSM;

class Two_scale;

template<>
class NE6SSM_low_scale_constraint<Two_scale> : public Constraint<Two_scale> {
public:
   NE6SSM_low_scale_constraint();
   NE6SSM_low_scale_constraint(const NE6SSM_input_parameters&, const QedQcd&);
   virtual ~NE6SSM_low_scale_constraint();
   virtual void apply();
   virtual double get_scale() const;
   virtual void set_model(Two_scale_model*);

   void clear();
   double get_initial_scale_guess() const;
   void initialize();
   void set_input_parameters(const NE6SSM_input_parameters&);
   void set_sm_parameters(const QedQcd&);
   void set_threshold_corrections(unsigned); ///< diable/enable threshold corrections

private:
   double scale;
   double initial_scale_guess;
   NE6SSM<Two_scale>* model;
   NE6SSM_input_parameters inputPars;
   QedQcd oneset;
   double MZDRbar;
   double new_g1, new_g2, new_g3;
   unsigned threshold_corrections; ///< diable/enable threshold corrections

   void calculate_DRbar_gauge_couplings();
   void calculate_DRbar_yukawa_couplings();
   void calculate_Yu_DRbar();
   void calculate_Yd_DRbar();
   void calculate_Ye_DRbar();
   double calculate_delta_alpha_em(double) const;
   double calculate_delta_alpha_s(double) const;
   void update_scale();
};

} // namespace flexiblesusy

#endif
