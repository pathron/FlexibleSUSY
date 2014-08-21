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

// File generated at Wed 9 Jul 2014 14:04:39

#include "NE6SSM_two_scale_convergence_tester.hpp"
#include <cmath>
#include <algorithm>
#include "wrappers.hpp"

namespace flexiblesusy {

#define OLD1(p) ol->get_##p()
#define NEW1(p) ne->get_##p()

#define OLD(p,i) ol->get_##p()(i)
#define NEW(p,i) ne->get_##p()(i)

NE6SSM_convergence_tester<Two_scale>::NE6SSM_convergence_tester(NE6SSM<Two_scale>* model, double accuracy_goal)
   : Convergence_tester_DRbar<NE6SSM<Two_scale> >(model, accuracy_goal)
{
}

NE6SSM_convergence_tester<Two_scale>::~NE6SSM_convergence_tester()
{
}

double NE6SSM_convergence_tester<Two_scale>::max_rel_diff() const
{
   const NE6SSM<Two_scale>* ol = get_last_iteration_model();
   const NE6SSM<Two_scale>* ne = get_model();

   double diff[81] = { 0 };

   diff[0] = MaxRelDiff(OLD1(MGlu),NEW1(MGlu));
   diff[1] = MaxRelDiff(OLD1(MChaP),NEW1(MChaP));
   diff[2] = MaxRelDiff(OLD1(MVZp),NEW1(MVZp));
   for (unsigned i = 0; i < 6; ++i) {
      diff[i + 3] = MaxRelDiff(OLD(MSd,i),NEW(MSd,i));
   }
   for (unsigned i = 0; i < 3; ++i) {
      diff[i + 9] = MaxRelDiff(OLD(MSv,i),NEW(MSv,i));
   }
   for (unsigned i = 0; i < 6; ++i) {
      diff[i + 12] = MaxRelDiff(OLD(MSu,i),NEW(MSu,i));
   }
   for (unsigned i = 0; i < 6; ++i) {
      diff[i + 18] = MaxRelDiff(OLD(MSe,i),NEW(MSe,i));
   }
   for (unsigned i = 0; i < 6; ++i) {
      diff[i + 24] = MaxRelDiff(OLD(MSDX,i),NEW(MSDX,i));
   }
   for (unsigned i = 0; i < 5; ++i) {
      diff[i + 30] = MaxRelDiff(OLD(Mhh,i),NEW(Mhh,i));
   }
   for (unsigned i = 2; i < 5; ++i) {
      diff[i + 35] = MaxRelDiff(OLD(MAh,i),NEW(MAh,i));
   }
   for (unsigned i = 1; i < 2; ++i) {
      diff[i + 40] = MaxRelDiff(OLD(MHpm,i),NEW(MHpm,i));
   }
   for (unsigned i = 0; i < 8; ++i) {
      diff[i + 42] = MaxRelDiff(OLD(MChi,i),NEW(MChi,i));
   }
   for (unsigned i = 0; i < 2; ++i) {
      diff[i + 50] = MaxRelDiff(OLD(MCha,i),NEW(MCha,i));
   }
   for (unsigned i = 0; i < 3; ++i) {
      diff[i + 52] = MaxRelDiff(OLD(MFDX,i),NEW(MFDX,i));
   }
   for (unsigned i = 0; i < 7; ++i) {
      diff[i + 55] = MaxRelDiff(OLD(MSHI0,i),NEW(MSHI0,i));
   }
   for (unsigned i = 0; i < 4; ++i) {
      diff[i + 62] = MaxRelDiff(OLD(MSHIPM,i),NEW(MSHIPM,i));
   }
   for (unsigned i = 0; i < 2; ++i) {
      diff[i + 66] = MaxRelDiff(OLD(MChaI,i),NEW(MChaI,i));
   }
   for (unsigned i = 0; i < 7; ++i) {
      diff[i + 68] = MaxRelDiff(OLD(MChiI,i),NEW(MChiI,i));
   }
   for (unsigned i = 0; i < 2; ++i) {
      diff[i + 75] = MaxRelDiff(OLD(MSHp0,i),NEW(MSHp0,i));
   }
   for (unsigned i = 0; i < 2; ++i) {
      diff[i + 77] = MaxRelDiff(OLD(MSHpp,i),NEW(MSHpp,i));
   }
   for (unsigned i = 0; i < 2; ++i) {
      diff[i + 79] = MaxRelDiff(OLD(MChiP,i),NEW(MChiP,i));
   }

   return *std::max_element(diff, diff + 81);

}

} // namespace flexiblesusy
