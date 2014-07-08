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

// File generated at Tue 8 Jul 2014 14:40:53

#include "NE6SSM_two_scale_susy_parameters.hpp"
#include "wrappers.hpp"

namespace flexiblesusy {

#define INPUT(parameter) input.parameter
#define TRACE_STRUCT susy_traces

/**
 * Calculates the one-loop beta function of g1.
 *
 * @return one-loop beta function
 */
double NE6SSM_susy_parameters::calc_beta_g1_one_loop(const Susy_traces& susy_traces) const
{


   double beta_g1;

   beta_g1 = 9.6*Power(g1,3)*oneOver16PiSqr;


   return beta_g1;
}

/**
 * Calculates the two-loop beta function of g1.
 *
 * @return two-loop beta function
 */
double NE6SSM_susy_parameters::calc_beta_g1_two_loop(const Susy_traces& susy_traces) const
{
   const double tracefdAdjfd = TRACE_STRUCT.tracefdAdjfd;
   const double tracefuAdjfu = TRACE_STRUCT.tracefuAdjfu;
   const double tracegDAdjgD = TRACE_STRUCT.tracegDAdjgD;
   const double tracehEAdjhE = TRACE_STRUCT.tracehEAdjhE;
   const double traceYdAdjYd = TRACE_STRUCT.traceYdAdjYd;
   const double traceYeAdjYe = TRACE_STRUCT.traceYeAdjYe;
   const double traceYuAdjYu = TRACE_STRUCT.traceYuAdjYu;
   const double traceKappaAdjKappa = TRACE_STRUCT.traceKappaAdjKappa;
   const double traceLambda12AdjLambda12 =
      TRACE_STRUCT.traceLambda12AdjLambda12;


   double beta_g1;

   beta_g1 = 0.04*Power(g1,3)*twoLoop*(-30*tracefdAdjfd - 30*tracefuAdjfu
      - 70*tracegDAdjgD - 90*tracehEAdjhE - 20*traceKappaAdjKappa - 30*
      traceLambda12AdjLambda12 - 70*traceYdAdjYd - 90*traceYeAdjYe - 130*
      traceYuAdjYu - 30*AbsSqr(Lambdax) - 30*AbsSqr(SigmaL) + 234*Sqr(g1) + 81*
      Sqr(g1p) + 270*Sqr(g2) + 600*Sqr(g3));


   return beta_g1;
}

} // namespace flexiblesusy
