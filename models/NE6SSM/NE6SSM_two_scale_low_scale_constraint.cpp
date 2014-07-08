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

#include "NE6SSM_two_scale_low_scale_constraint.hpp"
#include "NE6SSM_two_scale_model.hpp"
#include "wrappers.hpp"
#include "logger.hpp"
#include "ew_input.hpp"
#include "gsl_utils.hpp"
#include "minimizer.hpp"
#include "root_finder.hpp"

#include <cassert>
#include <cmath>
#include <limits>

namespace flexiblesusy {

#define INPUTPARAMETER(p) inputPars.p
#define MODELPARAMETER(p) model->get_##p()
#define BETAPARAMETER(p) beta_functions.get_##p()
#define BETA(p) beta_##p
#define SM(p) Electroweak_constants::p
#define STANDARDDEVIATION(p) Electroweak_constants::Error_##p
#define Pole(p) model->get_physical().p
#define MODEL model
#define MODELCLASSNAME NE6SSM<Two_scale>

NE6SSM_low_scale_constraint<Two_scale>::NE6SSM_low_scale_constraint()
   : Constraint<Two_scale>()
   , scale(0.)
   , initial_scale_guess(0.)
   , model(0)
   , inputPars()
   , oneset()
   , MZDRbar(0.)
   , new_g1(0.)
   , new_g2(0.)
   , new_g3(0.)
   , threshold_corrections(1)
{
}

NE6SSM_low_scale_constraint<Two_scale>::NE6SSM_low_scale_constraint(const NE6SSM_input_parameters& inputPars_, const QedQcd& oneset_)
   : Constraint<Two_scale>()
   , model(0)
   , inputPars(inputPars_)
   , oneset(oneset_)
   , new_g1(0.)
   , new_g2(0.)
   , new_g3(0.)
{
   initialize();
}

NE6SSM_low_scale_constraint<Two_scale>::~NE6SSM_low_scale_constraint()
{
}

void NE6SSM_low_scale_constraint<Two_scale>::apply()
{
   assert(model && "Error: NE6SSM_low_scale_constraint:"
          " model pointer must not be zero");

   model->calculate_DRbar_parameters();
   update_scale();
   calculate_DRbar_gauge_couplings();

   const auto TanBeta = INPUTPARAMETER(TanBeta);
   const auto g1 = MODELPARAMETER(g1);
   const auto g2 = MODELPARAMETER(g2);

   calculate_Yu_DRbar();
   calculate_Yd_DRbar();
   calculate_Ye_DRbar();
   MODEL->set_vd((2*MZDRbar)/(Sqrt(0.6*Sqr(g1) + Sqr(g2))*Sqrt(1 + Sqr(TanBeta)
      )));
   MODEL->set_vu((2*MZDRbar*TanBeta)/(Sqrt(0.6*Sqr(g1) + Sqr(g2))*Sqrt(1 + Sqr(
      TanBeta))));


   model->set_g1(new_g1);
   model->set_g2(new_g2);
   model->set_g3(new_g3);
}

double NE6SSM_low_scale_constraint<Two_scale>::get_scale() const
{
   return scale;
}

double NE6SSM_low_scale_constraint<Two_scale>::get_initial_scale_guess() const
{
   return initial_scale_guess;
}

void NE6SSM_low_scale_constraint<Two_scale>::set_model(Two_scale_model* model_)
{
   model = cast_model<NE6SSM<Two_scale> >(model_);
}

void NE6SSM_low_scale_constraint<Two_scale>::set_input_parameters(const NE6SSM_input_parameters& inputPars_)
{
   inputPars = inputPars_;
}

void NE6SSM_low_scale_constraint<Two_scale>::set_sm_parameters(const QedQcd& oneset_)
{
   oneset = oneset_;
}

void NE6SSM_low_scale_constraint<Two_scale>::clear()
{
   scale = 0.;
   initial_scale_guess = 0.;
   model = NULL;
   oneset = QedQcd();
   MZDRbar = 0.;
   new_g1 = 0.;
   new_g2 = 0.;
   new_g3 = 0.;
}

void NE6SSM_low_scale_constraint<Two_scale>::initialize()
{
   initial_scale_guess = SM(MZ);

   scale = initial_scale_guess;

   MZDRbar = 0.;
   new_g1 = 0.;
   new_g2 = 0.;
   new_g3 = 0.;
}

void NE6SSM_low_scale_constraint<Two_scale>::update_scale()
{
   scale = SM(MZ);


}

void NE6SSM_low_scale_constraint<Two_scale>::calculate_DRbar_gauge_couplings()
{
   assert(oneset.displayMu() == get_scale() && "Error: low-energy data"
          " set is not defined at the same scale as the low-energy"
          " constraint.  You need to run the low-energy data set to this"
          " scale!");

   const double alpha_em = oneset.displayAlpha(ALPHA);
   const double alpha_s  = oneset.displayAlpha(ALPHAS);

   double delta_alpha_em = 0.;
   double delta_alpha_s  = 0.;

   if (model->get_thresholds()) {
      delta_alpha_em = calculate_delta_alpha_em(alpha_em);
      delta_alpha_s  = calculate_delta_alpha_s(alpha_s);
   }

   const double alpha_em_drbar = alpha_em / (1.0 - delta_alpha_em);
   const double alpha_s_drbar  = alpha_s  / (1.0 - delta_alpha_s);
   const double e_drbar        = Sqrt(4.0 * Pi * alpha_em_drbar);

   // interface variables
   MZDRbar
      = model->calculate_MVZ_DRbar(Electroweak_constants::MZ);
   const double MWDRbar
      = model->calculate_MVWm_DRbar(Electroweak_constants::MW);
   const double AlphaS = alpha_s_drbar;
   const double EDRbar = e_drbar;

   const double ThetaW = ArcSin(Sqrt(1 - Sqr(MWDRbar)/Sqr(MZDRbar)));
   new_g1 = 1.2909944487358056*EDRbar*Sec(ThetaW);
   new_g2 = EDRbar*Csc(ThetaW);
   new_g3 = 3.5449077018110318*Sqrt(AlphaS);

}

double NE6SSM_low_scale_constraint<Two_scale>::calculate_delta_alpha_em(double alphaEm) const
{
   const double currentScale = model->get_scale();
   const auto MCha = MODELPARAMETER(MCha);
   const auto MChaI = MODELPARAMETER(MChaI);
   const auto MFDX = MODELPARAMETER(MFDX);
   const auto MFu = MODELPARAMETER(MFu);
   const auto MHpm = MODELPARAMETER(MHpm);
   const auto MSd = MODELPARAMETER(MSd);
   const auto MSDX = MODELPARAMETER(MSDX);
   const auto MSe = MODELPARAMETER(MSe);
   const auto MSHIPM = MODELPARAMETER(MSHIPM);
   const auto MSHpp = MODELPARAMETER(MSHpp);
   const auto MSu = MODELPARAMETER(MSu);
   const auto MChaP = MODELPARAMETER(MChaP);

   const double delta_alpha_em_SM = 0.15915494309189535*alphaEm*(
      0.3333333333333333 - 1.7777777777777777*FiniteLog(Abs(MFu(2)/currentScale)))
      ;

   const double delta_alpha_em = 0.15915494309189535*alphaEm*(
      -1.3333333333333333*FiniteLog(Abs(MChaP/currentScale)) - 1.3333333333333333*
      FiniteLog(Abs(MCha(0)/currentScale)) - 1.3333333333333333*FiniteLog(Abs(MCha
      (1)/currentScale)) - 1.3333333333333333*FiniteLog(Abs(MChaI(0)/currentScale)
      ) - 1.3333333333333333*FiniteLog(Abs(MChaI(1)/currentScale)) -
      0.14814814814814814*FiniteLog(Abs(MFDX(0)/currentScale)) -
      0.14814814814814814*FiniteLog(Abs(MFDX(1)/currentScale)) -
      0.14814814814814814*FiniteLog(Abs(MFDX(2)/currentScale)) -
      0.3333333333333333*FiniteLog(Abs(MHpm(1)/currentScale)) - 0.1111111111111111
      *FiniteLog(Abs(MSd(0)/currentScale)) - 0.1111111111111111*FiniteLog(Abs(MSd(
      1)/currentScale)) - 0.1111111111111111*FiniteLog(Abs(MSd(2)/currentScale)) -
      0.1111111111111111*FiniteLog(Abs(MSd(3)/currentScale)) - 0.1111111111111111
      *FiniteLog(Abs(MSd(4)/currentScale)) - 0.1111111111111111*FiniteLog(Abs(MSd(
      5)/currentScale)) - 0.037037037037037035*FiniteLog(Abs(MSDX(0)/currentScale)
      ) - 0.037037037037037035*FiniteLog(Abs(MSDX(1)/currentScale)) -
      0.037037037037037035*FiniteLog(Abs(MSDX(2)/currentScale)) -
      0.037037037037037035*FiniteLog(Abs(MSDX(3)/currentScale)) -
      0.037037037037037035*FiniteLog(Abs(MSDX(4)/currentScale)) -
      0.037037037037037035*FiniteLog(Abs(MSDX(5)/currentScale)) -
      0.3333333333333333*FiniteLog(Abs(MSe(0)/currentScale)) - 0.3333333333333333*
      FiniteLog(Abs(MSe(1)/currentScale)) - 0.3333333333333333*FiniteLog(Abs(MSe(2
      )/currentScale)) - 0.3333333333333333*FiniteLog(Abs(MSe(3)/currentScale)) -
      0.3333333333333333*FiniteLog(Abs(MSe(4)/currentScale)) - 0.3333333333333333*
      FiniteLog(Abs(MSe(5)/currentScale)) - 0.3333333333333333*FiniteLog(Abs(
      MSHIPM(0)/currentScale)) - 0.3333333333333333*FiniteLog(Abs(MSHIPM(1)
      /currentScale)) - 0.3333333333333333*FiniteLog(Abs(MSHIPM(2)/currentScale))
      - 0.3333333333333333*FiniteLog(Abs(MSHIPM(3)/currentScale)) -
      0.3333333333333333*FiniteLog(Abs(MSHpp(0)/currentScale)) -
      0.3333333333333333*FiniteLog(Abs(MSHpp(1)/currentScale)) -
      0.4444444444444444*FiniteLog(Abs(MSu(0)/currentScale)) - 0.4444444444444444*
      FiniteLog(Abs(MSu(1)/currentScale)) - 0.4444444444444444*FiniteLog(Abs(MSu(2
      )/currentScale)) - 0.4444444444444444*FiniteLog(Abs(MSu(3)/currentScale)) -
      0.4444444444444444*FiniteLog(Abs(MSu(4)/currentScale)) - 0.4444444444444444*
      FiniteLog(Abs(MSu(5)/currentScale)));

   return delta_alpha_em + delta_alpha_em_SM;

}

double NE6SSM_low_scale_constraint<Two_scale>::calculate_delta_alpha_s(double alphaS) const
{
   const double currentScale = model->get_scale();
   const auto MFDX = MODELPARAMETER(MFDX);
   const auto MFu = MODELPARAMETER(MFu);
   const auto MSd = MODELPARAMETER(MSd);
   const auto MSDX = MODELPARAMETER(MSDX);
   const auto MSu = MODELPARAMETER(MSu);
   const auto MGlu = MODELPARAMETER(MGlu);

   const double delta_alpha_s_SM = -0.1061032953945969*alphaS*FiniteLog(Abs(MFu
      (2)/currentScale));

   const double delta_alpha_s = 0.15915494309189535*alphaS*(0.5 - 2*FiniteLog(
      Abs(MGlu/currentScale)) - 0.6666666666666666*FiniteLog(Abs(MFDX(0)
      /currentScale)) - 0.6666666666666666*FiniteLog(Abs(MFDX(1)/currentScale)) -
      0.6666666666666666*FiniteLog(Abs(MFDX(2)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSd(0)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSd(1)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSd(2)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSd(3)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSd(4)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSd(5)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSDX(0)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSDX(1)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSDX(2)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSDX(3)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSDX(4)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSDX(5)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSu(0)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSu(1)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSu(2)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSu(3)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSu(4)/currentScale)) -
      0.16666666666666666*FiniteLog(Abs(MSu(5)/currentScale)));

   return delta_alpha_s + delta_alpha_s_SM;

}

void NE6SSM_low_scale_constraint<Two_scale>::calculate_DRbar_yukawa_couplings()
{
   calculate_Yu_DRbar();
   calculate_Yd_DRbar();
   calculate_Ye_DRbar();
}

void NE6SSM_low_scale_constraint<Two_scale>::calculate_Yu_DRbar()
{
   Eigen::Matrix<double,3,3> topDRbar(Eigen::Matrix<double,3,3>::Zero());
   topDRbar(0,0)      = oneset.displayMass(mUp);
   topDRbar(1,1)      = oneset.displayMass(mCharm);
   topDRbar(2,2)      = oneset.displayMass(mTop);

   if (model->get_thresholds())
      topDRbar(2,2) = model->calculate_MFu_DRbar(oneset.displayPoleMt(), 2);

   const auto vu = MODELPARAMETER(vu);
   MODEL->set_Yu(Diag((1.4142135623730951*topDRbar)/vu));

}

void NE6SSM_low_scale_constraint<Two_scale>::calculate_Yd_DRbar()
{
   Eigen::Matrix<double,3,3> bottomDRbar(Eigen::Matrix<double,3,3>::Zero());
   bottomDRbar(0,0)   = oneset.displayMass(mDown);
   bottomDRbar(1,1)   = oneset.displayMass(mStrange);
   bottomDRbar(2,2)   = oneset.displayMass(mBottom);

   if (model->get_thresholds())
      bottomDRbar(2,2) = model->calculate_MFd_DRbar(oneset.displayMass(mBottom), 2);

   const auto vd = MODELPARAMETER(vd);
   MODEL->set_Yd(Diag((1.4142135623730951*bottomDRbar)/vd));

}

void NE6SSM_low_scale_constraint<Two_scale>::calculate_Ye_DRbar()
{
   Eigen::Matrix<double,3,3> electronDRbar(Eigen::Matrix<double,3,3>::Zero());
   electronDRbar(0,0) = oneset.displayMass(mElectron);
   electronDRbar(1,1) = oneset.displayMass(mMuon);
   electronDRbar(2,2) = oneset.displayMass(mTau);

   if (model->get_thresholds())
      electronDRbar(2,2) = model->calculate_MFe_DRbar(oneset.displayMass(mTau), 2);

   const auto vd = MODELPARAMETER(vd);
   MODEL->set_Ye(Diag((1.4142135623730951*electronDRbar)/vd));

}

} // namespace flexiblesusy
