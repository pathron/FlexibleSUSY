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

// File generated at Wed 9 Jul 2014 14:04:41

#include "NE6SSM_two_scale_susy_scale_constraint.hpp"
#include "NE6SSM_two_scale_model.hpp"
#include "wrappers.hpp"
#include "logger.hpp"
#include "ew_input.hpp"
#include "gsl_utils.hpp"
#include "minimizer.hpp"
#include "root_finder.hpp"

#include <cassert>
#include <cmath>

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

NE6SSM_susy_scale_constraint<Two_scale>::NE6SSM_susy_scale_constraint()
   : Constraint<Two_scale>()
   , scale(0.)
   , initial_scale_guess(0.)
   , model(0)
   , inputPars()
{
}

NE6SSM_susy_scale_constraint<Two_scale>::NE6SSM_susy_scale_constraint(const NE6SSM_input_parameters& inputPars_)
   : Constraint<Two_scale>()
   , model(0)
   , inputPars(inputPars_)
{
   initialize();
}

NE6SSM_susy_scale_constraint<Two_scale>::~NE6SSM_susy_scale_constraint()
{
}

void NE6SSM_susy_scale_constraint<Two_scale>::apply()
{
   assert(model && "Error: NE6SSM_susy_scale_constraint:"
          " model pointer must not be zero");

   model->calculate_DRbar_parameters();
   update_scale();

   // apply user-defined susy scale constraints
   const auto BmuPrimeInput = INPUTPARAMETER(BmuPrimeInput);
   const auto muPrimeInput = INPUTPARAMETER(muPrimeInput);
   const auto vSInput = INPUTPARAMETER(vSInput);
   const auto hEInput = INPUTPARAMETER(hEInput);
   const auto SigmaLInput = INPUTPARAMETER(SigmaLInput);
   const auto KappaPrInput = INPUTPARAMETER(KappaPrInput);
   const auto SigmaxInput = INPUTPARAMETER(SigmaxInput);
   const auto gDInput = INPUTPARAMETER(gDInput);
   const auto KappaInput = INPUTPARAMETER(KappaInput);
   const auto Lambda12Input = INPUTPARAMETER(Lambda12Input);
   const auto LambdaxInput = INPUTPARAMETER(LambdaxInput);
   const auto fuInput = INPUTPARAMETER(fuInput);
   const auto fdInput = INPUTPARAMETER(fdInput);
   const auto MuPhiInput = INPUTPARAMETER(MuPhiInput);
   const auto XiFInput = INPUTPARAMETER(XiFInput);
   const auto g1pInput = INPUTPARAMETER(g1pInput);
   const auto vsbInput = INPUTPARAMETER(vsbInput);
   const auto vphiInput = INPUTPARAMETER(vphiInput);
   const auto TYdInput = INPUTPARAMETER(TYdInput);
   const auto ThEInput = INPUTPARAMETER(ThEInput);
   const auto TYeInput = INPUTPARAMETER(TYeInput);
   const auto TSigmaLInput = INPUTPARAMETER(TSigmaLInput);
   const auto TKappaPrInput = INPUTPARAMETER(TKappaPrInput);
   const auto TSigmaxInput = INPUTPARAMETER(TSigmaxInput);
   const auto TgDInput = INPUTPARAMETER(TgDInput);
   const auto TKappaInput = INPUTPARAMETER(TKappaInput);
   const auto TLambda12Input = INPUTPARAMETER(TLambda12Input);
   const auto TLambdaxInput = INPUTPARAMETER(TLambdaxInput);
   const auto TfuInput = INPUTPARAMETER(TfuInput);
   const auto TfdInput = INPUTPARAMETER(TfdInput);
   const auto TYuInput = INPUTPARAMETER(TYuInput);
   const auto BMuPhiInput = INPUTPARAMETER(BMuPhiInput);
   const auto LXiFInput = INPUTPARAMETER(LXiFInput);
   const auto mq2Input = INPUTPARAMETER(mq2Input);
   const auto ml2Input = INPUTPARAMETER(ml2Input);
   const auto md2Input = INPUTPARAMETER(md2Input);
   const auto mu2Input = INPUTPARAMETER(mu2Input);
   const auto me2Input = INPUTPARAMETER(me2Input);
   const auto mH1I2Input = INPUTPARAMETER(mH1I2Input);
   const auto mH2I2Input = INPUTPARAMETER(mH2I2Input);
   const auto mSI2Input = INPUTPARAMETER(mSI2Input);
   const auto mDx2Input = INPUTPARAMETER(mDx2Input);
   const auto mDxbar2Input = INPUTPARAMETER(mDxbar2Input);
   const auto mHp2Input = INPUTPARAMETER(mHp2Input);
   const auto mHpbar2Input = INPUTPARAMETER(mHpbar2Input);
   const auto MassBInput = INPUTPARAMETER(MassBInput);
   const auto MassWBInput = INPUTPARAMETER(MassWBInput);
   const auto MassGInput = INPUTPARAMETER(MassGInput);
   const auto MassBpInput = INPUTPARAMETER(MassBpInput);

   MODEL->set_BMuPr(BmuPrimeInput);
   MODEL->set_MuPr(muPrimeInput);
   MODEL->set_vs(vSInput);
   MODEL->set_hE(hEInput);
   MODEL->set_SigmaL(SigmaLInput);
   MODEL->set_KappaPr(KappaPrInput);
   MODEL->set_Sigmax(SigmaxInput);
   MODEL->set_gD(gDInput);
   MODEL->set_Kappa(KappaInput);
   MODEL->set_Lambda12(Lambda12Input);
   MODEL->set_Lambdax(LambdaxInput);
   MODEL->set_fu(fuInput);
   MODEL->set_fd(fdInput);
   MODEL->set_MuPhi(MuPhiInput);
   MODEL->set_XiF(XiFInput);
   MODEL->set_g1p(g1pInput);
   MODEL->set_vsb(vsbInput);
   MODEL->set_vphi(vphiInput);
   MODEL->set_TYd(TYdInput);
   MODEL->set_ThE(ThEInput);
   MODEL->set_TYe(TYeInput);
   MODEL->set_TSigmaL(TSigmaLInput);
   MODEL->set_TKappaPr(TKappaPrInput);
   MODEL->set_TSigmax(TSigmaxInput);
   MODEL->set_TgD(TgDInput);
   MODEL->set_TKappa(TKappaInput);
   MODEL->set_TLambda12(TLambda12Input);
   MODEL->set_TLambdax(TLambdaxInput);
   MODEL->set_Tfu(TfuInput);
   MODEL->set_Tfd(TfdInput);
   MODEL->set_TYu(TYuInput);
   MODEL->set_BMuPhi(BMuPhiInput);
   MODEL->set_LXiF(LXiFInput);
   MODEL->set_mq2(mq2Input);
   MODEL->set_ml2(ml2Input);
   MODEL->set_md2(md2Input);
   MODEL->set_mu2(mu2Input);
   MODEL->set_me2(me2Input);
   MODEL->set_mH1I2(mH1I2Input);
   MODEL->set_mH2I2(mH2I2Input);
   MODEL->set_mSI2(mSI2Input);
   MODEL->set_mDx2(mDx2Input);
   MODEL->set_mDxbar2(mDxbar2Input);
   MODEL->set_mHp2(mHp2Input);
   MODEL->set_mHpbar2(mHpbar2Input);
   MODEL->set_MassB(MassBInput);
   MODEL->set_MassWB(MassWBInput);
   MODEL->set_MassG(MassGInput);
   MODEL->set_MassBp(MassBpInput);


   // the parameters, which are fixed by the EWSB eqs., will now be
   // defined at this scale (at the EWSB loop level defined in the
   // model)
   model->solve_ewsb();
}

double NE6SSM_susy_scale_constraint<Two_scale>::get_scale() const
{
   return scale;
}

double NE6SSM_susy_scale_constraint<Two_scale>::get_initial_scale_guess() const
{
   return initial_scale_guess;
}

void NE6SSM_susy_scale_constraint<Two_scale>::set_model(Two_scale_model* model_)
{
   model = cast_model<NE6SSM<Two_scale> >(model_);
}

void NE6SSM_susy_scale_constraint<Two_scale>::set_input_parameters(const NE6SSM_input_parameters& inputPars_)
{
   inputPars = inputPars_;
}

void NE6SSM_susy_scale_constraint<Two_scale>::clear()
{
   scale = 0.;
   initial_scale_guess = 0.;
   model = NULL;
}

void NE6SSM_susy_scale_constraint<Two_scale>::initialize()
{
   initial_scale_guess = 1000;

   scale = initial_scale_guess;
}

void NE6SSM_susy_scale_constraint<Two_scale>::update_scale()
{
   const auto MSu = MODELPARAMETER(MSu);

   scale = Sqrt(MSu(0)*MSu(5));


}

} // namespace flexiblesusy
