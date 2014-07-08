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

// File generated at Tue 8 Jul 2014 14:46:26

#include "NE6SSM_two_scale_soft_parameters.hpp"
#include "wrappers.hpp"

#include <iostream>

namespace flexiblesusy {

#define INPUT(parameter) input.parameter
#define TRACE_STRUCT soft_traces

NE6SSM_soft_parameters::NE6SSM_soft_parameters(const NE6SSM_input_parameters& input_)
   : NE6SSM_susy_parameters(input_)
   , TYd(Eigen::Matrix<double,3,3>::Zero()), ThE(Eigen::Matrix<double,3,2>
   ::Zero()), TYe(Eigen::Matrix<double,3,3>::Zero()), TSigmaL(0), TKappaPr(0),
   TSigmax(0), TgD(Eigen::Matrix<double,3,3>::Zero()), TKappa(Eigen::Matrix<
   double,3,3>::Zero()), TLambda12(Eigen::Matrix<double,2,2>::Zero()), TLambdax
   (0), Tfu(Eigen::Matrix<double,3,2>::Zero()), Tfd(Eigen::Matrix<double,3,2>
   ::Zero()), TYu(Eigen::Matrix<double,3,3>::Zero()), BMuPr(0), BMuPhi(0), LXiF
   (0), mq2(Eigen::Matrix<double,3,3>::Zero()), ml2(Eigen::Matrix<double,3,3>
   ::Zero()), mHd2(0), mHu2(0), md2(Eigen::Matrix<double,3,3>::Zero()), mu2(
   Eigen::Matrix<double,3,3>::Zero()), me2(Eigen::Matrix<double,3,3>::Zero()),
   ms2(0), msbar2(0), mH1I2(Eigen::Matrix<double,2,2>::Zero()), mH2I2(
   Eigen::Matrix<double,2,2>::Zero()), mSI2(Eigen::Matrix<double,3,3>::Zero()),
   mDx2(Eigen::Matrix<double,3,3>::Zero()), mDxbar2(Eigen::Matrix<double,3,3>
   ::Zero()), mHp2(0), mHpbar2(0), mphi2(0), MassB(0), MassWB(0), MassG(0),
   MassBp(0)

{
   set_number_of_parameters(numberOfParameters);
}

NE6SSM_soft_parameters::NE6SSM_soft_parameters(
   const NE6SSM_susy_parameters& susy_model
   , const Eigen::Matrix<double,3,3>& TYd_, const Eigen::Matrix<double,3,2>&
   ThE_, const Eigen::Matrix<double,3,3>& TYe_, double TSigmaL_, double
   TKappaPr_, double TSigmax_, const Eigen::Matrix<double,3,3>& TgD_, const
   Eigen::Matrix<double,3,3>& TKappa_, const Eigen::Matrix<double,2,2>&
   TLambda12_, double TLambdax_, const Eigen::Matrix<double,3,2>& Tfu_, const
   Eigen::Matrix<double,3,2>& Tfd_, const Eigen::Matrix<double,3,3>& TYu_,
   double BMuPr_, double BMuPhi_, double LXiF_, const Eigen::Matrix<double,3,3>
   & mq2_, const Eigen::Matrix<double,3,3>& ml2_, double mHd2_, double mHu2_,
   const Eigen::Matrix<double,3,3>& md2_, const Eigen::Matrix<double,3,3>& mu2_
   , const Eigen::Matrix<double,3,3>& me2_, double ms2_, double msbar2_, const
   Eigen::Matrix<double,2,2>& mH1I2_, const Eigen::Matrix<double,2,2>& mH2I2_,
   const Eigen::Matrix<double,3,3>& mSI2_, const Eigen::Matrix<double,3,3>&
   mDx2_, const Eigen::Matrix<double,3,3>& mDxbar2_, double mHp2_, double
   mHpbar2_, double mphi2_, double MassB_, double MassWB_, double MassG_,
   double MassBp_

)
   : NE6SSM_susy_parameters(susy_model)
   , TYd(TYd_), ThE(ThE_), TYe(TYe_), TSigmaL(TSigmaL_), TKappaPr(TKappaPr_),
   TSigmax(TSigmax_), TgD(TgD_), TKappa(TKappa_), TLambda12(TLambda12_),
   TLambdax(TLambdax_), Tfu(Tfu_), Tfd(Tfd_), TYu(TYu_), BMuPr(BMuPr_), BMuPhi(
   BMuPhi_), LXiF(LXiF_), mq2(mq2_), ml2(ml2_), mHd2(mHd2_), mHu2(mHu2_), md2(
   md2_), mu2(mu2_), me2(me2_), ms2(ms2_), msbar2(msbar2_), mH1I2(mH1I2_),
   mH2I2(mH2I2_), mSI2(mSI2_), mDx2(mDx2_), mDxbar2(mDxbar2_), mHp2(mHp2_),
   mHpbar2(mHpbar2_), mphi2(mphi2_), MassB(MassB_), MassWB(MassWB_), MassG(
   MassG_), MassBp(MassBp_)

{
   set_number_of_parameters(numberOfParameters);
}

Eigen::ArrayXd NE6SSM_soft_parameters::beta() const
{
   return calc_beta().get();
}

NE6SSM_soft_parameters NE6SSM_soft_parameters::calc_beta() const
{
   Soft_traces soft_traces;
   calc_soft_traces(soft_traces);

   Eigen::Matrix<double,3,3> beta_TYd(calc_beta_TYd_one_loop(TRACE_STRUCT));
   Eigen::Matrix<double,3,2> beta_ThE(calc_beta_ThE_one_loop(TRACE_STRUCT));
   Eigen::Matrix<double,3,3> beta_TYe(calc_beta_TYe_one_loop(TRACE_STRUCT));
   double beta_TSigmaL(calc_beta_TSigmaL_one_loop(TRACE_STRUCT));
   double beta_TKappaPr(calc_beta_TKappaPr_one_loop(TRACE_STRUCT));
   double beta_TSigmax(calc_beta_TSigmax_one_loop(TRACE_STRUCT));
   Eigen::Matrix<double,3,3> beta_TgD(calc_beta_TgD_one_loop(TRACE_STRUCT));
   Eigen::Matrix<double,3,3> beta_TKappa(calc_beta_TKappa_one_loop(TRACE_STRUCT
      ));
   Eigen::Matrix<double,2,2> beta_TLambda12(calc_beta_TLambda12_one_loop(
      TRACE_STRUCT));
   double beta_TLambdax(calc_beta_TLambdax_one_loop(TRACE_STRUCT));
   Eigen::Matrix<double,3,2> beta_Tfu(calc_beta_Tfu_one_loop(TRACE_STRUCT));
   Eigen::Matrix<double,3,2> beta_Tfd(calc_beta_Tfd_one_loop(TRACE_STRUCT));
   Eigen::Matrix<double,3,3> beta_TYu(calc_beta_TYu_one_loop(TRACE_STRUCT));
   double beta_BMuPr(calc_beta_BMuPr_one_loop(TRACE_STRUCT));
   double beta_BMuPhi(calc_beta_BMuPhi_one_loop(TRACE_STRUCT));
   double beta_LXiF(calc_beta_LXiF_one_loop(TRACE_STRUCT));
   Eigen::Matrix<double,3,3> beta_mq2(calc_beta_mq2_one_loop(TRACE_STRUCT));
   Eigen::Matrix<double,3,3> beta_ml2(calc_beta_ml2_one_loop(TRACE_STRUCT));
   double beta_mHd2(calc_beta_mHd2_one_loop(TRACE_STRUCT));
   double beta_mHu2(calc_beta_mHu2_one_loop(TRACE_STRUCT));
   Eigen::Matrix<double,3,3> beta_md2(calc_beta_md2_one_loop(TRACE_STRUCT));
   Eigen::Matrix<double,3,3> beta_mu2(calc_beta_mu2_one_loop(TRACE_STRUCT));
   Eigen::Matrix<double,3,3> beta_me2(calc_beta_me2_one_loop(TRACE_STRUCT));
   double beta_ms2(calc_beta_ms2_one_loop(TRACE_STRUCT));
   double beta_msbar2(calc_beta_msbar2_one_loop(TRACE_STRUCT));
   Eigen::Matrix<double,2,2> beta_mH1I2(calc_beta_mH1I2_one_loop(TRACE_STRUCT))
      ;
   Eigen::Matrix<double,2,2> beta_mH2I2(calc_beta_mH2I2_one_loop(TRACE_STRUCT))
      ;
   Eigen::Matrix<double,3,3> beta_mSI2(calc_beta_mSI2_one_loop(TRACE_STRUCT));
   Eigen::Matrix<double,3,3> beta_mDx2(calc_beta_mDx2_one_loop(TRACE_STRUCT));
   Eigen::Matrix<double,3,3> beta_mDxbar2(calc_beta_mDxbar2_one_loop(
      TRACE_STRUCT));
   double beta_mHp2(calc_beta_mHp2_one_loop(TRACE_STRUCT));
   double beta_mHpbar2(calc_beta_mHpbar2_one_loop(TRACE_STRUCT));
   double beta_mphi2(calc_beta_mphi2_one_loop(TRACE_STRUCT));
   double beta_MassB(calc_beta_MassB_one_loop(TRACE_STRUCT));
   double beta_MassWB(calc_beta_MassWB_one_loop(TRACE_STRUCT));
   double beta_MassG(calc_beta_MassG_one_loop(TRACE_STRUCT));
   double beta_MassBp(calc_beta_MassBp_one_loop(TRACE_STRUCT));

   if (get_loops() > 1) {
      beta_TYd += calc_beta_TYd_two_loop(TRACE_STRUCT);
      beta_ThE += calc_beta_ThE_two_loop(TRACE_STRUCT);
      beta_TYe += calc_beta_TYe_two_loop(TRACE_STRUCT);
      beta_TSigmaL += calc_beta_TSigmaL_two_loop(TRACE_STRUCT);
      beta_TKappaPr += calc_beta_TKappaPr_two_loop(TRACE_STRUCT);
      beta_TSigmax += calc_beta_TSigmax_two_loop(TRACE_STRUCT);
      beta_TgD += calc_beta_TgD_two_loop(TRACE_STRUCT);
      beta_TKappa += calc_beta_TKappa_two_loop(TRACE_STRUCT);
      beta_TLambda12 += calc_beta_TLambda12_two_loop(TRACE_STRUCT);
      beta_TLambdax += calc_beta_TLambdax_two_loop(TRACE_STRUCT);
      beta_Tfu += calc_beta_Tfu_two_loop(TRACE_STRUCT);
      beta_Tfd += calc_beta_Tfd_two_loop(TRACE_STRUCT);
      beta_TYu += calc_beta_TYu_two_loop(TRACE_STRUCT);
      beta_BMuPr += calc_beta_BMuPr_two_loop(TRACE_STRUCT);
      beta_BMuPhi += calc_beta_BMuPhi_two_loop(TRACE_STRUCT);
      beta_LXiF += calc_beta_LXiF_two_loop(TRACE_STRUCT);
      beta_mq2 += calc_beta_mq2_two_loop(TRACE_STRUCT);
      beta_ml2 += calc_beta_ml2_two_loop(TRACE_STRUCT);
      beta_mHd2 += calc_beta_mHd2_two_loop(TRACE_STRUCT);
      beta_mHu2 += calc_beta_mHu2_two_loop(TRACE_STRUCT);
      beta_md2 += calc_beta_md2_two_loop(TRACE_STRUCT);
      beta_mu2 += calc_beta_mu2_two_loop(TRACE_STRUCT);
      beta_me2 += calc_beta_me2_two_loop(TRACE_STRUCT);
      beta_ms2 += calc_beta_ms2_two_loop(TRACE_STRUCT);
      beta_msbar2 += calc_beta_msbar2_two_loop(TRACE_STRUCT);
      beta_mH1I2 += calc_beta_mH1I2_two_loop(TRACE_STRUCT);
      beta_mH2I2 += calc_beta_mH2I2_two_loop(TRACE_STRUCT);
      beta_mSI2 += calc_beta_mSI2_two_loop(TRACE_STRUCT);
      beta_mDx2 += calc_beta_mDx2_two_loop(TRACE_STRUCT);
      beta_mDxbar2 += calc_beta_mDxbar2_two_loop(TRACE_STRUCT);
      beta_mHp2 += calc_beta_mHp2_two_loop(TRACE_STRUCT);
      beta_mHpbar2 += calc_beta_mHpbar2_two_loop(TRACE_STRUCT);
      beta_mphi2 += calc_beta_mphi2_two_loop(TRACE_STRUCT);
      beta_MassB += calc_beta_MassB_two_loop(TRACE_STRUCT);
      beta_MassWB += calc_beta_MassWB_two_loop(TRACE_STRUCT);
      beta_MassG += calc_beta_MassG_two_loop(TRACE_STRUCT);
      beta_MassBp += calc_beta_MassBp_two_loop(TRACE_STRUCT);

   }


   const NE6SSM_susy_parameters susy_betas(NE6SSM_susy_parameters::calc_beta());

   return NE6SSM_soft_parameters(susy_betas, beta_TYd, beta_ThE, beta_TYe, beta_TSigmaL, beta_TKappaPr, beta_TSigmax, beta_TgD, beta_TKappa, beta_TLambda12, beta_TLambdax, beta_Tfu, beta_Tfd, beta_TYu, beta_BMuPr, beta_BMuPhi, beta_LXiF, beta_mq2, beta_ml2, beta_mHd2, beta_mHu2, beta_md2, beta_mu2, beta_me2, beta_ms2, beta_msbar2, beta_mH1I2, beta_mH2I2, beta_mSI2, beta_mDx2, beta_mDxbar2, beta_mHp2, beta_mHpbar2, beta_mphi2, beta_MassB, beta_MassWB, beta_MassG, beta_MassBp);
}

void NE6SSM_soft_parameters::clear()
{
   NE6SSM_susy_parameters::clear();

   TYd = Eigen::Matrix<double,3,3>::Zero();
   ThE = Eigen::Matrix<double,3,2>::Zero();
   TYe = Eigen::Matrix<double,3,3>::Zero();
   TSigmaL = 0.;
   TKappaPr = 0.;
   TSigmax = 0.;
   TgD = Eigen::Matrix<double,3,3>::Zero();
   TKappa = Eigen::Matrix<double,3,3>::Zero();
   TLambda12 = Eigen::Matrix<double,2,2>::Zero();
   TLambdax = 0.;
   Tfu = Eigen::Matrix<double,3,2>::Zero();
   Tfd = Eigen::Matrix<double,3,2>::Zero();
   TYu = Eigen::Matrix<double,3,3>::Zero();
   BMuPr = 0.;
   BMuPhi = 0.;
   LXiF = 0.;
   mq2 = Eigen::Matrix<double,3,3>::Zero();
   ml2 = Eigen::Matrix<double,3,3>::Zero();
   mHd2 = 0.;
   mHu2 = 0.;
   md2 = Eigen::Matrix<double,3,3>::Zero();
   mu2 = Eigen::Matrix<double,3,3>::Zero();
   me2 = Eigen::Matrix<double,3,3>::Zero();
   ms2 = 0.;
   msbar2 = 0.;
   mH1I2 = Eigen::Matrix<double,2,2>::Zero();
   mH2I2 = Eigen::Matrix<double,2,2>::Zero();
   mSI2 = Eigen::Matrix<double,3,3>::Zero();
   mDx2 = Eigen::Matrix<double,3,3>::Zero();
   mDxbar2 = Eigen::Matrix<double,3,3>::Zero();
   mHp2 = 0.;
   mHpbar2 = 0.;
   mphi2 = 0.;
   MassB = 0.;
   MassWB = 0.;
   MassG = 0.;
   MassBp = 0.;

}

const Eigen::ArrayXd NE6SSM_soft_parameters::get() const
{
   Eigen::ArrayXd pars(NE6SSM_susy_parameters::get());
   pars.conservativeResize(numberOfParameters);

   pars(83) = TYd(0,0);
   pars(84) = TYd(0,1);
   pars(85) = TYd(0,2);
   pars(86) = TYd(1,0);
   pars(87) = TYd(1,1);
   pars(88) = TYd(1,2);
   pars(89) = TYd(2,0);
   pars(90) = TYd(2,1);
   pars(91) = TYd(2,2);
   pars(92) = ThE(0,0);
   pars(93) = ThE(0,1);
   pars(94) = ThE(1,0);
   pars(95) = ThE(1,1);
   pars(96) = ThE(2,0);
   pars(97) = ThE(2,1);
   pars(98) = TYe(0,0);
   pars(99) = TYe(0,1);
   pars(100) = TYe(0,2);
   pars(101) = TYe(1,0);
   pars(102) = TYe(1,1);
   pars(103) = TYe(1,2);
   pars(104) = TYe(2,0);
   pars(105) = TYe(2,1);
   pars(106) = TYe(2,2);
   pars(107) = TSigmaL;
   pars(108) = TKappaPr;
   pars(109) = TSigmax;
   pars(110) = TgD(0,0);
   pars(111) = TgD(0,1);
   pars(112) = TgD(0,2);
   pars(113) = TgD(1,0);
   pars(114) = TgD(1,1);
   pars(115) = TgD(1,2);
   pars(116) = TgD(2,0);
   pars(117) = TgD(2,1);
   pars(118) = TgD(2,2);
   pars(119) = TKappa(0,0);
   pars(120) = TKappa(0,1);
   pars(121) = TKappa(0,2);
   pars(122) = TKappa(1,0);
   pars(123) = TKappa(1,1);
   pars(124) = TKappa(1,2);
   pars(125) = TKappa(2,0);
   pars(126) = TKappa(2,1);
   pars(127) = TKappa(2,2);
   pars(128) = TLambda12(0,0);
   pars(129) = TLambda12(0,1);
   pars(130) = TLambda12(1,0);
   pars(131) = TLambda12(1,1);
   pars(132) = TLambdax;
   pars(133) = Tfu(0,0);
   pars(134) = Tfu(0,1);
   pars(135) = Tfu(1,0);
   pars(136) = Tfu(1,1);
   pars(137) = Tfu(2,0);
   pars(138) = Tfu(2,1);
   pars(139) = Tfd(0,0);
   pars(140) = Tfd(0,1);
   pars(141) = Tfd(1,0);
   pars(142) = Tfd(1,1);
   pars(143) = Tfd(2,0);
   pars(144) = Tfd(2,1);
   pars(145) = TYu(0,0);
   pars(146) = TYu(0,1);
   pars(147) = TYu(0,2);
   pars(148) = TYu(1,0);
   pars(149) = TYu(1,1);
   pars(150) = TYu(1,2);
   pars(151) = TYu(2,0);
   pars(152) = TYu(2,1);
   pars(153) = TYu(2,2);
   pars(154) = BMuPr;
   pars(155) = BMuPhi;
   pars(156) = LXiF;
   pars(157) = mq2(0,0);
   pars(158) = mq2(0,1);
   pars(159) = mq2(0,2);
   pars(160) = mq2(1,0);
   pars(161) = mq2(1,1);
   pars(162) = mq2(1,2);
   pars(163) = mq2(2,0);
   pars(164) = mq2(2,1);
   pars(165) = mq2(2,2);
   pars(166) = ml2(0,0);
   pars(167) = ml2(0,1);
   pars(168) = ml2(0,2);
   pars(169) = ml2(1,0);
   pars(170) = ml2(1,1);
   pars(171) = ml2(1,2);
   pars(172) = ml2(2,0);
   pars(173) = ml2(2,1);
   pars(174) = ml2(2,2);
   pars(175) = mHd2;
   pars(176) = mHu2;
   pars(177) = md2(0,0);
   pars(178) = md2(0,1);
   pars(179) = md2(0,2);
   pars(180) = md2(1,0);
   pars(181) = md2(1,1);
   pars(182) = md2(1,2);
   pars(183) = md2(2,0);
   pars(184) = md2(2,1);
   pars(185) = md2(2,2);
   pars(186) = mu2(0,0);
   pars(187) = mu2(0,1);
   pars(188) = mu2(0,2);
   pars(189) = mu2(1,0);
   pars(190) = mu2(1,1);
   pars(191) = mu2(1,2);
   pars(192) = mu2(2,0);
   pars(193) = mu2(2,1);
   pars(194) = mu2(2,2);
   pars(195) = me2(0,0);
   pars(196) = me2(0,1);
   pars(197) = me2(0,2);
   pars(198) = me2(1,0);
   pars(199) = me2(1,1);
   pars(200) = me2(1,2);
   pars(201) = me2(2,0);
   pars(202) = me2(2,1);
   pars(203) = me2(2,2);
   pars(204) = ms2;
   pars(205) = msbar2;
   pars(206) = mH1I2(0,0);
   pars(207) = mH1I2(0,1);
   pars(208) = mH1I2(1,0);
   pars(209) = mH1I2(1,1);
   pars(210) = mH2I2(0,0);
   pars(211) = mH2I2(0,1);
   pars(212) = mH2I2(1,0);
   pars(213) = mH2I2(1,1);
   pars(214) = mSI2(0,0);
   pars(215) = mSI2(0,1);
   pars(216) = mSI2(0,2);
   pars(217) = mSI2(1,0);
   pars(218) = mSI2(1,1);
   pars(219) = mSI2(1,2);
   pars(220) = mSI2(2,0);
   pars(221) = mSI2(2,1);
   pars(222) = mSI2(2,2);
   pars(223) = mDx2(0,0);
   pars(224) = mDx2(0,1);
   pars(225) = mDx2(0,2);
   pars(226) = mDx2(1,0);
   pars(227) = mDx2(1,1);
   pars(228) = mDx2(1,2);
   pars(229) = mDx2(2,0);
   pars(230) = mDx2(2,1);
   pars(231) = mDx2(2,2);
   pars(232) = mDxbar2(0,0);
   pars(233) = mDxbar2(0,1);
   pars(234) = mDxbar2(0,2);
   pars(235) = mDxbar2(1,0);
   pars(236) = mDxbar2(1,1);
   pars(237) = mDxbar2(1,2);
   pars(238) = mDxbar2(2,0);
   pars(239) = mDxbar2(2,1);
   pars(240) = mDxbar2(2,2);
   pars(241) = mHp2;
   pars(242) = mHpbar2;
   pars(243) = mphi2;
   pars(244) = MassB;
   pars(245) = MassWB;
   pars(246) = MassG;
   pars(247) = MassBp;


   return pars;
}

void NE6SSM_soft_parameters::print(std::ostream& ostr) const
{
   NE6SSM_susy_parameters::print(ostr);
   ostr << "soft parameters:\n";
   ostr << "TYd = " << TYd << '\n';
   ostr << "ThE = " << ThE << '\n';
   ostr << "TYe = " << TYe << '\n';
   ostr << "TSigmaL = " << TSigmaL << '\n';
   ostr << "TKappaPr = " << TKappaPr << '\n';
   ostr << "TSigmax = " << TSigmax << '\n';
   ostr << "TgD = " << TgD << '\n';
   ostr << "TKappa = " << TKappa << '\n';
   ostr << "TLambda12 = " << TLambda12 << '\n';
   ostr << "TLambdax = " << TLambdax << '\n';
   ostr << "Tfu = " << Tfu << '\n';
   ostr << "Tfd = " << Tfd << '\n';
   ostr << "TYu = " << TYu << '\n';
   ostr << "BMuPr = " << BMuPr << '\n';
   ostr << "BMuPhi = " << BMuPhi << '\n';
   ostr << "LXiF = " << LXiF << '\n';
   ostr << "mq2 = " << mq2 << '\n';
   ostr << "ml2 = " << ml2 << '\n';
   ostr << "mHd2 = " << mHd2 << '\n';
   ostr << "mHu2 = " << mHu2 << '\n';
   ostr << "md2 = " << md2 << '\n';
   ostr << "mu2 = " << mu2 << '\n';
   ostr << "me2 = " << me2 << '\n';
   ostr << "ms2 = " << ms2 << '\n';
   ostr << "msbar2 = " << msbar2 << '\n';
   ostr << "mH1I2 = " << mH1I2 << '\n';
   ostr << "mH2I2 = " << mH2I2 << '\n';
   ostr << "mSI2 = " << mSI2 << '\n';
   ostr << "mDx2 = " << mDx2 << '\n';
   ostr << "mDxbar2 = " << mDxbar2 << '\n';
   ostr << "mHp2 = " << mHp2 << '\n';
   ostr << "mHpbar2 = " << mHpbar2 << '\n';
   ostr << "mphi2 = " << mphi2 << '\n';
   ostr << "MassB = " << MassB << '\n';
   ostr << "MassWB = " << MassWB << '\n';
   ostr << "MassG = " << MassG << '\n';
   ostr << "MassBp = " << MassBp << '\n';

}

void NE6SSM_soft_parameters::set(const Eigen::ArrayXd& v)
{
   NE6SSM_susy_parameters::set(v);

   TYd(0,0) = v(83);
   TYd(0,1) = v(84);
   TYd(0,2) = v(85);
   TYd(1,0) = v(86);
   TYd(1,1) = v(87);
   TYd(1,2) = v(88);
   TYd(2,0) = v(89);
   TYd(2,1) = v(90);
   TYd(2,2) = v(91);
   ThE(0,0) = v(92);
   ThE(0,1) = v(93);
   ThE(1,0) = v(94);
   ThE(1,1) = v(95);
   ThE(2,0) = v(96);
   ThE(2,1) = v(97);
   TYe(0,0) = v(98);
   TYe(0,1) = v(99);
   TYe(0,2) = v(100);
   TYe(1,0) = v(101);
   TYe(1,1) = v(102);
   TYe(1,2) = v(103);
   TYe(2,0) = v(104);
   TYe(2,1) = v(105);
   TYe(2,2) = v(106);
   TSigmaL = v(107);
   TKappaPr = v(108);
   TSigmax = v(109);
   TgD(0,0) = v(110);
   TgD(0,1) = v(111);
   TgD(0,2) = v(112);
   TgD(1,0) = v(113);
   TgD(1,1) = v(114);
   TgD(1,2) = v(115);
   TgD(2,0) = v(116);
   TgD(2,1) = v(117);
   TgD(2,2) = v(118);
   TKappa(0,0) = v(119);
   TKappa(0,1) = v(120);
   TKappa(0,2) = v(121);
   TKappa(1,0) = v(122);
   TKappa(1,1) = v(123);
   TKappa(1,2) = v(124);
   TKappa(2,0) = v(125);
   TKappa(2,1) = v(126);
   TKappa(2,2) = v(127);
   TLambda12(0,0) = v(128);
   TLambda12(0,1) = v(129);
   TLambda12(1,0) = v(130);
   TLambda12(1,1) = v(131);
   TLambdax = v(132);
   Tfu(0,0) = v(133);
   Tfu(0,1) = v(134);
   Tfu(1,0) = v(135);
   Tfu(1,1) = v(136);
   Tfu(2,0) = v(137);
   Tfu(2,1) = v(138);
   Tfd(0,0) = v(139);
   Tfd(0,1) = v(140);
   Tfd(1,0) = v(141);
   Tfd(1,1) = v(142);
   Tfd(2,0) = v(143);
   Tfd(2,1) = v(144);
   TYu(0,0) = v(145);
   TYu(0,1) = v(146);
   TYu(0,2) = v(147);
   TYu(1,0) = v(148);
   TYu(1,1) = v(149);
   TYu(1,2) = v(150);
   TYu(2,0) = v(151);
   TYu(2,1) = v(152);
   TYu(2,2) = v(153);
   BMuPr = v(154);
   BMuPhi = v(155);
   LXiF = v(156);
   mq2(0,0) = v(157);
   mq2(0,1) = v(158);
   mq2(0,2) = v(159);
   mq2(1,0) = v(160);
   mq2(1,1) = v(161);
   mq2(1,2) = v(162);
   mq2(2,0) = v(163);
   mq2(2,1) = v(164);
   mq2(2,2) = v(165);
   ml2(0,0) = v(166);
   ml2(0,1) = v(167);
   ml2(0,2) = v(168);
   ml2(1,0) = v(169);
   ml2(1,1) = v(170);
   ml2(1,2) = v(171);
   ml2(2,0) = v(172);
   ml2(2,1) = v(173);
   ml2(2,2) = v(174);
   mHd2 = v(175);
   mHu2 = v(176);
   md2(0,0) = v(177);
   md2(0,1) = v(178);
   md2(0,2) = v(179);
   md2(1,0) = v(180);
   md2(1,1) = v(181);
   md2(1,2) = v(182);
   md2(2,0) = v(183);
   md2(2,1) = v(184);
   md2(2,2) = v(185);
   mu2(0,0) = v(186);
   mu2(0,1) = v(187);
   mu2(0,2) = v(188);
   mu2(1,0) = v(189);
   mu2(1,1) = v(190);
   mu2(1,2) = v(191);
   mu2(2,0) = v(192);
   mu2(2,1) = v(193);
   mu2(2,2) = v(194);
   me2(0,0) = v(195);
   me2(0,1) = v(196);
   me2(0,2) = v(197);
   me2(1,0) = v(198);
   me2(1,1) = v(199);
   me2(1,2) = v(200);
   me2(2,0) = v(201);
   me2(2,1) = v(202);
   me2(2,2) = v(203);
   ms2 = v(204);
   msbar2 = v(205);
   mH1I2(0,0) = v(206);
   mH1I2(0,1) = v(207);
   mH1I2(1,0) = v(208);
   mH1I2(1,1) = v(209);
   mH2I2(0,0) = v(210);
   mH2I2(0,1) = v(211);
   mH2I2(1,0) = v(212);
   mH2I2(1,1) = v(213);
   mSI2(0,0) = v(214);
   mSI2(0,1) = v(215);
   mSI2(0,2) = v(216);
   mSI2(1,0) = v(217);
   mSI2(1,1) = v(218);
   mSI2(1,2) = v(219);
   mSI2(2,0) = v(220);
   mSI2(2,1) = v(221);
   mSI2(2,2) = v(222);
   mDx2(0,0) = v(223);
   mDx2(0,1) = v(224);
   mDx2(0,2) = v(225);
   mDx2(1,0) = v(226);
   mDx2(1,1) = v(227);
   mDx2(1,2) = v(228);
   mDx2(2,0) = v(229);
   mDx2(2,1) = v(230);
   mDx2(2,2) = v(231);
   mDxbar2(0,0) = v(232);
   mDxbar2(0,1) = v(233);
   mDxbar2(0,2) = v(234);
   mDxbar2(1,0) = v(235);
   mDxbar2(1,1) = v(236);
   mDxbar2(1,2) = v(237);
   mDxbar2(2,0) = v(238);
   mDxbar2(2,1) = v(239);
   mDxbar2(2,2) = v(240);
   mHp2 = v(241);
   mHpbar2 = v(242);
   mphi2 = v(243);
   MassB = v(244);
   MassWB = v(245);
   MassG = v(246);
   MassBp = v(247);

}

void NE6SSM_soft_parameters::calc_soft_traces(Soft_traces& soft_traces) const
{
   TRACE_STRUCT.traceAdjfdTfd = (fd.adjoint()*Tfd).trace();
   TRACE_STRUCT.traceAdjYdTYd = (Yd.adjoint()*TYd).trace();
   TRACE_STRUCT.traceAdjYeTYe = (Ye.adjoint()*TYe).trace();
   TRACE_STRUCT.tracefdAdjfd = (fd*fd.adjoint()).trace();
   TRACE_STRUCT.traceYdAdjYd = (Yd*Yd.adjoint()).trace();
   TRACE_STRUCT.traceYeAdjYe = (Ye*Ye.adjoint()).trace();
   TRACE_STRUCT.tracefuAdjfu = (fu*fu.adjoint()).trace();
   TRACE_STRUCT.traceYuAdjYu = (Yu*Yu.adjoint()).trace();
   TRACE_STRUCT.traceKappaAdjKappa = (Kappa*(Kappa).adjoint()).trace();
   TRACE_STRUCT.traceLambda12AdjLambda12 = (Lambda12*(Lambda12).adjoint())
      .trace();
   TRACE_STRUCT.traceAdjfuTfu = (fu.adjoint()*Tfu).trace();
   TRACE_STRUCT.traceAdjYuTYu = (Yu.adjoint()*TYu).trace();
   TRACE_STRUCT.traceAdjKappaTKappa = ((Kappa).adjoint()*TKappa).trace();
   TRACE_STRUCT.traceAdjLambda12TLambda12 = ((Lambda12).adjoint()*TLambda12)
      .trace();
   TRACE_STRUCT.tracefdAdjfdTfdAdjfd = (fd*fd.adjoint()*Tfd*fd.adjoint()).trace
      ();
   TRACE_STRUCT.tracefdAdjfdTfuAdjfu = (fd*fd.adjoint()*Tfu*fu.adjoint()).trace
      ();
   TRACE_STRUCT.tracefuAdjfuTfdAdjfd = (fu*fu.adjoint()*Tfd*fd.adjoint()).trace
      ();
   TRACE_STRUCT.tracehEAdjhETYeAdjYe = (hE*hE.adjoint()*TYe*Ye.adjoint()).trace
      ();
   TRACE_STRUCT.traceYdAdjYdTYdAdjYd = (Yd*Yd.adjoint()*TYd*Yd.adjoint()).trace
      ();
   TRACE_STRUCT.traceYdAdjYuTYuAdjYd = (Yd*Yu.adjoint()*TYu*Yd.adjoint()).trace
      ();
   TRACE_STRUCT.traceYeAdjYeThEAdjhE = (Ye*Ye.adjoint()*ThE*hE.adjoint()).trace
      ();
   TRACE_STRUCT.traceYeAdjYeTYeAdjYe = (Ye*Ye.adjoint()*TYe*Ye.adjoint()).trace
      ();
   TRACE_STRUCT.traceYuAdjYdTYdAdjYu = (Yu*Yd.adjoint()*TYd*Yu.adjoint()).trace
      ();
   TRACE_STRUCT.traceAdjfdTfdconjLambda12TpLambda12 = (fd.adjoint()*Tfd*
      Lambda12.conjugate()*(Lambda12).transpose()).trace();
   TRACE_STRUCT.traceAdjgDTpYdconjYdTgD = (gD.adjoint()*Yd.transpose()*
      Yd.conjugate()*TgD).trace();
   TRACE_STRUCT.traceAdjYdTYdconjgDTpgD = (Yd.adjoint()*TYd*gD.conjugate()*
      gD.transpose()).trace();
   TRACE_STRUCT.traceAdjLambda12TpfdconjfdTLambda12 = ((Lambda12).adjoint()*
      fd.transpose()*fd.conjugate()*TLambda12).trace();
   TRACE_STRUCT.traceAdjgDTgD = (gD.adjoint()*TgD).trace();
   TRACE_STRUCT.traceAdjhEThE = (hE.adjoint()*ThE).trace();
   TRACE_STRUCT.tracegDAdjgD = (gD*gD.adjoint()).trace();
   TRACE_STRUCT.tracehEAdjhE = (hE*hE.adjoint()).trace();
   TRACE_STRUCT.tracefdAdjfdfdAdjfd = (fd*fd.adjoint()*fd*fd.adjoint()).trace()
      ;
   TRACE_STRUCT.tracefdAdjfdfuAdjfu = (fd*fd.adjoint()*fu*fu.adjoint()).trace()
      ;
   TRACE_STRUCT.tracegDAdjgDTpYdconjYd = (gD*gD.adjoint()*Yd.transpose()*
      Yd.conjugate()).trace();
   TRACE_STRUCT.tracehEAdjhEYeAdjYe = (hE*hE.adjoint()*Ye*Ye.adjoint()).trace()
      ;
   TRACE_STRUCT.traceYdAdjYdYdAdjYd = (Yd*Yd.adjoint()*Yd*Yd.adjoint()).trace()
      ;
   TRACE_STRUCT.traceYdAdjYuYuAdjYd = (Yd*Yu.adjoint()*Yu*Yd.adjoint()).trace()
      ;
   TRACE_STRUCT.traceYeAdjYeYeAdjYe = (Ye*Ye.adjoint()*Ye*Ye.adjoint()).trace()
      ;
   TRACE_STRUCT.traceLambda12AdjLambda12Tpfdconjfd = (Lambda12*(Lambda12)
      .adjoint()*fd.transpose()*fd.conjugate()).trace();
   TRACE_STRUCT.tracefuAdjhEThEAdjfu = (fu*hE.adjoint()*ThE*fu.adjoint()).trace
      ();
   TRACE_STRUCT.tracegDAdjgDTgDAdjgD = (gD*gD.adjoint()*TgD*gD.adjoint()).trace
      ();
   TRACE_STRUCT.tracegDAdjKappaTKappaAdjgD = (gD*(Kappa).adjoint()*TKappa*
      gD.adjoint()).trace();
   TRACE_STRUCT.tracehEAdjfuTfuAdjhE = (hE*fu.adjoint()*Tfu*hE.adjoint()).trace
      ();
   TRACE_STRUCT.tracehEAdjhEThEAdjhE = (hE*hE.adjoint()*ThE*hE.adjoint()).trace
      ();
   TRACE_STRUCT.tracehEAdjLambda12TLambda12AdjhE = (hE*(Lambda12).adjoint()*
      TLambda12*hE.adjoint()).trace();
   TRACE_STRUCT.traceKappaAdjgDTgDAdjKappa = (Kappa*gD.adjoint()*TgD*(Kappa)
      .adjoint()).trace();
   TRACE_STRUCT.traceLambda12AdjhEThEAdjLambda12 = (Lambda12*hE.adjoint()*ThE*(
      Lambda12).adjoint()).trace();
   TRACE_STRUCT.traceAdjgDTpYuconjYuTgD = (gD.adjoint()*Yu.transpose()*
      Yu.conjugate()*TgD).trace();
   TRACE_STRUCT.traceAdjYuTYuconjgDTpgD = (Yu.adjoint()*TYu*gD.conjugate()*
      gD.transpose()).trace();
   TRACE_STRUCT.tracefuAdjhEhEAdjfu = (fu*hE.adjoint()*hE*fu.adjoint()).trace()
      ;
   TRACE_STRUCT.tracegDAdjgDgDAdjgD = (gD*gD.adjoint()*gD*gD.adjoint()).trace()
      ;
   TRACE_STRUCT.tracegDAdjgDTpYuconjYu = (gD*gD.adjoint()*Yu.transpose()*
      Yu.conjugate()).trace();
   TRACE_STRUCT.tracegDAdjKappaKappaAdjgD = (gD*(Kappa).adjoint()*Kappa*
      gD.adjoint()).trace();
   TRACE_STRUCT.tracehEAdjhEhEAdjhE = (hE*hE.adjoint()*hE*hE.adjoint()).trace()
      ;
   TRACE_STRUCT.tracehEAdjLambda12Lambda12AdjhE = (hE*(Lambda12).adjoint()*
      Lambda12*hE.adjoint()).trace();
   TRACE_STRUCT.tracefuAdjLambda12Lambda12Adjfu = (fu*(Lambda12).adjoint()*
      Lambda12*fu.adjoint()).trace();
   TRACE_STRUCT.tracefuAdjLambda12TLambda12Adjfu = (fu*(Lambda12).adjoint()*
      TLambda12*fu.adjoint()).trace();
   TRACE_STRUCT.traceKappaAdjKappaKappaAdjKappa = (Kappa*(Kappa).adjoint()*
      Kappa*(Kappa).adjoint()).trace();
   TRACE_STRUCT.traceKappaAdjKappaTKappaAdjKappa = (Kappa*(Kappa).adjoint()*
      TKappa*(Kappa).adjoint()).trace();
   TRACE_STRUCT.traceLambda12AdjfuTfuAdjLambda12 = (Lambda12*fu.adjoint()*Tfu*(
      Lambda12).adjoint()).trace();
   TRACE_STRUCT.traceLambda12AdjLambda12Lambda12AdjLambda12 = (Lambda12*(
      Lambda12).adjoint()*Lambda12*(Lambda12).adjoint()).trace();
   TRACE_STRUCT.traceLambda12AdjLambda12TLambda12AdjLambda12 = (Lambda12*(
      Lambda12).adjoint()*TLambda12*(Lambda12).adjoint()).trace();
   TRACE_STRUCT.tracefuAdjfufuAdjfu = (fu*fu.adjoint()*fu*fu.adjoint()).trace()
      ;
   TRACE_STRUCT.tracefuAdjfuTfuAdjfu = (fu*fu.adjoint()*Tfu*fu.adjoint()).trace
      ();
   TRACE_STRUCT.traceYuAdjYuYuAdjYu = (Yu*Yu.adjoint()*Yu*Yu.adjoint()).trace()
      ;
   TRACE_STRUCT.traceYuAdjYuTYuAdjYu = (Yu*Yu.adjoint()*TYu*Yu.adjoint()).trace
      ();
   TRACE_STRUCT.traceconjTgDTpgD = (TgD.conjugate()*gD.transpose()).trace();
   TRACE_STRUCT.traceconjTgDTpTgD = (TgD.conjugate()*(TgD).transpose()).trace()
      ;
   TRACE_STRUCT.traceconjThETphE = (ThE.conjugate()*hE.transpose()).trace();
   TRACE_STRUCT.traceconjThETpThE = (ThE.conjugate()*(ThE).transpose()).trace()
      ;
   TRACE_STRUCT.tracegDmDxbar2AdjgD = (gD*mDxbar2*gD.adjoint()).trace();
   TRACE_STRUCT.tracegDAdjgDmq2 = (gD*gD.adjoint()*mq2).trace();
   TRACE_STRUCT.tracehEAdjhEconjme2 = (hE*hE.adjoint()*me2.conjugate()).trace()
      ;
   TRACE_STRUCT.tracehEconjmH1I2AdjhE = (hE*mH1I2.conjugate()*hE.adjoint())
      .trace();
   TRACE_STRUCT.traceconjTfdTpTfd = (Tfd.conjugate()*(Tfd).transpose()).trace()
      ;
   TRACE_STRUCT.traceconjTYdTpTYd = (TYd.conjugate()*(TYd).transpose()).trace()
      ;
   TRACE_STRUCT.traceconjTYeTpTYe = (TYe.conjugate()*(TYe).transpose()).trace()
      ;
   TRACE_STRUCT.tracefdmH2I2Adjfd = (fd*mH2I2*fd.adjoint()).trace();
   TRACE_STRUCT.tracefdAdjfdconjmSI2 = (fd*fd.adjoint()*mSI2.conjugate()).trace
      ();
   TRACE_STRUCT.tracemd2YdAdjYd = (md2*Yd*Yd.adjoint()).trace();
   TRACE_STRUCT.traceme2YeAdjYe = (me2*Ye*Ye.adjoint()).trace();
   TRACE_STRUCT.traceml2AdjYeYe = (ml2*Ye.adjoint()*Ye).trace();
   TRACE_STRUCT.tracemq2AdjYdYd = (mq2*Yd.adjoint()*Yd).trace();
   TRACE_STRUCT.traceconjTfdTpfd = (Tfd.conjugate()*fd.transpose()).trace();
   TRACE_STRUCT.traceconjTYdTpYd = (TYd.conjugate()*Yd.transpose()).trace();
   TRACE_STRUCT.traceconjTYeTpYe = (TYe.conjugate()*Ye.transpose()).trace();
   TRACE_STRUCT.traceconjTfuTpTfu = (Tfu.conjugate()*(Tfu).transpose()).trace()
      ;
   TRACE_STRUCT.traceconjTYuTpTYu = (TYu.conjugate()*(TYu).transpose()).trace()
      ;
   TRACE_STRUCT.tracefumH1I2Adjfu = (fu*mH1I2*fu.adjoint()).trace();
   TRACE_STRUCT.tracefuAdjfuconjmSI2 = (fu*fu.adjoint()*mSI2.conjugate()).trace
      ();
   TRACE_STRUCT.tracemq2AdjYuYu = (mq2*Yu.adjoint()*Yu).trace();
   TRACE_STRUCT.tracemu2YuAdjYu = (mu2*Yu*Yu.adjoint()).trace();
   TRACE_STRUCT.traceconjTfuTpfu = (Tfu.conjugate()*fu.transpose()).trace();
   TRACE_STRUCT.traceconjTYuTpYu = (TYu.conjugate()*Yu.transpose()).trace();
   TRACE_STRUCT.tracegDAdjgDconjmq2 = (gD*gD.adjoint()*mq2.conjugate()).trace()
      ;
   TRACE_STRUCT.tracegDconjmDxbar2AdjgD = (gD*mDxbar2.conjugate()*gD.adjoint())
      .trace();
   TRACE_STRUCT.tracehEmH1I2AdjhE = (hE*mH1I2*hE.adjoint()).trace();
   TRACE_STRUCT.tracehEAdjhEme2 = (hE*hE.adjoint()*me2).trace();
   TRACE_STRUCT.traceconjTKappaTpKappa = (TKappa.conjugate()*(Kappa).transpose(
      )).trace();
   TRACE_STRUCT.traceconjTKappaTpTKappa = (TKappa.conjugate()*(TKappa)
      .transpose()).trace();
   TRACE_STRUCT.traceconjTLambda12TpLambda12 = (TLambda12.conjugate()*(Lambda12
      ).transpose()).trace();
   TRACE_STRUCT.traceconjTLambda12TpTLambda12 = (TLambda12.conjugate()*(
      TLambda12).transpose()).trace();
   TRACE_STRUCT.tracemH1I2AdjLambda12Lambda12 = (mH1I2*(Lambda12).adjoint()*
      Lambda12).trace();
   TRACE_STRUCT.traceKappaAdjKappaconjmDx2 = (Kappa*(Kappa).adjoint()*
      mDx2.conjugate()).trace();
   TRACE_STRUCT.traceKappaconjmDxbar2AdjKappa = (Kappa*mDxbar2.conjugate()*(
      Kappa).adjoint()).trace();
   TRACE_STRUCT.traceLambda12AdjLambda12conjmH2I2 = (Lambda12*(Lambda12)
      .adjoint()*mH2I2.conjugate()).trace();
   TRACE_STRUCT.tracefdAdjfdTfdAdjTfd = (fd*fd.adjoint()*Tfd*(Tfd).adjoint())
      .trace();
   TRACE_STRUCT.tracefdAdjfdTfuAdjTfu = (fd*fd.adjoint()*Tfu*(Tfu).adjoint())
      .trace();
   TRACE_STRUCT.tracefdAdjTfdTfdAdjfd = (fd*(Tfd).adjoint()*Tfd*fd.adjoint())
      .trace();
   TRACE_STRUCT.tracefdAdjTfdTfuAdjfu = (fd*(Tfd).adjoint()*Tfu*fu.adjoint())
      .trace();
   TRACE_STRUCT.tracefdconjTLambda12TpTLambda12Adjfd = (fd*TLambda12.conjugate(
      )*(TLambda12).transpose()*fd.adjoint()).trace();
   TRACE_STRUCT.tracefuAdjfuTfdAdjTfd = (fu*fu.adjoint()*Tfd*(Tfd).adjoint())
      .trace();
   TRACE_STRUCT.tracefuAdjTfuTfdAdjfd = (fu*(Tfu).adjoint()*Tfd*fd.adjoint())
      .trace();
   TRACE_STRUCT.tracegDAdjgDTpTYdconjTYd = (gD*gD.adjoint()*(TYd).transpose()*
      TYd.conjugate()).trace();
   TRACE_STRUCT.tracehEAdjhETYeAdjTYe = (hE*hE.adjoint()*TYe*(TYe).adjoint())
      .trace();
   TRACE_STRUCT.tracehEAdjThETYeAdjYe = (hE*(ThE).adjoint()*TYe*Ye.adjoint())
      .trace();
   TRACE_STRUCT.traceYdAdjYdTYdAdjTYd = (Yd*Yd.adjoint()*TYd*(TYd).adjoint())
      .trace();
   TRACE_STRUCT.traceYdAdjYuTYuAdjTYd = (Yd*Yu.adjoint()*TYu*(TYd).adjoint())
      .trace();
   TRACE_STRUCT.traceYdAdjTYdTYdAdjYd = (Yd*(TYd).adjoint()*TYd*Yd.adjoint())
      .trace();
   TRACE_STRUCT.traceYdAdjTYuTYuAdjYd = (Yd*(TYu).adjoint()*TYu*Yd.adjoint())
      .trace();
   TRACE_STRUCT.traceYdconjTgDTpTgDAdjYd = (Yd*TgD.conjugate()*(TgD).transpose(
      )*Yd.adjoint()).trace();
   TRACE_STRUCT.traceYeAdjYeThEAdjThE = (Ye*Ye.adjoint()*ThE*(ThE).adjoint())
      .trace();
   TRACE_STRUCT.traceYeAdjYeTYeAdjTYe = (Ye*Ye.adjoint()*TYe*(TYe).adjoint())
      .trace();
   TRACE_STRUCT.traceYeAdjTYeThEAdjhE = (Ye*(TYe).adjoint()*ThE*hE.adjoint())
      .trace();
   TRACE_STRUCT.traceYeAdjTYeTYeAdjYe = (Ye*(TYe).adjoint()*TYe*Ye.adjoint())
      .trace();
   TRACE_STRUCT.traceYuAdjYdTYdAdjTYu = (Yu*Yd.adjoint()*TYd*(TYu).adjoint())
      .trace();
   TRACE_STRUCT.traceYuAdjTYdTYdAdjYu = (Yu*(TYd).adjoint()*TYd*Yu.adjoint())
      .trace();
   TRACE_STRUCT.traceLambda12AdjLambda12TpTfdconjTfd = (Lambda12*(Lambda12)
      .adjoint()*(Tfd).transpose()*Tfd.conjugate()).trace();
   TRACE_STRUCT.traceAdjfdTfdconjTLambda12TpLambda12 = (fd.adjoint()*Tfd*
      TLambda12.conjugate()*(Lambda12).transpose()).trace();
   TRACE_STRUCT.traceAdjgDTpYdconjTYdTgD = (gD.adjoint()*Yd.transpose()*
      TYd.conjugate()*TgD).trace();
   TRACE_STRUCT.traceAdjYdTYdconjTgDTpgD = (Yd.adjoint()*TYd*TgD.conjugate()*
      gD.transpose()).trace();
   TRACE_STRUCT.traceAdjLambda12TpfdconjTfdTLambda12 = ((Lambda12).adjoint()*
      fd.transpose()*Tfd.conjugate()*TLambda12).trace();
   TRACE_STRUCT.tracefdmH2I2AdjfdfdAdjfd = (fd*mH2I2*fd.adjoint()*fd*fd.adjoint
      ()).trace();
   TRACE_STRUCT.tracefdmH2I2AdjfdfuAdjfu = (fd*mH2I2*fd.adjoint()*fu*fu.adjoint
      ()).trace();
   TRACE_STRUCT.tracefdAdjfdfdmH2I2Adjfd = (fd*fd.adjoint()*fd*mH2I2*fd.adjoint
      ()).trace();
   TRACE_STRUCT.tracefdAdjfdfumH1I2Adjfu = (fd*fd.adjoint()*fu*mH1I2*fu.adjoint
      ()).trace();
   TRACE_STRUCT.tracefdAdjfdfuAdjfuconjmSI2 = (fd*fd.adjoint()*fu*fu.adjoint()*
      mSI2.conjugate()).trace();
   TRACE_STRUCT.tracefdAdjfdconjmSI2fdAdjfd = (fd*fd.adjoint()*mSI2.conjugate()
      *fd*fd.adjoint()).trace();
   TRACE_STRUCT.tracefdAdjfdconjmSI2fuAdjfu = (fd*fd.adjoint()*mSI2.conjugate()
      *fu*fu.adjoint()).trace();
   TRACE_STRUCT.tracefdconjLambda12TpLambda12AdjfdconjmSI2 = (fd*
      Lambda12.conjugate()*(Lambda12).transpose()*fd.adjoint()*mSI2.conjugate())
      .trace();
   TRACE_STRUCT.tracegDAdjgDconjmq2TpYdconjYd = (gD*gD.adjoint()*mq2.conjugate(
      )*Yd.transpose()*Yd.conjugate()).trace();
   TRACE_STRUCT.tracegDAdjgDTpYdconjmd2conjYd = (gD*gD.adjoint()*Yd.transpose()
      *md2.conjugate()*Yd.conjugate()).trace();
   TRACE_STRUCT.tracegDAdjgDTpYdconjYdconjmq2 = (gD*gD.adjoint()*Yd.transpose()
      *Yd.conjugate()*mq2.conjugate()).trace();
   TRACE_STRUCT.tracegDconjmDxbar2AdjgDTpYdconjYd = (gD*mDxbar2.conjugate()*
      gD.adjoint()*Yd.transpose()*Yd.conjugate()).trace();
   TRACE_STRUCT.tracehEmH1I2AdjhEYeAdjYe = (hE*mH1I2*hE.adjoint()*Ye*Ye.adjoint
      ()).trace();
   TRACE_STRUCT.tracehEAdjhEme2YeAdjYe = (hE*hE.adjoint()*me2*Ye*Ye.adjoint())
      .trace();
   TRACE_STRUCT.tracehEAdjhEYeml2AdjYe = (hE*hE.adjoint()*Ye*ml2*Ye.adjoint())
      .trace();
   TRACE_STRUCT.tracehEAdjhEYeAdjYeme2 = (hE*hE.adjoint()*Ye*Ye.adjoint()*me2)
      .trace();
   TRACE_STRUCT.tracemd2YdAdjYdYdAdjYd = (md2*Yd*Yd.adjoint()*Yd*Yd.adjoint())
      .trace();
   TRACE_STRUCT.tracemd2YdAdjYuYuAdjYd = (md2*Yd*Yu.adjoint()*Yu*Yd.adjoint())
      .trace();
   TRACE_STRUCT.traceme2YeAdjYeYeAdjYe = (me2*Ye*Ye.adjoint()*Ye*Ye.adjoint())
      .trace();
   TRACE_STRUCT.tracemH1I2AdjLambda12TpfdconjfdLambda12 = (mH1I2*(Lambda12)
      .adjoint()*fd.transpose()*fd.conjugate()*Lambda12).trace();
   TRACE_STRUCT.traceml2AdjYeYeAdjYeYe = (ml2*Ye.adjoint()*Ye*Ye.adjoint()*Ye)
      .trace();
   TRACE_STRUCT.tracemq2AdjYdYdAdjYdYd = (mq2*Yd.adjoint()*Yd*Yd.adjoint()*Yd)
      .trace();
   TRACE_STRUCT.tracemq2AdjYdYdAdjYuYu = (mq2*Yd.adjoint()*Yd*Yu.adjoint()*Yu)
      .trace();
   TRACE_STRUCT.tracemq2AdjYuYuAdjYdYd = (mq2*Yu.adjoint()*Yu*Yd.adjoint()*Yd)
      .trace();
   TRACE_STRUCT.tracemu2YuAdjYdYdAdjYu = (mu2*Yu*Yd.adjoint()*Yd*Yu.adjoint())
      .trace();
   TRACE_STRUCT.traceLambda12AdjLambda12conjmH2I2Tpfdconjfd = (Lambda12*(
      Lambda12).adjoint()*mH2I2.conjugate()*fd.transpose()*fd.conjugate()).trace()
      ;
   TRACE_STRUCT.traceLambda12AdjLambda12TpfdconjfdconjmH2I2 = (Lambda12*(
      Lambda12).adjoint()*fd.transpose()*fd.conjugate()*mH2I2.conjugate()).trace()
      ;
   TRACE_STRUCT.tracefuAdjfuTfuAdjTfu = (fu*fu.adjoint()*Tfu*(Tfu).adjoint())
      .trace();
   TRACE_STRUCT.tracefuAdjhEThEAdjTfu = (fu*hE.adjoint()*ThE*(Tfu).adjoint())
      .trace();
   TRACE_STRUCT.tracefuAdjLambda12TLambda12AdjTfu = (fu*(Lambda12).adjoint()*
      TLambda12*(Tfu).adjoint()).trace();
   TRACE_STRUCT.tracefuAdjTfuTfuAdjfu = (fu*(Tfu).adjoint()*Tfu*fu.adjoint())
      .trace();
   TRACE_STRUCT.tracefuAdjThEThEAdjfu = (fu*(ThE).adjoint()*ThE*fu.adjoint())
      .trace();
   TRACE_STRUCT.tracefuAdjTLambda12TLambda12Adjfu = (fu*(TLambda12).adjoint()*
      TLambda12*fu.adjoint()).trace();
   TRACE_STRUCT.tracegDAdjgDTpTYuconjTYu = (gD*gD.adjoint()*(TYu).transpose()*
      TYu.conjugate()).trace();
   TRACE_STRUCT.tracehEAdjfuTfuAdjThE = (hE*fu.adjoint()*Tfu*(ThE).adjoint())
      .trace();
   TRACE_STRUCT.tracehEAdjTfuTfuAdjhE = (hE*(Tfu).adjoint()*Tfu*hE.adjoint())
      .trace();
   TRACE_STRUCT.traceYuAdjYuTYuAdjTYu = (Yu*Yu.adjoint()*TYu*(TYu).adjoint())
      .trace();
   TRACE_STRUCT.traceYuAdjTYuTYuAdjYu = (Yu*(TYu).adjoint()*TYu*Yu.adjoint())
      .trace();
   TRACE_STRUCT.traceYuconjTgDTpTgDAdjYu = (Yu*TgD.conjugate()*(TgD).transpose(
      )*Yu.adjoint()).trace();
   TRACE_STRUCT.traceLambda12AdjfuTfuAdjTLambda12 = (Lambda12*fu.adjoint()*Tfu*
      (TLambda12).adjoint()).trace();
   TRACE_STRUCT.traceLambda12AdjTfuTfuAdjLambda12 = (Lambda12*(Tfu).adjoint()*
      Tfu*(Lambda12).adjoint()).trace();
   TRACE_STRUCT.traceAdjgDTpYuconjTYuTgD = (gD.adjoint()*Yu.transpose()*
      TYu.conjugate()*TgD).trace();
   TRACE_STRUCT.traceAdjYuTYuconjTgDTpgD = (Yu.adjoint()*TYu*TgD.conjugate()*
      gD.transpose()).trace();
   TRACE_STRUCT.tracefumH1I2AdjfufuAdjfu = (fu*mH1I2*fu.adjoint()*fu*fu.adjoint
      ()).trace();
   TRACE_STRUCT.tracefumH1I2AdjhEhEAdjfu = (fu*mH1I2*hE.adjoint()*hE*fu.adjoint
      ()).trace();
   TRACE_STRUCT.tracefumH1I2AdjLambda12Lambda12Adjfu = (fu*mH1I2*(Lambda12)
      .adjoint()*Lambda12*fu.adjoint()).trace();
   TRACE_STRUCT.tracefuAdjfufumH1I2Adjfu = (fu*fu.adjoint()*fu*mH1I2*fu.adjoint
      ()).trace();
   TRACE_STRUCT.tracefuAdjfuconjmSI2fuAdjfu = (fu*fu.adjoint()*mSI2.conjugate()
      *fu*fu.adjoint()).trace();
   TRACE_STRUCT.tracefuAdjhEhEmH1I2Adjfu = (fu*hE.adjoint()*hE*mH1I2*fu.adjoint
      ()).trace();
   TRACE_STRUCT.tracefuAdjhEhEAdjfuconjmSI2 = (fu*hE.adjoint()*hE*fu.adjoint()*
      mSI2.conjugate()).trace();
   TRACE_STRUCT.tracefuAdjhEme2hEAdjfu = (fu*hE.adjoint()*me2*hE*fu.adjoint())
      .trace();
   TRACE_STRUCT.tracefuAdjLambda12Lambda12mH1I2Adjfu = (fu*(Lambda12).adjoint()
      *Lambda12*mH1I2*fu.adjoint()).trace();
   TRACE_STRUCT.tracefuAdjLambda12Lambda12AdjfuconjmSI2 = (fu*(Lambda12)
      .adjoint()*Lambda12*fu.adjoint()*mSI2.conjugate()).trace();
   TRACE_STRUCT.tracefuAdjLambda12conjmH2I2Lambda12Adjfu = (fu*(Lambda12)
      .adjoint()*mH2I2.conjugate()*Lambda12*fu.adjoint()).trace();
   TRACE_STRUCT.tracegDAdjgDconjmq2TpYuconjYu = (gD*gD.adjoint()*mq2.conjugate(
      )*Yu.transpose()*Yu.conjugate()).trace();
   TRACE_STRUCT.tracegDAdjgDTpYuconjmu2conjYu = (gD*gD.adjoint()*Yu.transpose()
      *mu2.conjugate()*Yu.conjugate()).trace();
   TRACE_STRUCT.tracegDAdjgDTpYuconjYuconjmq2 = (gD*gD.adjoint()*Yu.transpose()
      *Yu.conjugate()*mq2.conjugate()).trace();
   TRACE_STRUCT.tracegDconjmDxbar2AdjgDTpYuconjYu = (gD*mDxbar2.conjugate()*
      gD.adjoint()*Yu.transpose()*Yu.conjugate()).trace();
   TRACE_STRUCT.tracemq2AdjYuYuAdjYuYu = (mq2*Yu.adjoint()*Yu*Yu.adjoint()*Yu)
      .trace();
   TRACE_STRUCT.tracemu2YuAdjYuYuAdjYu = (mu2*Yu*Yu.adjoint()*Yu*Yu.adjoint())
      .trace();
   TRACE_STRUCT.tracegDAdjKappaTKappaAdjTgD = (gD*(Kappa).adjoint()*TKappa*(TgD
      ).adjoint()).trace();
   TRACE_STRUCT.tracegDAdjTKappaTKappaAdjgD = (gD*(TKappa).adjoint()*TKappa*
      gD.adjoint()).trace();
   TRACE_STRUCT.tracehEAdjLambda12TLambda12AdjThE = (hE*(Lambda12).adjoint()*
      TLambda12*(ThE).adjoint()).trace();
   TRACE_STRUCT.tracehEAdjTLambda12TLambda12AdjhE = (hE*(TLambda12).adjoint()*
      TLambda12*hE.adjoint()).trace();
   TRACE_STRUCT.traceKappaAdjgDTgDAdjTKappa = (Kappa*gD.adjoint()*TgD*(TKappa)
      .adjoint()).trace();
   TRACE_STRUCT.traceKappaAdjKappaTKappaAdjTKappa = (Kappa*(Kappa).adjoint()*
      TKappa*(TKappa).adjoint()).trace();
   TRACE_STRUCT.traceKappaAdjTgDTgDAdjKappa = (Kappa*(TgD).adjoint()*TgD*(Kappa
      ).adjoint()).trace();
   TRACE_STRUCT.traceKappaAdjTKappaTKappaAdjKappa = (Kappa*(TKappa).adjoint()*
      TKappa*(Kappa).adjoint()).trace();
   TRACE_STRUCT.traceLambda12AdjhEThEAdjTLambda12 = (Lambda12*hE.adjoint()*ThE*
      (TLambda12).adjoint()).trace();
   TRACE_STRUCT.traceLambda12AdjLambda12TLambda12AdjTLambda12 = (Lambda12*(
      Lambda12).adjoint()*TLambda12*(TLambda12).adjoint()).trace();
   TRACE_STRUCT.traceLambda12AdjThEThEAdjLambda12 = (Lambda12*(ThE).adjoint()*
      ThE*(Lambda12).adjoint()).trace();
   TRACE_STRUCT.traceLambda12AdjTLambda12TLambda12AdjLambda12 = (Lambda12*(
      TLambda12).adjoint()*TLambda12*(Lambda12).adjoint()).trace();
   TRACE_STRUCT.tracegDAdjKappaKappaAdjgDconjmq2 = (gD*(Kappa).adjoint()*Kappa*
      gD.adjoint()*mq2.conjugate()).trace();
   TRACE_STRUCT.tracegDAdjKappaKappaconjmDxbar2AdjgD = (gD*(Kappa).adjoint()*
      Kappa*mDxbar2.conjugate()*gD.adjoint()).trace();
   TRACE_STRUCT.tracegDAdjKappaconjmDx2KappaAdjgD = (gD*(Kappa).adjoint()*
      mDx2.conjugate()*Kappa*gD.adjoint()).trace();
   TRACE_STRUCT.tracegDconjmDxbar2AdjKappaKappaAdjgD = (gD*mDxbar2.conjugate()*
      (Kappa).adjoint()*Kappa*gD.adjoint()).trace();
   TRACE_STRUCT.tracehEmH1I2AdjLambda12Lambda12AdjhE = (hE*mH1I2*(Lambda12)
      .adjoint()*Lambda12*hE.adjoint()).trace();
   TRACE_STRUCT.tracehEAdjLambda12Lambda12mH1I2AdjhE = (hE*(Lambda12).adjoint()
      *Lambda12*mH1I2*hE.adjoint()).trace();
   TRACE_STRUCT.tracehEAdjLambda12Lambda12AdjhEme2 = (hE*(Lambda12).adjoint()*
      Lambda12*hE.adjoint()*me2).trace();
   TRACE_STRUCT.tracehEAdjLambda12conjmH2I2Lambda12AdjhE = (hE*(Lambda12)
      .adjoint()*mH2I2.conjugate()*Lambda12*hE.adjoint()).trace();
   TRACE_STRUCT.tracemH1I2AdjLambda12Lambda12AdjLambda12Lambda12 = (mH1I2*(
      Lambda12).adjoint()*Lambda12*(Lambda12).adjoint()*Lambda12).trace();
   TRACE_STRUCT.traceKappaAdjKappaKappaAdjKappaconjmDx2 = (Kappa*(Kappa)
      .adjoint()*Kappa*(Kappa).adjoint()*mDx2.conjugate()).trace();
   TRACE_STRUCT.traceKappaAdjKappaKappaconjmDxbar2AdjKappa = (Kappa*(Kappa)
      .adjoint()*Kappa*mDxbar2.conjugate()*(Kappa).adjoint()).trace();
   TRACE_STRUCT.traceKappaAdjKappaconjmDx2KappaAdjKappa = (Kappa*(Kappa)
      .adjoint()*mDx2.conjugate()*Kappa*(Kappa).adjoint()).trace();
   TRACE_STRUCT.traceKappaconjmDxbar2AdjKappaKappaAdjKappa = (Kappa*
      mDxbar2.conjugate()*(Kappa).adjoint()*Kappa*(Kappa).adjoint()).trace();
   TRACE_STRUCT.traceLambda12AdjLambda12Lambda12AdjLambda12conjmH2I2 = (
      Lambda12*(Lambda12).adjoint()*Lambda12*(Lambda12).adjoint()*mH2I2.conjugate(
      )).trace();
   TRACE_STRUCT.traceLambda12AdjLambda12conjmH2I2Lambda12AdjLambda12 = (
      Lambda12*(Lambda12).adjoint()*mH2I2.conjugate()*Lambda12*(Lambda12).adjoint(
      )).trace();
   TRACE_STRUCT.tracegDAdjgDTgDAdjTgD = (gD*gD.adjoint()*TgD*(TgD).adjoint())
      .trace();
   TRACE_STRUCT.tracegDAdjTgDTgDAdjgD = (gD*(TgD).adjoint()*TgD*gD.adjoint())
      .trace();
   TRACE_STRUCT.tracehEAdjhEThEAdjThE = (hE*hE.adjoint()*ThE*(ThE).adjoint())
      .trace();
   TRACE_STRUCT.tracehEAdjThEThEAdjhE = (hE*(ThE).adjoint()*ThE*hE.adjoint())
      .trace();
   TRACE_STRUCT.tracegDAdjgDgDconjmDxbar2AdjgD = (gD*gD.adjoint()*gD*
      mDxbar2.conjugate()*gD.adjoint()).trace();
   TRACE_STRUCT.tracegDAdjgDconjmq2gDAdjgD = (gD*gD.adjoint()*mq2.conjugate()*
      gD*gD.adjoint()).trace();
   TRACE_STRUCT.tracegDconjmDxbar2AdjgDgDAdjgD = (gD*mDxbar2.conjugate()*
      gD.adjoint()*gD*gD.adjoint()).trace();
   TRACE_STRUCT.tracehEmH1I2AdjhEhEAdjhE = (hE*mH1I2*hE.adjoint()*hE*hE.adjoint
      ()).trace();
   TRACE_STRUCT.tracehEAdjhEhEmH1I2AdjhE = (hE*hE.adjoint()*hE*mH1I2*hE.adjoint
      ()).trace();
   TRACE_STRUCT.tracehEAdjhEhEAdjhEme2 = (hE*hE.adjoint()*hE*hE.adjoint()*me2)
      .trace();
   TRACE_STRUCT.tracehEAdjhEme2hEAdjhE = (hE*hE.adjoint()*me2*hE*hE.adjoint())
      .trace();

   const auto QS = INPUT(QS);

   TRACE_STRUCT.Tr11 = 0.7745966692414834*g1*(-mHd2 - mHp2 + mHpbar2 + mHu2 + (
      md2).trace() - (mDx2).trace() + (mDxbar2).trace() + (me2).trace() - (mH1I2)
      .trace() + (mH2I2).trace() - (ml2).trace() + (mq2).trace() - 2*(mu2).trace()
      );
   TRACE_STRUCT.Tr14 = 0.15811388300841897*g1p*(-6*mHd2 + 4*mHp2 - 4*mHpbar2 -
      4*mHu2 + ms2*QS - msbar2*QS + 6*(md2).trace() - 6*(mDx2).trace() - 9*(
      mDxbar2).trace() + (me2).trace() - 6*(mH1I2).trace() - 4*(mH2I2).trace() + 4
      *(ml2).trace() + 6*(mq2).trace() + 5*(mSI2).trace() + 3*(mu2).trace());
   TRACE_STRUCT.Tr2U111 = 0.1*Sqr(g1)*(3*mHd2 + 3*mHp2 + 3*mHpbar2 + 3*mHu2 + 2
      *(md2).trace() + 2*(mDx2).trace() + 2*(mDxbar2).trace() + 6*(me2).trace() +
      3*(mH1I2).trace() + 3*(mH2I2).trace() + 3*(ml2).trace() + (mq2).trace() + 8*
      (mu2).trace());
   TRACE_STRUCT.Tr2U114 = 0.1224744871391589*g1*g1p*(3*mHd2 - 2*mHp2 - 2*
      mHpbar2 - 2*mHu2 + 2*(md2).trace() + 2*(mDx2).trace() - 3*(mDxbar2).trace()
      + (me2).trace() + 3*(mH1I2).trace() - 2*(mH2I2).trace() - 2*(ml2).trace() +
      (mq2).trace() - 2*(mu2).trace());
   TRACE_STRUCT.Tr31 = 0.006454972243679028*g1*(60*(mHd2 - mHu2)*AbsSqr(Lambdax
      ) + 60*(mHp2 - mHpbar2)*AbsSqr(SigmaL) - 18*mHd2*Sqr(g1) - 18*mHp2*Sqr(g1) +
      18*mHpbar2*Sqr(g1) + 18*mHu2*Sqr(g1) - 27*mHd2*Sqr(g1p) - 12*mHp2*Sqr(g1p)
      + 12*mHpbar2*Sqr(g1p) + 12*mHu2*Sqr(g1p) - 90*mHd2*Sqr(g2) - 90*mHp2*Sqr(g2)
      + 90*mHpbar2*Sqr(g2) + 90*mHu2*Sqr(g2) + 8*Sqr(g1)*(md2).trace() + 12*Sqr(
      g1p)*(md2).trace() + 160*Sqr(g3)*(md2).trace() - 8*Sqr(g1)*(mDx2).trace() -
      12*Sqr(g1p)*(mDx2).trace() - 160*Sqr(g3)*(mDx2).trace() + 8*Sqr(g1)*(mDxbar2
      ).trace() + 27*Sqr(g1p)*(mDxbar2).trace() + 160*Sqr(g3)*(mDxbar2).trace() +
      72*Sqr(g1)*(me2).trace() + 3*Sqr(g1p)*(me2).trace() - 18*Sqr(g1)*(mH1I2)
      .trace() - 27*Sqr(g1p)*(mH1I2).trace() - 90*Sqr(g2)*(mH1I2).trace() + 18*Sqr
      (g1)*(mH2I2).trace() + 12*Sqr(g1p)*(mH2I2).trace() + 90*Sqr(g2)*(mH2I2)
      .trace() - 18*Sqr(g1)*(ml2).trace() - 12*Sqr(g1p)*(ml2).trace() - 90*Sqr(g2)
      *(ml2).trace() + 2*Sqr(g1)*(mq2).trace() + 3*Sqr(g1p)*(mq2).trace() + 90*Sqr
      (g2)*(mq2).trace() + 160*Sqr(g3)*(mq2).trace() - 64*Sqr(g1)*(mu2).trace() -
      6*Sqr(g1p)*(mu2).trace() - 320*Sqr(g3)*(mu2).trace() + 60*mHd2*(fd*
      fd.adjoint()).trace() - 60*mHu2*(fu*fu.adjoint()).trace() + 180*mHp2*(gD*
      gD.adjoint()).trace() + 60*mHp2*(hE*hE.adjoint()).trace() + 180*mHd2*(Yd*
      Yd.adjoint()).trace() + 60*mHd2*(Ye*Ye.adjoint()).trace() - 180*mHu2*(Yu*
      Yu.adjoint()).trace() - 60*(fd*mH2I2.conjugate()*fd.adjoint()).trace() + 60*
      (fu*mH1I2.conjugate()*fu.adjoint()).trace() - 120*(gD*mDxbar2*gD.adjoint())
      .trace() - 60*(gD*gD.adjoint()*mq2).trace() - 120*(hE*hE.adjoint()*
      me2.conjugate()).trace() + 60*(hE*mH1I2.conjugate()*hE.adjoint()).trace() +
      60*(mDx2*Kappa*(Kappa).adjoint()).trace() - 60*(mDxbar2*(Kappa).adjoint()*
      Kappa).trace() - 60*(mH2I2*Lambda12*(Lambda12).adjoint()).trace() - 120*(Yd*
      Yd.adjoint()*md2.conjugate()).trace() - 60*(Yd*mq2.conjugate()*Yd.adjoint())
      .trace() - 120*(Ye*Ye.adjoint()*me2.conjugate()).trace() + 60*(Ye*
      ml2.conjugate()*Ye.adjoint()).trace() + 240*(Yu*Yu.adjoint()*mu2.conjugate()
      ).trace() - 60*(Yu*mq2.conjugate()*Yu.adjoint()).trace() + 60*(Lambda12*
      mH1I2.conjugate()*(Lambda12).adjoint()).trace());
   TRACE_STRUCT.Tr22 = 0.5*(mHd2 + mHp2 + mHpbar2 + mHu2 + (mH1I2).trace() + (
      mH2I2).trace() + (ml2).trace() + 3*(mq2).trace());
   TRACE_STRUCT.Tr23 = 0.5*((md2).trace() + (mDx2).trace() + (mDxbar2).trace()
      + 2*(mq2).trace() + (mu2).trace());
   TRACE_STRUCT.Tr2U141 = 0.1224744871391589*g1*g1p*(3*mHd2 - 2*mHp2 - 2*
      mHpbar2 - 2*mHu2 + 2*(md2).trace() + 2*(mDx2).trace() - 3*(mDxbar2).trace()
      + (me2).trace() + 3*(mH1I2).trace() - 2*(mH2I2).trace() - 2*(ml2).trace() +
      (mq2).trace() - 2*(mu2).trace());
   TRACE_STRUCT.Tr2U144 = 0.025*Sqr(g1p)*(18*mHd2 + 8*mHp2 + 8*mHpbar2 + 8*mHu2
      + ms2*Sqr(QS) + msbar2*Sqr(QS) + 12*(md2).trace() + 12*(mDx2).trace() + 27*
      (mDxbar2).trace() + (me2).trace() + 18*(mH1I2).trace() + 8*(mH2I2).trace() +
      8*(ml2).trace() + 6*(mq2).trace() + 25*(mSI2).trace() + 3*(mu2).trace());
   TRACE_STRUCT.Tr34 = -0.003952847075210475*g1p*(-40*(3*mHd2 + 2*mHu2 - ms2*QS
      )*AbsSqr(Lambdax) + 20*(ms2 - msbar2)*QS*AbsSqr(Sigmax) + 80*mHp2*AbsSqr(
      SigmaL) - 80*mHpbar2*AbsSqr(SigmaL) + 36*mHd2*Sqr(g1) - 24*mHp2*Sqr(g1) + 24
      *mHpbar2*Sqr(g1) + 24*mHu2*Sqr(g1) + 54*mHd2*Sqr(g1p) - 16*mHp2*Sqr(g1p) +
      16*mHpbar2*Sqr(g1p) + 16*mHu2*Sqr(g1p) - ms2*Power(QS,3)*Sqr(g1p) + msbar2*
      Power(QS,3)*Sqr(g1p) + 180*mHd2*Sqr(g2) - 120*mHp2*Sqr(g2) + 120*mHpbar2*Sqr
      (g2) + 120*mHu2*Sqr(g2) - 16*Sqr(g1)*(md2).trace() - 24*Sqr(g1p)*(md2).trace
      () - 320*Sqr(g3)*(md2).trace() + 16*Sqr(g1)*(mDx2).trace() + 24*Sqr(g1p)*(
      mDx2).trace() + 320*Sqr(g3)*(mDx2).trace() + 24*Sqr(g1)*(mDxbar2).trace() +
      81*Sqr(g1p)*(mDxbar2).trace() + 480*Sqr(g3)*(mDxbar2).trace() - 24*Sqr(g1)*(
      me2).trace() - Sqr(g1p)*(me2).trace() + 36*Sqr(g1)*(mH1I2).trace() + 54*Sqr(
      g1p)*(mH1I2).trace() + 180*Sqr(g2)*(mH1I2).trace() + 24*Sqr(g1)*(mH2I2)
      .trace() + 16*Sqr(g1p)*(mH2I2).trace() + 120*Sqr(g2)*(mH2I2).trace() - 24*
      Sqr(g1)*(ml2).trace() - 16*Sqr(g1p)*(ml2).trace() - 120*Sqr(g2)*(ml2).trace(
      ) - 4*Sqr(g1)*(mq2).trace() - 6*Sqr(g1p)*(mq2).trace() - 180*Sqr(g2)*(mq2)
      .trace() - 320*Sqr(g3)*(mq2).trace() - 125*Sqr(g1p)*(mSI2).trace() - 32*Sqr(
      g1)*(mu2).trace() - 3*Sqr(g1p)*(mu2).trace() - 160*Sqr(g3)*(mu2).trace() -
      120*mHd2*(fd*fd.adjoint()).trace() - 80*mHu2*(fu*fu.adjoint()).trace() + 240
      *mHp2*(gD*gD.adjoint()).trace() + 80*mHp2*(hE*hE.adjoint()).trace() - 360*
      mHd2*(Yd*Yd.adjoint()).trace() - 120*mHd2*(Ye*Ye.adjoint()).trace() - 240*
      mHu2*(Yu*Yu.adjoint()).trace() + 60*ms2*QS*(Kappa*(Kappa).adjoint()).trace()
      + 40*ms2*QS*(Lambda12*(Lambda12).adjoint()).trace() + 200*(fd*fd.adjoint()*
      mSI2).trace() - 80*(fd*mH2I2.conjugate()*fd.adjoint()).trace() + 200*(fu*
      fu.adjoint()*mSI2).trace() - 120*(fu*mH1I2.conjugate()*fu.adjoint()).trace()
      - 360*(gD*mDxbar2*gD.adjoint()).trace() + 120*(gD*gD.adjoint()*mq2).trace()
      + 40*(hE*hE.adjoint()*me2.conjugate()).trace() - 120*(hE*mH1I2.conjugate()*
      hE.adjoint()).trace() - 120*(mDx2*Kappa*(Kappa).adjoint()).trace() - 180*(
      mDxbar2*(Kappa).adjoint()*Kappa).trace() - 80*(mH2I2*Lambda12*(Lambda12)
      .adjoint()).trace() + 240*(Yd*Yd.adjoint()*md2.conjugate()).trace() + 120*(
      Yd*mq2.conjugate()*Yd.adjoint()).trace() + 40*(Ye*Ye.adjoint()*me2.conjugate
      ()).trace() + 80*(Ye*ml2.conjugate()*Ye.adjoint()).trace() + 120*(Yu*
      Yu.adjoint()*mu2.conjugate()).trace() + 120*(Yu*mq2.conjugate()*Yu.adjoint()
      ).trace() - 120*(Lambda12*mH1I2.conjugate()*(Lambda12).adjoint()).trace());

}

std::ostream& operator<<(std::ostream& ostr, const NE6SSM_soft_parameters& soft_pars)
{
   soft_pars.print(std::cout);
   return ostr;
}

} // namespace flexiblesusy
