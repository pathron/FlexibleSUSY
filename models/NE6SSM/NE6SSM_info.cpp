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

// File generated at Tue 8 Jul 2014 14:47:11

#include "NE6SSM_info.hpp"

#include <iostream>

namespace flexiblesusy {

namespace NE6SSM_info {
   const unsigned particle_multiplicities[NUMBER_OF_PARTICLES] = {1, 3, 1, 1, 1
      , 6, 3, 6, 6, 6, 5, 5, 2, 8, 2, 3, 3, 3, 3, 7, 4, 2, 7, 2, 2, 2, 1, 1, 1};

   const char* particle_names[NUMBER_OF_PARTICLES] = {"Glu", "Fv", "ChaP", "VZ"
      , "VZp", "Sd", "Sv", "Su", "Se", "SDX", "hh", "Ah", "Hpm", "Chi", "Cha",
      "Fe", "Fd", "Fu", "FDX", "SHI0", "SHIPM", "ChaI", "ChiI", "SHp0", "SHpp",
      "ChiP", "VG", "VP", "VWm"};

   const char* particle_latex_names[NUMBER_OF_PARTICLES] = {   "\\tilde{g}",
      "\\nu", "\\tilde{\\chi}^{'-}", "Z", "{Z'}", "\\tilde{d}", "\\tilde{\\nu}",
      "\\tilde{u}", "\\tilde{e}", "\\tilde{x}", "h", "A^0", "H^-",
      "\\tilde{\\chi}^0", "\\tilde{\\chi}^-", "e", "d", "u", "x", "h^{0,Inert}",
      "h^{-,Inert}", "\\tilde{\\chi}^{-,Inert}", "\\tilde{\\chi}^{0,Inert}",
      "H^{'0}", "H^{'-}", "\\tilde{\\chi}^{'0}", "g", "\\gamma", "W^-"};

   const char* parameter_names[NUMBER_OF_PARAMETERS] = {"Yd(0,0)", "Yd(0,1)",
      "Yd(0,2)", "Yd(1,0)", "Yd(1,1)", "Yd(1,2)", "Yd(2,0)", "Yd(2,1)", "Yd(2,2)",
      "hE(0,0)", "hE(0,1)", "hE(1,0)", "hE(1,1)", "hE(2,0)", "hE(2,1)", "Ye(0,0)"
      , "Ye(0,1)", "Ye(0,2)", "Ye(1,0)", "Ye(1,1)", "Ye(1,2)", "Ye(2,0)",
      "Ye(2,1)", "Ye(2,2)", "SigmaL", "KappaPr", "Sigmax", "gD(0,0)", "gD(0,1)",
      "gD(0,2)", "gD(1,0)", "gD(1,1)", "gD(1,2)", "gD(2,0)", "gD(2,1)", "gD(2,2)",
      "Kappa(0,0)", "Kappa(0,1)", "Kappa(0,2)", "Kappa(1,0)", "Kappa(1,1)",
      "Kappa(1,2)", "Kappa(2,0)", "Kappa(2,1)", "Kappa(2,2)", "Lambda12(0,0)",
      "Lambda12(0,1)", "Lambda12(1,0)", "Lambda12(1,1)", "Lambdax", "fu(0,0)",
      "fu(0,1)", "fu(1,0)", "fu(1,1)", "fu(2,0)", "fu(2,1)", "fd(0,0)", "fd(0,1)",
      "fd(1,0)", "fd(1,1)", "fd(2,0)", "fd(2,1)", "Yu(0,0)", "Yu(0,1)", "Yu(0,2)"
      , "Yu(1,0)", "Yu(1,1)", "Yu(1,2)", "Yu(2,0)", "Yu(2,1)", "Yu(2,2)", "MuPr",
      "MuPhi", "XiF", "g1", "g2", "g3", "g1p", "vd", "vu", "vs", "vsb", "vphi",
      "TYd(0,0)", "TYd(0,1)", "TYd(0,2)", "TYd(1,0)", "TYd(1,1)", "TYd(1,2)",
      "TYd(2,0)", "TYd(2,1)", "TYd(2,2)", "ThE(0,0)", "ThE(0,1)", "ThE(1,0)",
      "ThE(1,1)", "ThE(2,0)", "ThE(2,1)", "TYe(0,0)", "TYe(0,1)", "TYe(0,2)",
      "TYe(1,0)", "TYe(1,1)", "TYe(1,2)", "TYe(2,0)", "TYe(2,1)", "TYe(2,2)",
      "TSigmaL", "TKappaPr", "TSigmax", "TgD(0,0)", "TgD(0,1)", "TgD(0,2)",
      "TgD(1,0)", "TgD(1,1)", "TgD(1,2)", "TgD(2,0)", "TgD(2,1)", "TgD(2,2)",
      "TKappa(0,0)", "TKappa(0,1)", "TKappa(0,2)", "TKappa(1,0)", "TKappa(1,1)",
      "TKappa(1,2)", "TKappa(2,0)", "TKappa(2,1)", "TKappa(2,2)", "TLambda12(0,0)"
      , "TLambda12(0,1)", "TLambda12(1,0)", "TLambda12(1,1)", "TLambdax",
      "Tfu(0,0)", "Tfu(0,1)", "Tfu(1,0)", "Tfu(1,1)", "Tfu(2,0)", "Tfu(2,1)",
      "Tfd(0,0)", "Tfd(0,1)", "Tfd(1,0)", "Tfd(1,1)", "Tfd(2,0)", "Tfd(2,1)",
      "TYu(0,0)", "TYu(0,1)", "TYu(0,2)", "TYu(1,0)", "TYu(1,1)", "TYu(1,2)",
      "TYu(2,0)", "TYu(2,1)", "TYu(2,2)", "BMuPr", "BMuPhi", "LXiF", "mq2(0,0)",
      "mq2(0,1)", "mq2(0,2)", "mq2(1,0)", "mq2(1,1)", "mq2(1,2)", "mq2(2,0)",
      "mq2(2,1)", "mq2(2,2)", "ml2(0,0)", "ml2(0,1)", "ml2(0,2)", "ml2(1,0)",
      "ml2(1,1)", "ml2(1,2)", "ml2(2,0)", "ml2(2,1)", "ml2(2,2)", "mHd2", "mHu2",
      "md2(0,0)", "md2(0,1)", "md2(0,2)", "md2(1,0)", "md2(1,1)", "md2(1,2)",
      "md2(2,0)", "md2(2,1)", "md2(2,2)", "mu2(0,0)", "mu2(0,1)", "mu2(0,2)",
      "mu2(1,0)", "mu2(1,1)", "mu2(1,2)", "mu2(2,0)", "mu2(2,1)", "mu2(2,2)",
      "me2(0,0)", "me2(0,1)", "me2(0,2)", "me2(1,0)", "me2(1,1)", "me2(1,2)",
      "me2(2,0)", "me2(2,1)", "me2(2,2)", "ms2", "msbar2", "mH1I2(0,0)",
      "mH1I2(0,1)", "mH1I2(1,0)", "mH1I2(1,1)", "mH2I2(0,0)", "mH2I2(0,1)",
      "mH2I2(1,0)", "mH2I2(1,1)", "mSI2(0,0)", "mSI2(0,1)", "mSI2(0,2)",
      "mSI2(1,0)", "mSI2(1,1)", "mSI2(1,2)", "mSI2(2,0)", "mSI2(2,1)", "mSI2(2,2)"
      , "mDx2(0,0)", "mDx2(0,1)", "mDx2(0,2)", "mDx2(1,0)", "mDx2(1,1)",
      "mDx2(1,2)", "mDx2(2,0)", "mDx2(2,1)", "mDx2(2,2)", "mDxbar2(0,0)",
      "mDxbar2(0,1)", "mDxbar2(0,2)", "mDxbar2(1,0)", "mDxbar2(1,1)",
      "mDxbar2(1,2)", "mDxbar2(2,0)", "mDxbar2(2,1)", "mDxbar2(2,2)", "mHp2",
      "mHpbar2", "mphi2", "MassB", "MassWB", "MassG", "MassBp"};

   const char* model_name = "NE6SSM";
   const bool is_low_energy_model = true;

void print(std::ostream& ostr)
{
   ostr
      << "Model information\n"
      << "=================\n"
      << "Model name:            " << model_name << '\n'
      << "Is a low-energy model: "
      << (is_low_energy_model ? "true" : "false") << '\n'
      << "Number of multiplets:  " << NUMBER_OF_PARTICLES << '\n'
      << "Number of parameters:  " << NUMBER_OF_PARAMETERS << '\n'
      ;

   ostr << "\n"
      "Multiplets:            ";
   for (unsigned i = 0; i < NUMBER_OF_PARTICLES; i++) {
      ostr << particle_names[i]
           << '[' << particle_multiplicities[i] << ']';
      if (i + 1 < NUMBER_OF_PARTICLES)
         ostr << ", ";
   }

   ostr << "\n\n"
      "Parameters:            ";
   for (unsigned i = 0; i < NUMBER_OF_PARAMETERS; i++) {
      ostr << parameter_names[i];
      if (i + 1 < NUMBER_OF_PARAMETERS)
         ostr << ", ";
   }
   ostr << '\n';
}

} // namespace NE6SSM_info

} // namespace flexiblesusy

