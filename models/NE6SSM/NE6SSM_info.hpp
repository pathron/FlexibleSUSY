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

#ifndef NE6SSM_INFO_H
#define NE6SSM_INFO_H

#include <iosfwd>

namespace flexiblesusy {

namespace NE6SSM_info {
   enum Particles : unsigned {Glu, Fv, ChaP, VZ, VZp, Sd, Sv, Su, Se, SDX, hh,
      Ah, Hpm, Chi, Cha, Fe, Fd, Fu, FDX, SHI0, SHIPM, ChaI, ChiI, SHp0, SHpp,
      ChiP, VG, VP, VWm, NUMBER_OF_PARTICLES};

   enum Parameters : unsigned {Yd00, Yd01, Yd02, Yd10, Yd11, Yd12, Yd20, Yd21,
      Yd22, hE00, hE01, hE10, hE11, hE20, hE21, Ye00, Ye01, Ye02, Ye10, Ye11, Ye12
      , Ye20, Ye21, Ye22, SigmaL, KappaPr, Sigmax, gD00, gD01, gD02, gD10, gD11,
      gD12, gD20, gD21, gD22, Kappa00, Kappa01, Kappa02, Kappa10, Kappa11, Kappa12
      , Kappa20, Kappa21, Kappa22, Lambda1200, Lambda1201, Lambda1210, Lambda1211,
      Lambdax, fu00, fu01, fu10, fu11, fu20, fu21, fd00, fd01, fd10, fd11, fd20,
      fd21, Yu00, Yu01, Yu02, Yu10, Yu11, Yu12, Yu20, Yu21, Yu22, MuPr, MuPhi, XiF
      , g1, g2, g3, g1p, vd, vu, vs, vsb, vphi, TYd00, TYd01, TYd02, TYd10, TYd11,
      TYd12, TYd20, TYd21, TYd22, ThE00, ThE01, ThE10, ThE11, ThE20, ThE21, TYe00
      , TYe01, TYe02, TYe10, TYe11, TYe12, TYe20, TYe21, TYe22, TSigmaL, TKappaPr,
      TSigmax, TgD00, TgD01, TgD02, TgD10, TgD11, TgD12, TgD20, TgD21, TgD22,
      TKappa00, TKappa01, TKappa02, TKappa10, TKappa11, TKappa12, TKappa20,
      TKappa21, TKappa22, TLambda1200, TLambda1201, TLambda1210, TLambda1211,
      TLambdax, Tfu00, Tfu01, Tfu10, Tfu11, Tfu20, Tfu21, Tfd00, Tfd01, Tfd10,
      Tfd11, Tfd20, Tfd21, TYu00, TYu01, TYu02, TYu10, TYu11, TYu12, TYu20, TYu21,
      TYu22, BMuPr, BMuPhi, LXiF, mq200, mq201, mq202, mq210, mq211, mq212, mq220
      , mq221, mq222, ml200, ml201, ml202, ml210, ml211, ml212, ml220, ml221,
      ml222, mHd2, mHu2, md200, md201, md202, md210, md211, md212, md220, md221,
      md222, mu200, mu201, mu202, mu210, mu211, mu212, mu220, mu221, mu222, me200,
      me201, me202, me210, me211, me212, me220, me221, me222, ms2, msbar2,
      mH1I200, mH1I201, mH1I210, mH1I211, mH2I200, mH2I201, mH2I210, mH2I211,
      mSI200, mSI201, mSI202, mSI210, mSI211, mSI212, mSI220, mSI221, mSI222,
      mDx200, mDx201, mDx202, mDx210, mDx211, mDx212, mDx220, mDx221, mDx222,
      mDxbar200, mDxbar201, mDxbar202, mDxbar210, mDxbar211, mDxbar212, mDxbar220,
      mDxbar221, mDxbar222, mHp2, mHpbar2, mphi2, MassB, MassWB, MassG, MassBp,
      NUMBER_OF_PARAMETERS};

   extern const unsigned particle_multiplicities[NUMBER_OF_PARTICLES];
   extern const char* particle_names[NUMBER_OF_PARTICLES];
   extern const char* particle_latex_names[NUMBER_OF_PARTICLES];
   extern const char* parameter_names[NUMBER_OF_PARAMETERS];
   extern const char* model_name;
   extern const bool is_low_energy_model;

   void print(std::ostream&);
}

} // namespace flexiblesusy

#endif
