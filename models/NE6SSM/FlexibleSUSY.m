
FSModelName = "NE6SSM";

(* CE6SSM input parameters *)

MINPAR = { {3, TanBeta}
         };

EXTPAR = { 
   {65, vSInput},
   {63, muPrimeInput},
   {64, BmuPrimeInput},
   {72, QS}        
         };

DefaultParameterPoint = {
   {QS, 5}, 
   {muPrimeInput, 400},
   {BmuPrimeInput, 40000},
   {vSInput, 100},
   {TanBeta, 10}
};

EWSBOutputParameters = {mHd2, mHu2, ms2, msbar2, mphi2};

SUSYScale = 1000;

SUSYScaleFirstGuess =  1000; 

SUSYScaleInput = {
   {B[\[Mu]Pr], BmuPrimeInput},
   {\[Mu]Pr, muPrimeInput},
   {vs, vSInput}
};

LowScale = SM[MZ];

LowScaleFirstGuess = SM[MZ];

LowScaleInput={
   {Yu, Automatic},
   {Yd, Automatic},
   {Ye, Automatic},
   {vd, 2 MZDRbar / Sqrt[GUTNormalization[g1]^2 g1^2 + g2^2] Cos[ArcTan[TanBeta]]},
   {vu, 2 MZDRbar / Sqrt[GUTNormalization[g1]^2 g1^2 + g2^2] Sin[ArcTan[TanBeta]]}
};

InitialGuessAtLowScale = {
   {vd, SM[vev] Cos[ArcTan[TanBeta]]},
   {vu, SM[vev] Sin[ArcTan[TanBeta]]},
   {vs, vSInput},
   {Yu, Automatic},
   {Yd, Automatic},
   {Ye, Automatic},
   {mHd2, SM[MZ]^2},
   {mHu2, SM[MZ]^2},
   {ms2, SM[MZ]^2},
   {B[\[Mu]Pr], SM[MZ]^2},
   {\[Mu]Pr, SM[MZ]}
};


OnlyLowEnergyFlexibleSUSY = True;
