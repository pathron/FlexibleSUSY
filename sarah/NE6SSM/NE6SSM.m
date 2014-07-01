Off[General::spell]

Model`Name = "NE6SSM";
Model`NameLaTeX ="NE6SSM";
Model`Authors = "P.Athron";
Model`Date = "2013-11-10";

(*-------------------------------------------*)
(*   Particle Content*)
(*-------------------------------------------*)

(* Global symmetries *)

Global[[1]] = {Z[2],RParity};
RpM = {-1,-1,1};
RpP = {1,1,-1};

(* Vector Superfields *)

Gauge[[1]]={B,   U[1], hypercharge, g1,False,RpM};
Gauge[[2]]={WB, SU[2], left,        g2,True, RpM};
Gauge[[3]]={G,  SU[3], color,       g3,False,RpM};
Gauge[[4]]={Bp,  U[1], Ncharge,    g1p,False,RpM};

(* Chiral Superfields *)

SuperFields[[1]] = {q, 3, {uL,  dL},     1/6, 2, 3, 1, RpM};  
SuperFields[[2]] = {l, 3, {vL,  eL},    -1/2, 2, 1, 2, RpM};
SuperFields[[3]] = {Hd,1, {Hd0, Hdm},   -1/2, 2, 1, -3, RpP};
SuperFields[[4]] = {Hu,1, {Hup, Hu0},    1/2, 2, 1, -2, RpP};

SuperFields[[5]] = {d, 3, conj[dR],    1/3, 1, -3, 2, RpM};
SuperFields[[6]] = {u, 3, conj[uR],   -2/3, 1, -3, 1, RpM};
SuperFields[[7]] = {e, 3, conj[eR],      1, 1,  1, 1, RpM};
SuperFields[[8]] = {s, 1, sR,     0, 1,  1, QS, RpP};
SuperFields[[9]] = {sbar, 1, sbarR,    0, 1,  1, -QS, RpP};
 
(* These come from the 2&-plets but the third  gen is at GUT scale *)
 SuperFields[[10]] = {H1I, 2, {H1I0, H1Im},  -1/2, 2, 1, -3, RpP};
 SuperFields[[11]] = {H2I, 2, {H2Ip, H2I0},   1/2, 2, 1, -2, RpP};
 SuperFields[[12]] = {NS, 3, NSIR,    0, 1,  1, 5, RpP}; 

SuperFields[[13]] = {Dx, 3, DxL,  -1/3, 1, 3, -2, RpP};
SuperFields[[14]] = {Dxbar, 3, conj[DxbarR],  1/3, 1, -3, -3, RpP};

SuperFields[[15]] = {Hp, 1, {Hpd0, Hpdm},  -1/2, 2,  1, 2, RpP};
SuperFields[[16]] = {Hpbar, 1, {Hpup, Hpu0}, 1/2, 2,  1, -2, RpP};
SuperFields[[17]] = {phi, 1, phiR, 0, 1, 1, 0, RpP};
NoU1Mixing=True;
AddMixedSofts = False;

(*------------------------------------------------------*)
(*Z2H exact Superpotential *)
(*------------------------------------------------------*)

SuperPotential = Yu u.q.Hu - Yd d.q.Hd - Ye e.l.Hd + \[Lambda] s.Hu.Hd  + \[Kappa] s.Dx.Dxbar + \[Mu]Pr Hpbar.Hp - \[Sigma] phi.s.sbar + \[Kappa]Pr/3 phi.phi.phi + MuPhi/2 phi.phi + \[Xi]F phi + fu NS.H1I.Hu + fd NS.Hd.H2I + gD q.Hp.Dxbar + hE e.H1I.Hp +  \[Sigma]L phi.Hp.Hpbar;

(*-------------------------------------------*)
(* Integrate Out or Delete Particles         *)
(*-------------------------------------------*)

IntegrateOut={};
DeleteParticles={};


(*----------------------------------------------*)
(*   ROTATIONS                                  *)
(*----------------------------------------------*)

NameOfStates={GaugeES, EWSB};

(* ----- Before EWSB ----- *)

DEFINITION[GaugeES][DiracSpinors]={
  Bino ->{fB, conj[fB]},
  Wino -> {fWB, conj[fWB]},
  Glu -> {fG, conj[fG]},
  (*  H0 -> {FHd0, conj[FHu0]},
   HC -> {FHdm, conj[FHup]}, *)
  H01 -> {FHd0, 0},
  H02 -> {0, conj[FHu0]},
  HC1 -> {FHdm, 0},
  HC2 -> {0, conj[FHup]},
  Fd1 -> {FdL, 0},
  Fd2 -> {0, FdR},
  Fu1 -> {FuL, 0},
  Fu2 -> {0, FuR},
  Fe1 -> {FeL, 0},
  Fe2 -> {0, FeR},
  Fv -> {FvL,0},
  FS1 -> {FsR,0},
  FS2 -> {0,conj[FsR]},
  FSbar1 -> {FsbarR,0},
  FSbar2 -> {0,conj[FsbarR]},
  Fphi1 -> {FphiR,0},
  Fphi2 -> {0,conj[FphiR]},
  FBp -> {fBp,conj[fBp]},
  (* 
   Removing inerts from spectrum
   H0I1 -> {FH1I0, 0},
   H0I2 -> {0, conj[FH2I0]},
   HCI1 -> {FH1Im, 0},
   HCI2 -> {0, conj[FH2Ip]},
   FSI1 -> {FsIR, 0},
   FSI2 -> {0, conj[FsIR]},
   *)
  FDx1 -> {FDxL, 0},
  FDx2 -> {0, FDxbarR},
  Hp01 -> {FHpd0, 0},
  Hp02 -> {0, conj[FHpu0]},
  HpC1 -> {FHpdm, 0} ,
  HpC2 -> {0, conj[FHpup]} 
};


(* ----- After EWSB ----- *)


(* Gauge Sector *)

DEFINITION[EWSB][GaugeSector] =
{ 
   {{VB,VWB[3],VBp},{VP,VZ,VZp},ZZ},
  {{VWB[1],VWB[2]},{VWm,conj[VWm]},ZW},
  {{fWB[1],fWB[2],fWB[3]},{fWm,fWp,fW0},ZfW}
};      
          	

(* ----- VEVs ---- *)

DEFINITION[EWSB][VEVs]= 
  { {SHd0, {vd, 1/Sqrt[2]}, {sigmad, \[ImaginaryI]/Sqrt[2]},{phid,1/Sqrt[2]}},
    {SHu0, {vu, 1/Sqrt[2]}, {sigmau, \[ImaginaryI]/Sqrt[2]},{phiu,1/Sqrt[2]}},
    {SsR,  {vs, 1/Sqrt[2]}, {sigmaS, \[ImaginaryI]/Sqrt[2]},{phiS,1/Sqrt[2]}},
    {SsbarR,  {vsb, 1/Sqrt[2]}, {sigmaSbar, \[ImaginaryI]/Sqrt[2]},{phiSbar, 1/Sqrt[2]}},
    {SphiR,  {vphi, 1/Sqrt[2]}, {sigmaPhi, \[ImaginaryI]/Sqrt[2]},{phiPhi, 1/Sqrt[2]}}
};


 
(* ---- Mixings ---- *)

DEFINITION[EWSB][MatterSector]= 
   {    
      {{SdL, SdR}, {Sd, ZD}},
      {{SvL}, {Sv, ZV}},
      {{SuL, SuR}, {Su, ZU}},
      {{SeL, SeR}, {Se, ZE}},
      {{SDxL, SDxbarR}, {SDX, ZDX}},
      {{phid, phiu, phiS, phiSbar, phiPhi}, {hh, ZH}},
      {{sigmad, sigmau, sigmaS, sigmaSbar, sigmaPhi}, {Ah, ZA}},
      {{SHdm,conj[SHup]},{Hpm,ZP}},
      {{fB, fW0, FHd0, FHu0, FsR, FsbarR, FphiR, fBp}, {L0, ZN}}, 
      {{{fWm, FHdm}, {fWp, FHup}}, {{Lm,UM}, {Lp,UP}}}, 
      {{{FeL},{conj[FeR]}},{{FEL,ZEL},{FER,ZER}}},
      {{{FdL},{conj[FdR]}},{{FDL,ZDL},{FDR,ZDR}}},
      {{{FuL},{conj[FuR]}},{{FUL,ZUL},{FUR,ZUR}}},
      {{{FDxL},{conj[FDxbarR]}},{{FDXL,ZDXL},{FDXR,ZDXR}}}, 
      (* Removing decoupled inerts from spectrum
   {{SH1I0,conj[SH2I0]},{SHI0,UHI0}},
   {{SH1Im,conj[SH2Ip]},{SHIp,UHIp}},
   {{{FH1Im},{FH2Ip}},{{LmI,ZMI},{LpI,ZPI}}},
   {{FH1I0,FH2I0},{L0I,ZNI}},
   {{SsIR},{SS0I,ZSSI}},
       *)
      {{SHpd0,conj[SHpu0]},{SHp0,UHp0}},
      {{SHpdm,conj[SHpup]},{SHpp,UHpp}},
      {{FHpd0,FHpu0},{L0p,ZNp}}
}; 
       
DEFINITION[EWSB][Phases]= 
{    {fG, PhaseGlu}
}; 

	
	
DEFINITION[EWSB][DiracSpinors]={
 Fd -> {FDL, conj[FDR]},
 Fe -> {FEL, conj[FER]},
 Fu -> {FUL, conj[FUR]},
 Fv -> {FvL, 0},
 Chi -> {L0, conj[L0]},
 Cha -> {Lm, conj[Lp]},
 Glu -> {fG, conj[fG]},
 (* 
  removing decoupled inerts from spectrum
  ChiI -> {L0I, conj[L0I]},
  ChaI -> {LmI, conj[LpI]},
  *)
 ChiP -> {L0p, conj[L0p]},
 ChaP -> {FHpdm, conj[FHpup]}, 
 FDX -> {FDXL, conj[FDXR]}
};	
