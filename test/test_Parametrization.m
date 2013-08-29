(* :Copyright:

   ====================================================================
   This file is part of FlexibleSUSY.

   FlexibleSUSY is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published
   by the Free Software Foundation, either version 3 of the License,
   or (at your option) any later version.

   FlexibleSUSY is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with FlexibleSUSY.  If not, see
   <http://www.gnu.org/licenses/>.
   ====================================================================

*)

Needs["TestSuite`", "TestSuite.m"];
Needs["Parametrization`", "Parametrization.m"];

workingDirectory = Directory[];
$sarahOutputDir = CreateDirectory[];
Print["Current working directory: ", workingDirectory];
Print["SARAH output directory: ", $sarahOutputDir];

Start["MSSM-RpV/LnV"];

On[Assert];

Print["testing EnforceCommonIndices[] ..."];

randomizeIndices[term_] := Module[{
	indices = Union@Flatten@Cases[term, _[i:{___}] :> i, {0, Infinity}]
    },
    term /. Thread[indices -> Module@@{indices, indices}]
];

convertedSoft = ConvertSarahTerms[
    Soft, {MassG, mHd2, B[\[Mu]], mu2[__], mq2[__], T[Yd][__], T[L1][__]}];

mu2Terms1 = RelevantTerms[mu2[__], convertedSoft];
mu2Terms2 = randomizeIndices[mu2Terms1];
mu2Terms3 = mu2Terms1/2 + mu2Terms2/2;
mu2Terms = Parametrization`Private`EnforceCommonIndices[mu2[__], mu2Terms3];

TestEquality[Length[mu2Terms3], 2];
TestEquality[2 First[mu2Terms3], mu2Terms];

mq2Terms1 = RelevantTerms[mq2[__], convertedSoft];
mq2Terms2 = randomizeIndices /@ mq2Terms1;
mq2Terms3 = Expand[mq2Terms1/2 + mq2Terms2/2];
mq2Terms = Parametrization`Private`EnforceCommonIndices[mq2[__], mq2Terms3];

TestEquality[Length[mq2Terms3], 4];
TestEquality[Length[mq2Terms], 2];

Print["testing HeriticityConditions[mu2[__],...] ..."];

mu2Terms = RelevantTerms[mu2[__], convertedSoft];
redundanciesMu2 =
    RedundancyList[mu2[__], TermsHolomorphicIn[mu2[__], mu2Terms]];
hermiticityMu2 = HermiticityConditions[mu2[__], mu2Terms];

TestEquality[redundanciesMu2, {}];
TestMatch[hermiticityMu2,
	  HoldPattern[{mu2[g2_, g1_] -> Parametrization`cnj[mu2[g1_, g2_]]}]];

Print["testing HeriticityConditions[mq2[__],...] ..."];

mq2Terms = RelevantTerms[mq2[__], convertedSoft];
redundanciesMq2 =
    RedundancyList[mq2[__], TermsHolomorphicIn[mq2[__], mq2Terms]];
hermiticityMq2 = HermiticityConditions[mq2[__], mq2Terms];

TestEquality[redundanciesMq2, {}];
TestMatch[hermiticityMq2,
	  HoldPattern[{mq2[g2_, g1_] -> Parametrization`cnj[mq2[g1_, g2_]]}]];

Print["testing Parametrize[mu2,...] ..."];

naiveMu2 = Parametrization`Private`Realize[mu2, {3, 3}];
parMu2 = Parametrization`Private`Parametrize[mu2, {3, 3}, hermiticityMu2];

TestEquality[Length[Parametrization`Private`RealVariables[naiveMu2]], 3 3 2];
TestEquality[Length[Parametrization`Private`RealVariables[parMu2]], 9];

Print["testing RedundancyList[T[L1],...] ..."];

TL1Terms = RelevantTerms[T[L1][__], convertedSoft];
redundanciesTL1 =
    RedundancyList[T[L1][__], TermsHolomorphicIn[T[L1][__], TL1Terms]];
hermiticityTL1 = HermiticityConditions[T[L1][__], TL1Terms];

TestMatch[redundanciesTL1,
	  HoldPattern[{T[L1][g2_, g1_, g3_] -> -T[L1][g1_, g2_, g3_]}]];
TestEquality[hermiticityTL1, {}];

Print["testing Parametrize[T[L1],...] ..."];

naiveTL1 = Parametrization`Private`Realize[T[L1], {3, 3, 3}];
parTL1 = Parametrization`Private`Parametrize[T[L1], {3, 3, 3}, redundanciesTL1];

TestEquality[Length[Parametrization`Private`RealVariables[naiveTL1]], 3 3 3 2];
TestEquality[Length[Parametrization`Private`RealVariables[parTL1]], 3 3 2];

Print["testing ParametrizeSusyBreakingCoupling[] ..."]

fxn := Parametrization`Private`ParametrizeSusyBreakingCoupling;

ComplexMatrix[name_, rows_, cols_] :=
    Table[Re[name[i,j]] + I Im[name[i,j]], {i, rows}, {j, cols}];

HermitianMatrix[name_, size_] := Table[
    Which[i < j, Re[name[i,j]] + I Im[name[i,j]],
	  i > j, Re[name[j,i]] - I Im[name[j,i]],
	  True , Re[name[i,j]]], {i, size}, {j, size}];

L1couplings[name_, size_] := Table[
    Which[i < j,   Re[name[i,j,k]] + I Im[name[i,j,k]],
	  i > j, - Re[name[j,i,k]] - I Im[name[j,i,k]],
	  True , 0], {i, size}, {j, size}, {k, size}];

TestEquality[fxn[MassG, convertedSoft], I Im[MassG] + Re[MassG]];
TestEquality[fxn[mHd2, convertedSoft], Re[mHd2]];
TestEquality[fxn[B[\[Mu]], convertedSoft], I Im[B[\[Mu]]] + Re[B[\[Mu]]]];
TestEquality[fxn[mu2[i1, i2], convertedSoft], HermitianMatrix[mu2, 3]];
TestEquality[fxn[mq2[i1, i2], convertedSoft], HermitianMatrix[mq2, 3]];
TestEquality[fxn[T[Yd][i1, i2], convertedSoft], ComplexMatrix[T[Yd], 3, 3]];
TestEquality[fxn[T[L1][i1, i2, i3], convertedSoft], L1couplings[T[L1], 3]];

Print["testing ParametrizeSuperpotentialCoupling[] ..."]

fxn := Parametrization`Private`ParametrizeSuperpotentialCoupling;

convertedW = ConvertSarahTerms[
    Superpotential, {\[Mu], Yd[__], T[L1][__]}];

TestEquality[fxn[\[Mu], convertedW], I Im[\[Mu]] + Re[\[Mu]]];
TestEquality[fxn[Yd[i1, i2], convertedW], ComplexMatrix[Yd, 3, 3]];
TestEquality[fxn[L1[i1, i2, i3], convertedW], L1couplings[L1, 3]];

DeleteDirectory[$sarahOutputDir, DeleteContents -> True];

PrintTestSummary[];
