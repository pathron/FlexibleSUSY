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

BeginPackage["Parametrization`", {"SARAH`", "IndexStructure`"}]

ParametrizeSuperpotentialCoupling::usage;
ParametrizeSusyBreakingCoupling::usage;
ParametrizeCoupling::usage;

Begin["`Private`"]

ParametrizeSuperpotentialCoupling[coupling_, superpotential_, dimensions_] :=
Module[{
	couplingPattern = CouplingPattern[coupling],
	redundancies
    },
    redundancies =
	RedundancyList[couplingPattern,
		       RelevantTerms[couplingPattern, superpotential]];
    Parametrize[Head[coupling], dimensions, redundancies]
];

ParametrizeSuperpotentialCoupling[coupling_, superpotential_] :=
    ParametrizeSuperpotentialCoupling[
	coupling, superpotential, SARAH`getDimParameters[Head[coupling]]];

ParametrizeSuperpotentialCoupling[coupling_, _] :=
    ParametrizeCoupling[coupling] /;
	SARAH`getDimParameters[Head[coupling]] === {};

ParametrizeSusyBreakingCoupling[coupling_, lagSoft_, dimensions_] := Module[{
	couplingPattern = CouplingPattern[coupling],
	relevantTerms,
	redundancies,
	hermiticity
    },
    relevantTerms = RelevantTerms[couplingPattern, lagSoft];
    redundancies =
	RedundancyList[couplingPattern,
		       TermsHolomorphicIn[couplingPattern, relevantTerms]];
    hermiticity = HermiticityConditions[couplingPattern, relevantTerms];
    Parametrize[Head[coupling], dimensions, Join[redundancies, hermiticity]]
];

ParametrizeSusyBreakingCoupling[coupling_, lagSoft_] :=
    ParametrizeSusyBreakingCoupling[
	coupling, lagSoft, SARAH`getDimParameters[Head[coupling]]];

ParametrizeSusyBreakingCoupling[coupling_, _] :=
    ParametrizeCoupling[coupling] /;
	SARAH`getDimParameters[Head[coupling]] === {};

ParametrizeCoupling[coupling_] := Re[coupling] /; LatticeRealQ[coupling];

ParametrizeCoupling[coupling_] := Re[coupling] + I Im[coupling];

Parametrize[couplingHead_, dimensions_, redundancies_] :=
    ReduceParameters[Realize[couplingHead, dimensions], redundancies];

Realize[couplingHead_, dimensions_] := Module[{
	loopArgs,
	entry,
	i
    },
    loopArgs = MapIndexed[{i@@#2, #1}&, dimensions];
    entry = couplingHead @@ loopArgs[[All, 1]];
    Table @@ Prepend[loopArgs, Re[entry] + I Im[entry]]
];

ReduceParameters[parametrizedIndexedCoupling_, redundancies_] := Module[{
	realVariables = RealVariables[parametrizedIndexedCoupling],
	equations = Cases[Flatten[UnrollIndexedRule[
		#, Dimensions[parametrizedIndexedCoupling]]& /@
	    redundancies] /. Rule :> Equal, _Equal],
	coefficientArrays,
	constraintMatrix,
	dependents,
	reductionRules
    },
    coefficientArrays = CoefficientArrays[equations, realVariables];
    Assert[MatchQ[Normal[coefficientArrays], {{___?PossibleZeroQ},_}]];
    constraintMatrix = RowReduce[coefficientArrays[[2]]];
    dependents = realVariables[[PositionOfFirstNonzero /@
	Cases[constraintMatrix, Except[{___?PossibleZeroQ}]]]];
    {reductionRules} = Solve[equations, dependents];
    parametrizedIndexedCoupling /. reductionRules
];

ReduceParameters[parametrizedIndexedCoupling_, {}] :=
    parametrizedIndexedCoupling;

PositionOfFirstNonzero[{z___?PossibleZeroQ, x_ /; !PossibleZeroQ[x], ___}] :=
    Length[{z}] + 1;

UnrollIndexedRule[rule:(indexedCoupling_ -> rhs_), dimensions_] := Module[{
	rulesOnParts = ((# /@ rule)& /@ {Re, Im}),
	loopArgs
    },
    loopArgs = Transpose[{List@@indexedCoupling, dimensions}];
    Flatten[Table @@ Prepend[loopArgs, rulesOnParts]]
];

RealVariables[parametrizedIndexedCoupling_] :=
    Variables[parametrizedIndexedCoupling];

LatticeRealQ[z_] := MemberQ[SARAH`realVar, z];

End[] (* `Private` *)

EndPackage[]
