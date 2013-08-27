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

SuperpotentialParameterRules::usage;
SusyBreakingParameterRules::usage;
ParameterRules::usage;
ParametrizeSuperpotentialCoupling::usage;
ParametrizeSusyBreakingCoupling::usage;
ParametrizeCoupling::usage;
HasIndicesQ::usage;
UpdateCouplingDimensions::usage;
CouplingDimensions::usage;

Begin["`Private`"]

SuperpotentialParameterRules[parameters_, convertedSuperpotential_] :=
    ParametrizationRule[
	#, ParametrizeSuperpotentialCoupling[#, convertedSuperpotential]]& /@
	parameters;

SusyBreakingParameterRules[parameters_, convertedSoft_] :=
    ParametrizationRule[
	#, ParametrizeSusyBreakingCoupling[#, convertedSoft]]& /@
	parameters;

ParameterRules[parameters_] :=
    ParametrizationRule[#, ParametrizeCoupling[#]]& /@ parameters;

ParametrizationRule[couplingHead_[__]?HasIndicesQ, parametrization_] :=
    couplingHead -> parametrization;

ParametrizationRule[coupling_, parametrization_] :=
    coupling -> parametrization;

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

ParametrizeSuperpotentialCoupling[coupling_?HasIndicesQ, superpotential_] :=
    ParametrizeSuperpotentialCoupling[
	coupling, superpotential, CouplingDimensions[Head[coupling]]];

ParametrizeSuperpotentialCoupling[coupling_, _] :=
    ParametrizeCoupling[coupling];

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

ParametrizeSusyBreakingCoupling[coupling_?HasIndicesQ, lagSoft_] :=
    ParametrizeSusyBreakingCoupling[
	coupling, lagSoft, CouplingDimensions[Head[coupling]]];

ParametrizeSusyBreakingCoupling[coupling_, _] := ParametrizeCoupling[coupling];

ParametrizeCoupling[couplingHead_[__]?HasIndicesQ] := Module[{
	dimensions = CouplingDimensions[couplingHead]
    },
    Map[If[LatticeRealQ[#], Re[#], Re[#] + I Im[#]] &,
	TableCoupling[couplingHead, dimensions], {Length[dimensions]}]
];

ParametrizeCoupling[coupling_] := Re[coupling] /; LatticeRealQ[coupling];

ParametrizeCoupling[coupling_] := Re[coupling] + I Im[coupling];

Parametrize[couplingHead_, dimensions_, redundancies_] :=
    ReduceParameters[Realize[couplingHead, dimensions], redundancies];

Realize[couplingHead_, dimensions_] :=
    Map[Re[#] + I Im[#] &,
	TableCoupling[couplingHead, dimensions], {Length[dimensions]}];

TableCoupling[couplingHead_, dimensions_] := Module[{
	loopArgs,
	entry,
	i
    },
    loopArgs = MapIndexed[{i@@#2, #1}&, dimensions];
    entry = couplingHead @@ loopArgs[[All, 1]];
    Table @@ Prepend[loopArgs, entry]
];

(*
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

PositionOfFirstNonzero[{z___?PossibleZeroQ, x_ /; !PossibleZeroQ[x], ___}] :=
    Length[{z}] + 1;
*)

ReduceParameters[parametrizedIndexedCoupling_, redundancies_] := Module[{
	realVariables = RealVariables[parametrizedIndexedCoupling],
	equations = Flatten[UnrollIndexedRule[
	    #, Dimensions[parametrizedIndexedCoupling]]& /@
	    redundancies] /. Rule :> Equal,
	reductionRules
    },
    reductionRules = Reduce[equations, realVariables] /.
	And -> List /. Equal -> Rule;
    parametrizedIndexedCoupling /. reductionRules
];

ReduceParameters[parametrizedIndexedCoupling_, {}] :=
    parametrizedIndexedCoupling;

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

HasIndicesQ[couplingHead_[__]] :=
    CouplingDimensions[couplingHead] =!= Undefined &&
    CouplingDimensions[couplingHead] =!= {};

HasIndicesQ[_] := False;

(* SARAH`getDimParameters[T] === {3, 3} *)

UpdateCouplingDimensions[] := (

DownValues[CouplingDimensions] = DownValues[SARAH`getDimParameters] /.
    SARAH`getDimParameters -> CouplingDimensions;

CouplingDimensions[couplingHead_] := Module[{
	dims,
	dimensionsList
    },
    dimensionsList = Cases[SARAH`parameters, {couplingHead, _, dims_} -> dims];
    If[dimensionsList === {}, Undefined, First[dimensionsList]]
];

);

UpdateCouplingDimensions[];

End[] (* `Private` *)

EndPackage[]
