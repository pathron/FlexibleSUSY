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

BeginPackage["Lattice`", {
    "SARAH`",
    "BetaFunction`",
    "Parametrization`",
    "Traces`",
    "CConversion`"}]

ParametrizeBetaFunctions::usage;

Begin["`Private`"]

ParametrizeBetaFunctions[betaFunctions_List, parameterRules_] := Module[{
	convertedBetaFunctions = betaFunctions /.
	    sarahOperatorReplacementRules,
	nestedTraceRules, traceRules,
	nBetaFunctions
    },
    nestedTraceRules = ParametrizeTraceAbbrs[
	GetAllBetaFunctions /@ convertedBetaFunctions];
    traceRules = Flatten[nestedTraceRules];
    convertedBetaFunctions = convertedBetaFunctions /. traceRules;
    nBetaFunctions = Length[convertedBetaFunctions];
    {MapIndexed[
	(WriteString["stdout",
		     "[", First[#2], "/", nBetaFunctions, "] expanding"];
	 ParametrizeBetaFunction[#1, Join[parameterRules, traceRules]])&,
	convertedBetaFunctions],
     ParametrizeTraces[nestedTraceRules, parameterRules]}
];

ParametrizeBetaFunction[
    BetaFunction`BetaFunction[name_, _, {beta1L_, beta2L_}],
    partRules_] :=
Module[{
	tmp
    },
    Flatten /@ {
	WriteString["stdout", " BETA[1, ", name, "]"];
	ParametrizeBetanLRules[name, beta1L, 1, partRules],
	WriteString["stdout", ", BETA[2, ", name, "]..."];
	tmp = ParametrizeBetanLRules[name, beta2L, 2, partRules];
	WriteString["stdout", " done\n"];
	tmp}
];

ParametrizeBetanLRules[name_, betanL_, n_, partRules_] := Module[{
	equations = ParametrizeBetanL[name, betanL, n, partRules]
    },
    EquationsToRules /@ equations
]

EquationsToRules[equations:HoldPattern@And[(BETA[_Integer, _] == _)..]] :=
    List@@equations /. Equal -> Rule;

EquationsToRules[(lhs:BETA[_Integer, _]) == rhs_] := {lhs -> rhs};

EquationsToRules[True] := {};

EquationsToRules[args__] :=
    (Print["Lattice`EquationsToRules[",args,"] failed."]; Abort[]);

ParametrizeBetanL[name_[i_,j_]?HasIndicesQ, betanL_, n_, partRules_] :=
    ParametrizeMatrixBetanL[name[i,j], betanL, n, partRules];

ParametrizeBetanL[name_[d__]?HasIndicesQ, betanL_, n_, partRules_] :=
    ParametrizeIndexedBetanL[name[d], betanL, n, partRules];

ParametrizeBetanL[name_, betanL_, n_, partRules_] := Module[{
	lBetanL, rBetanL,
	m
    },
    lBetanL = Betaize[n, Hold[name] /. partRules];
    rBetanL = Hold[betanL] /. partRules;
    ReduceBetaEquations[{#}]& /@
    SeparateParts[
	ReleaseHold[rBetanL - lBetanL //. matrixOpRules],
	partRules]
];

ParametrizeMatrixBetanL[name_[i_,j_]?HasIndicesQ, betanL_, n_, partRules_] :=
Module[{
	lBetanL, rBetanL,
	m
    },
    lBetanL = Betaize[n, Hold[name] /. partRules];
    rBetanL = Hold[betanL] /. KroneckerRule[name[i,j]] /. m_[i,j] :> m /.
       partRules;
    ReduceBetaEquations@Flatten[#]& /@
    SeparateParts[
	ReleaseHold[rBetanL - lBetanL //. matrixOpRules],
	partRules]
];

ParametrizeIndexedBetanL[name_[i__]?HasIndicesQ, betanL_, n_, partRules_] :=
Module[{
	dimensions = CouplingDimensions[name],
	lBetanL, rBetanL,
	loopArgs,
	m, l,
	unrollings
    },
    loopArgs = MapIndexed[{l@@#2, #1}&, dimensions];
    lBetanL = Betaize[n, Hold[name[i]] /. m_[i] :> m[[i]] /. partRules];
    rBetanL = Hold[betanL] /. KroneckerRule[name[i]] /. m_[i] :> m[[i]] /.
       partRules;
    (* TODO: unroll sum[]'s if SARAH`NoMatrixMultiplication -> True *)
    unrollings = Flatten[
	Table @@ Prepend[loopArgs, Thread[{i} -> loopArgs[[All, 1]]]],
	Length[dimensions]-1];
    ReduceBetaEquations@Flatten[#]& /@
    SeparateParts[
	ReleaseHold[rBetanL - lBetanL //. matrixOpRules /. #]& /@
	unrollings,
	partRules]
];

KroneckerRule[name_[i__]] := Module[{
	dimensions,
	d
    },
    With[{dimensions = CouplingDimensions[name]},
	Kronecker[d__] :> IdentityMatrix[
	    Flatten[Extract[dimensions, Position[{i}, #]]& /@ {d}]][d]]
];

ReduceBetaEquations[equations_] := Module[{
	variables =
	    Cases[equations, BETA[_Integer, (Re|Im)[__]], {0, Infinity}]
    },
    Reduce[# == 0& /@ equations, variables]
];

SeparateParts[z_, partRules_] := Module[{
	complexes = Union[Variables[partRules[[All, 2]]] /.
			  Re|Im -> Identity]
    },
    ComplexExpand[Through[{Re, Im}[z]], complexes]
];

Betaize[level_, parametrization_] :=
    parametrization /. {
	Re[z_] :> BETA[level, Re[z]],
	Im[z_] :> BETA[level, Im[z]]
    };

ParametrizeTraces[nestedTraceRules_List, parameterRules_] :=
    Flatten[ParametrizeTrace[#, parameterRules]& /@ nestedTraceRules]

ParametrizeTrace[{traces_Alternatives -> abbr_, ___}, parameterRules_] :=
    ParametrizeTrace[{First[traces] -> abbr}, parameterRules]

ParametrizeTrace[{trace_SARAH`trace -> Re[ab_] + I Im[ab_], Repeated[_,{0,1}]},
		 parameterRules_] :=
    Thread[{Re[ab], Im[ab]} ->
	   SeparateParts[
	       ReleaseHold[Hold[trace] /. parameterRules //. matrixOpRules],
	       parameterRules]];

ParametrizeTrace[{trace_SARAH`trace -> Re[ab_], Repeated[_,{0,1}]},
		 parameterRules_] :=
Module[{
	re, im
    },
    {re, im} =
	SeparateParts[
	    ReleaseHold[Hold[trace] /. parameterRules //. matrixOpRules],
	    parameterRules];
    Assert[PossibleZeroQ[im]];
    {Re[ab] -> re}
];

ParametrizeTrace[args__] :=
    (Print["Lattice`ParametrizeTrace[",args,"] failed."]; Abort[]);

ParametrizeTraceAbbrs[exp_] := Module[{
    	traces = Union@Flatten@Cases[exp, _SARAH`trace, {0, Infinity}],
	grouped
    },
    grouped =
	Gather[Gather[traces, TraceSameQ],
	       TraceSameQ[Parametrization`cnj@First[#1], First[#2]]&];
    ConjugateTraceAbbrRule /@
    Map[ParametrizeTraceAbbrRule, Map[TraceAbbrRule, grouped, {2}], {2}]
];

ConjugateTraceAbbrRule[rule:{_}] := rule;

ConjugateTraceAbbrRule[{a_ -> b_, c_ -> d_}] :=
    {a -> b, c -> Parametrization`cnj[b]};

ParametrizeTraceAbbrRule[traces_Alternatives -> abbr_] :=
    ParametrizeTraceAbbrRule[First[traces] -> abbr];

(* Q: can a trace also be purely imaginary? *)

ParametrizeTraceAbbrRule[trace_SARAH`trace?TraceRealQ -> abbr_] :=
    trace -> Re[abbr];

ParametrizeTraceAbbrRule[trace_SARAH`trace -> abbr_] :=
    trace -> Re[abbr] + I Im[abbr];

TraceAbbrRule[{trace_}] := trace -> CConversion`ToValidCSymbol[trace];

TraceAbbrRule[traces:{fst_,__}] :=
    Alternatives@@traces -> CConversion`ToValidCSymbol[fst];

TraceRealQ[trace_SARAH`trace] := TraceSameQ[trace, Parametrization`cnj[trace]];

TraceSameQ[SARAH`trace[a__], SARAH`trace[b__]] :=
    ListSameUptoRotationQ[{a}, {b}] ||
    ListSameUptoRotationQ[{a}, Parametrization`trp /@ Reverse[{b}]];

ListSameUptoRotationQ[a_List, b_List] :=
    Length[a] === Length[b] &&
    Or @@ (b === RotateLeft[a, #]& /@ Range[0, Length[a]-1]);

matrixOpRules := {
    SARAH`MatMul :> Dot,
    Parametrization`trp :> Transpose,
    Parametrization`cnj :> Conjugate,
    Parametrization`adj :> ConjugateTranspose,
    SARAH`trace[m__] :> Tr[Dot[m]]
};

End[] (* `Private` *)

EndPackage[]
