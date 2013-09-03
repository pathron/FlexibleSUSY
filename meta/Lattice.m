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
    "CConversion`",
    "TextFormatting`",
    "WriteOut`"}]

WriteRGECode::usage;
ParametrizeBetaFunctions::usage;

Begin["`Private`"]

Format[x, CForm] := Format["x", OutputForm];

Format[  x[i_], CForm] := Format[  "x["<>ToString[CForm[i]]<>"]", OutputForm];

Format[ dx[i_], CForm] := Format[ "dx["<>ToString[CForm[i]]<>"]", OutputForm];

Format[ddx[i_,j_], CForm] := Format["ddx(" <> ToString[CForm[i]] <> "," <>
				    ToString[CForm[j]] <> ")", OutputForm];

Format[a, CForm] := Format["a", OutputForm];

Format[drv[ap_, p_], CForm] :=
    Format["d" <> ToString[CForm[HoldForm[ap]]] <>
	   "d" <> ToString[CForm[HoldForm[p]]], OutputForm];

Unprotect[Re, Im];

(* CHECK: interference with two-scale method *)

Format[Re[z_], CForm] := Format["RE" <> ToValidCSymbolString[z], OutputForm];
Format[Im[z_], CForm] := Format["IM" <> ToValidCSymbolString[z], OutputForm];

Protect[Re, Im];

WriteRGECode[
    sarahAbbrs_List, betaFunctions_List, anomDims_List,
    gaugeCouplingRules_, otherParameterRules_, templateRules_, files_List] :=
Module[{
	parameterRules = Join[gaugeCouplingRules, otherParameterRules],
	gaugeCouplings = RealVariables[gaugeCouplingRules],
	betaFunctionRules, betaFunctionDerivRules,
	abbrRules, abbrDerivRules,
	parameters, enumRules, enumParameters,
	abbrDecls, abbrDefs,
	betaDecls, betaDefs,
	p
    },
    parameters = RealVariables[parameterRules];
    enumRules = EnumRules[parameters];
    enumParameters = EnumParameters[enumRules];
    {betaFunctionRules, abbrRules} =
	ParametrizeBetaFunctions[betaFunctions, sarahAbbrs, parameterRules];
    abbrDerivRules = DifferentiateRules[abbrRules, parameters, abbrRules];
    {abbrDecls, abbrDefs} = ToCCode[
       RuleToC[#, enumRules]& /@ Flatten[{abbrRules, abbrDerivRules}]];
    betaFunctionRules = Transpose[
	ScaleByA[#, gaugeCouplings]& /@
	SortBy[betaFunctionRules,
	       (# /. {{BETA[_Integer, p_] -> _, ___}, ___} :>
		Position[parameters, p])&]];
    {betaDecls, betaDefs} = ToCCode@Flatten[
       BetaFunctionRulesToC[betaFunctionRules, enumRules, abbrRules]];
    WriteOut`ReplaceInFiles[files, Join[templateRules, {
	"@enumParameters@"  -> WrapLines[IndentText[enumParameters,2],79,"  "],
	"@abbrDecls@"	    -> WrapLines[IndentText[abbrDecls,2],79,"  "],
	"@dxddxDecls@"      -> WrapLines[IndentText[betaDecls,2],79,"  "],
	"@abbrDefs@"	    -> WrapLines[abbrDefs,79,"  "],
	"@dxddxDefs@"       -> WrapLines[betaDefs,79,"  "]
    }]];
];

EnumRules[parameters_List] := MapIndexed[
    #1 -> "l" <> ToString@First[#2] <> ToString[#1, CForm]&, parameters];

EnumParameters[enumRules_List] :=
    StringJoin["enum : size_t { l0t, ", {Last[#], ", "}& /@ enumRules,
	       "eftWidth };"];

ScaleByA[b:{{(BETA[1, _] -> _)..}, {(BETA[_Integer, _] -> _)...}...},
	 gaugeCouplings_] :=
    Map[ScaleByA[#, gaugeCouplings]&, b, {2}]

ScaleByA[b:BETA[1, p_] -> rhs_, gaugeCouplings_] := (b -> rhs) /;
    MemberQ[gaugeCouplings, p];

ScaleByA[b:BETA[1, _] -> rhs_, _] := b -> a rhs;

ScaleByA[b:BETA[_Integer, _] -> rhs_, _] := b -> a rhs;

RealVariables[parameterRules_] := Module[{
	rvs = Variables[parameterRules[[All,2]]]
    },
    Assert[Complement[rvs, Union[rvs]] === {}];
    SortBy[rvs, Position[Flatten@parameterRules[[All,2]], #]&]
];

DifferentiateRules[rules_, parameters_, abbrRules_] :=
    DifferentiateRule[#, parameters, abbrRules]& /@ rules;

DifferentiateRule[lhs_ -> rhs_, parameters_, abbrRules_] :=
    DeleteCases[
	(Differentiate[lhs, #, abbrRules] ->
	 Differentiate[rhs, #, abbrRules])& /@
	parameters,
	_?PossibleZeroQ -> _?PossibleZeroQ];

ToCCode[cfxns_] := Module[{
	returnType,
	name,
	args,
	attributes,
	body
    },
    StringJoin /@
    Transpose[
	({{ReturnType, " ", Name, Args, {" ATTR(",Attributes,")"}, ";\n"},
	  {ReturnType, " CLASSNAME::", Name, Args, "\n", Body, "\n"}} /.
	 List@@# /. {___, Attributes, ___} -> {})& /@
	Flatten[cfxns]]
];

RuleToC[lhs_ -> rhs_, enumRules_] :=
CFxn[
    ReturnType -> "double",
    Name -> RValueToCFormString[lhs],
    Args -> "(const Eigen::VectorXd& x) const",
    Attributes -> "pure",
    Body -> "{\n" <>
    "  return " <> RValueToCFormString@ToCExp[rhs, x, enumRules] <> ";\n" <>
    "}\n"
];

BetaFunctionRulesToC[betanLrules_, enumRules_, abbrRules_] := {
CFxn[
    ReturnType -> "void",
    Name -> "dx",
    Args -> "(double a, const Eigen::VectorXd& x, Eigen::VectorXd& dx, size_t nloops) const",
    Body -> StringJoin["{\n",
    "  dx.setZero();\n",
    "  dx[l0t] = 1;\n",
    MapIndexed[{
    "\n  if (nloops < ", ToString@First[#2], ") return;\n",
    {"  ", BetaFunctionRuleToCStmt[#, enumRules]}& /@
	Flatten[#1]}&, betanLrules],
    "}\n"]],
CFxn[
    ReturnType -> "void",
    Name -> "ddx",
    Args -> "(double a, const Eigen::VectorXd& x, Eigen::MatrixXd& ddx, size_t nloops) const",
    Body -> StringJoin["{\n",
    "  ddx.setZero();\n",
    MapIndexed[{
    "\n  if (nloops < ", ToString@First[#2], ") return;\n",
    BetaFunctionRuleToDerivCStmt[#, enumRules, abbrRules]& /@ Flatten[#1]}&,
    betanLrules],
    "}\n"]
]};

BetaFunctionRuleToCStmt[BETA[1, p:(Re|Im)[_]] -> rhs_, enumRules_] :=
    BetaFunctionRuleToAssignment[1, p, rhs, enumRules, "="];

BetaFunctionRuleToCStmt[BETA[level_Integer, p:(Re|Im)[_]] -> rhs_,
			     enumRules_] :=
    BetaFunctionRuleToAssignment[level, p, rhs, enumRules, "+="];

BetaFunctionRuleToAssignment[_Integer, _, rhs_?PossibleZeroQ, _, _] := {};

BetaFunctionRuleToAssignment[
    level_Integer, p_, rhs_, enumRules_, op_] :=
    RValueToCFormString[ToCExp[p, dx, enumRules]] <> " " <> op <> " " <>
    RValueToCFormString[CConversion`oneOver16PiSqr^level
			ToCExp[rhs, x, enumRules]] <> ";\n";

BetaFunctionRuleToDerivCStmt[
    BETA[1, p:(Re|Im)[_]] -> rhs_, enumRules_, abbrRules_] :=
    BetaFunctionRuleToAssignments[1, p, rhs, enumRules, abbrRules, "="];

BetaFunctionRuleToDerivCStmt[
    BETA[level_Integer, p:(Re|Im)[_]] -> rhs_, enumRules_, abbrRules_] :=
    BetaFunctionRuleToAssignments[level, p, rhs, enumRules, abbrRules, "+="];

BetaFunctionRuleToAssignments[
    level_Integer, p_, rhs_, enumRules_, abbrRules_, op_] :=
Module[{
	pidx = p /. enumRules
    },
    Module[{
	    q, qidx,
	    deriv
	},
	{q, qidx} = List @@ #;
	deriv = Differentiate[rhs, q, abbrRules];
	If[PossibleZeroQ[deriv], {},
	   {"  ddx(", qidx, ",", pidx, ") ", op, " ",
	    RValueToCFormString[CConversion`oneOver16PiSqr^level
				ToCExp[deriv, x, enumRules]],
	    ";\n"}]
    ]& /@ enumRules
];

ToCExp[parametrization_, array_Symbol, enumRules_] := parametrization /.
    d:drv[(Re|Im)[_], (Re|Im)[_]] :> Symbol[ToString[d, CForm]][x] /.
    ((First[#] -> array@Symbol[Last[#]])& /@ enumRules) /.
    ap:(Re|Im)[abbr_Symbol] :> ap[x];

Differentiate[exp_, x_, abbrRules_] :=
    D[exp, x, NonConstants -> abbrRules[[All,1]]] /.
    HoldPattern@D[f_, y_, ___] -> drv[f, y] /.
    drv[f_, y_] /; IndependentQ[f, y, abbrRules] -> 0;

IndependentQ[ap_, x_, abbrRules_] :=
    PossibleZeroQ@Simplify@D[ap //. abbrRules, x];

ParametrizeBetaFunctions[betaFunctions_List, sarahAbbrs_, parameterRules_] :=
Module[{
	convertedBetaFunctions = betaFunctions /.
	    sarahOperatorReplacementRules,
	convertedSarahAbbrs = Flatten[sarahAbbrs /.
	    sarahOperatorReplacementRules, 1],
	nestedTraceRules, traceRules,
	sarahAbbrRules,
	nBetaFunctions
    },
    nestedTraceRules = ParametrizeTraceAbbrs[
	{convertedBetaFunctions, convertedSarahAbbrs}];
    traceRules = Flatten[nestedTraceRules];
    convertedBetaFunctions = convertedBetaFunctions /. traceRules;
    sarahAbbrRules = ParametrizeSarahAbbrs[
	convertedSarahAbbrs, Join[parameterRules, traceRules]];
    nBetaFunctions = Length[convertedBetaFunctions];
    {MapIndexed[
	(WriteString["stdout",
		     "[", First[#2], "/", nBetaFunctions, "] expanding "];
	 ParametrizeBetaFunction[
	     #1, Join[parameterRules, traceRules, sarahAbbrRules[[All,1]]]])&,
	convertedBetaFunctions],
     Flatten[{ParametrizeTraces[nestedTraceRules, parameterRules],
	      sarahAbbrRules[[All,2]]}]}
];

ParametrizeBetaFunction[
    BetaFunction`BetaFunction[name_, _, betanLs_List],
    partRules_] :=
Module[{
	result
    },
    result =
       MapIndexed[
	   Flatten@ParametrizeBetanLRules[name, #1, First[#2], partRules]&,
	   betanLs];
    WriteString["stdout", "done\n"];
    result
];

ParametrizeBetanLRules[name_, betanL_, n_, partRules_] := Module[{
	equations
    },
    WriteString["stdout", "BETA[",n ,", ", name, "]..."];
    equations = ParametrizeBetanL[name, betanL, n, partRules];
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

ParametrizeSarahAbbrs[sarahAbbrRules:{{_,_}...}, partRules_] :=
    SarahAbbrToRule /@
    ReleaseHold[Hold[sarahAbbrRules] /. partRules //. matrixOpRules]

SarahAbbrToRule[{abbr_, rhs_}] :=
    {abbr -> Re[abbr], {Re[abbr] -> rhs}} /; PossibleZeroQ@Simplify@Im[rhs];

SarahAbbrToRule[{ab_, rhs_}] :=
    {ab -> Re[ab] + I Im[ab], {Re[ab] -> Re[rhs], Im[ab] -> Im[rhs]}};

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
    Or @@ Table[b === RotateLeft[a, i], {i, 0, Length[a]-1}];

matrixOpRules := {
    SARAH`MatMul :> Dot,
    Parametrization`trp :> Transpose,
    Parametrization`cnj :> Conjugate,
    Parametrization`adj :> ConjugateTranspose,
    SARAH`trace[m__] :> Tr[Dot[m]]
};

End[] (* `Private` *)

EndPackage[]
