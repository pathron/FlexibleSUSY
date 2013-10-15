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
    "TreeMasses`",
    "CConversion`",
    "TextFormatting`",
    "WriteOut`",
    "Makefile`"}]

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
    Format[DrvToCFormString[drv[ap, p]], OutputForm];

DrvToCFormString[drv[ap_, p_]] :=
    "d"<>ToString[CForm[HoldForm[ap]]] <> "d"<>ToString[CForm[HoldForm[p]]];

Format[Lattice`Private`Re[z_], CForm] :=
    Format["RE" <> ToValidCSymbolString[z], OutputForm];
Format[Lattice`Private`Im[z_], CForm] :=
    Format["IM" <> ToValidCSymbolString[z], OutputForm];

Format[Lattice`Private`M[f_], CForm] :=
    Format["M" <> ToValidCSymbolString[f], OutputForm];

Format[Lattice`Private`M2[f_], CForm] :=
    Format["M2" <> ToValidCSymbolString[f], OutputForm];

WriteRGECode[
    sarahAbbrs_List, betaFunctions_List, anomDims_List,
    fsMassMatrices_,
    gaugeCouplingRules_, otherParameterRules_, templateRules_,
    modelName_, templateDir_, outputDir_] :=

Block[{
	drv,
	ToEnumSymbol,
	DeclaredRealQ
    },
    Format[d:drv[_, _], CForm] := Format[DrvToCFormString[d], OutputForm];

Module[{
	parameterRules = Join[gaugeCouplingRules, otherParameterRules],
	gaugeCouplings = RealVariables[gaugeCouplingRules],
	betaFunctionRules, betaFunctionDerivRules,
	abbrRules, abbrDerivRules,
        trivialAbbrRules, nonTrivialAbbrRules,
	parameters, enumRules, enumParameters,
	abbrDecls, abbrDefs,
	betaDecls, betaDefs,
	defChunks, nDefChunks,
	replacementFiles, cFiles,
	betaCFile, betaCFiles,
	massMatrices = FixDiagonalization[fsMassMatrices] /.
	    sarahOperatorReplacementRules,
	eigenVarsDefs, eigenVarsStmts,
	dependenceNumDecls, dependenceNumDefs,
	p
    },
    parameters = RealVariables[parameterRules];
    enumRules = EnumRules[parameters];
    enumParameters = EnumParameters[enumRules];
    SetToEnumSymbol /@ enumRules;
    {betaFunctionRules, abbrRules} =
	ParametrizeBetaFunctions[betaFunctions, sarahAbbrs, parameterRules];
    DoneLn[
    abbrDerivRules = DifferentiateRules[abbrRules, parameters, abbrRules];
    {trivialAbbrRules, nonTrivialAbbrRules} =
	SeparateTrivialRules@Flatten[{abbrRules, abbrDerivRules}];
    {abbrDecls, abbrDefs} = CFxnsToCCode[
        AbbrRuleToC /@ nonTrivialAbbrRules, Global`$flexiblesusyCSrcChunkSize],
    "Differentiating abbreviations... "];
    betaFunctionRules = Transpose[
	ScaleByA[#, gaugeCouplings]& /@
	SortBy[betaFunctionRules,
	       (# /. {{BETA[_Integer, p_] -> _, ___}, ___} :>
		Position[parameters, p])&]];
    {betaDecls, betaDefs} = CFxnsToCCode[Flatten[
	BetaFunctionRulesToC[betaFunctionRules, enumRules, abbrRules]],
	Global`$flexiblesusyCSrcChunkSize];
    {dependenceNumDecls, dependenceNumDefs} = CFxnsToCCode[
	DepNumRuleToC /@ ParametrizeDependenceNums[
	    FindDependenceNums[], parameterRules]];

    {eigenVarDefs, eigenVarStmts} = CMassesToCCode[
	FSMassMatrixToC /@
	ParametrizeMasses[massMatrices, parameterRules]];

    replacementFiles = {
	{FileNameJoin[{templateDir, "lattice_info.hpp.in"}],
	 FileNameJoin[{outputDir, modelName <> "_lattice_info.hpp"}]},
	{FileNameJoin[{templateDir, "lattice_model.hpp.in"}],
	 FileNameJoin[{outputDir, modelName <> "_lattice_model.hpp"}]},
	{FileNameJoin[{templateDir, "lattice_model.cpp.in"}],
	 FileNameJoin[{outputDir, modelName <> "_lattice_model.cpp"}]},
	{FileNameJoin[{templateDir, "lattice_model_interactions.cpp.in"}],
	 FileNameJoin[{outputDir, modelName <> "_lattice_model_interactions.cpp"}]}};
    WriteOut`ReplaceInFiles[replacementFiles,
	Join[templateRules, {
	"@abbrDecls@"	    -> IndentText[abbrDecls, 2],
	"@betaDecls@"	    -> IndentText[betaDecls, 2],
	"@dependenceNumDecls@" -> IndentText[dependenceNumDecls, 4],
	"@dependenceNumDefs@"  -> WrapText[StringJoin@dependenceNumDefs],
	"@eigenVarDefs@"    -> IndentText[eigenVarDefs, 4],
	"@eigenVarStmts@"   -> WrapText[eigenVarStmts],
	"@enumParameters@"  -> WrapText@IndentText[enumParameters, 2],
	"@vertexDecls@"	    -> "",
	"@vertexDefs@"	    -> ""
    }]];
    defChunks = Join[abbrDefs, betaDefs];
    nDefChunks = Length[defChunks];
    betaCFiles = MapIndexed[(
	betaCFile = FileNameJoin[
	    {outputDir, modelName <> "_lattice_model_betafunctions_" <>
	     IntegerString[First[#2], 10, StringLength@ToString[nDefChunks]] <>
	     ".cpp"}];
	WriteOut`ReplaceInFiles[{
	    {FileNameJoin[{templateDir, "lattice_model_betafunctions.cpp.in"}],
	     betaCFile}},
	    Join[templateRules, {
		"@abbrBetaDefs@"    -> WrapText[#1]
	    }]];
	betaCFile)&,
    defChunks];
    cFiles = Join[
	Select[replacementFiles[[All,2]], StringMatchQ[#, ___ ~~ ".cpp"]&],
	betaCFiles];
    WriteMakefile[templateDir, outputDir, cFiles, templateRules]
]];

ParametrizeDependenceNums[depNums_List, parameterRules_] :=
    ParametrizeDependenceNum[#, parameterRules]& /@ depNums;

ParametrizeDependenceNum[lhs_ -> rhs_, parameterRules_] := Module[{
	expanded = (rhs /. parameterRules)
    },
    If[RealQ[expanded], DeclaredRealQ[lhs[]] = True];
    lhs -> expanded
];

ParametrizeMasses[massMatrices_, parameterRules_] := Module[{
	matrices = Cases[parameterRules, HoldPattern[_ -> _?MatrixQ]][[All,1]]
    },
    ReleaseHold[Hold[massMatrices] /.
	(m_[i__Integer] /; MemberQ[matrices, m]) :> m[[i]] /.
	parameterRules //. matrixOpRules]
];

CMassesToCCode[cmasses_] :=
    StringJoin /@ Transpose[
	({{EigenDef, "\n"}, {SetStmt, "\n"}} /. List@@#)& /@
	Flatten[cmasses]];

FSMassMatrixToC[FSMassMatrix[{m_?RealQ}, f_, _]] :=
    MassToC[m, f, "double"];

FSMassMatrixToC[FSMassMatrix[{m_}, f_, _]] :=
    MassToC[m, f, "std::complex<double>"];

FSMassMatrixToC[FSMassMatrix[m_?RealMatrixQ, f_, {u_Symbol, v_Symbol}]] :=
    SVDToC[m, f, u, v, "double"];

FSMassMatrixToC[FSMassMatrix[m_?MatrixQ, f_, {u_Symbol, v_Symbol}]] :=
    SVDToC[m, f, u, v, "std::complex<double>"];

FSMassMatrixToC[FSMassMatrix[m_?RealMatrixQ, f_, z_Symbol]] :=
    HermitianToC[m, f, z, "double"];

FSMassMatrixToC[FSMassMatrix[m_?MatrixQ, f_, z_Symbol]] :=
    HermitianToC[m, f, z, "std::complex<double>"];

MassToC[m_, f_, cType_] := Module[{
	ev = ToCMassName[f]
    },
    CMass[
	EigenDef -> cType <> " " <> ev <> ";",
	SetStmt -> "  " <> ev <> " = " <> CExpToCFormString@ToCExp[m, x] <> ";"
    ]
];

SVDToC[m_, f_, u_, u_, scalarType_] := Module[{
	d, ev
    },
    {d, d} = Dimensions[m];
    ev = ToCMassName[f];
    CMass[
	EigenDef ->
	    CEigenArrayType[d] <> " " <> ev <> ";\n" <>
	    CEigenMatrixType["std::complex<double>", d, d] <> " " <>
	    ToValidCSymbolString[u] <> ";",
	SetStmt ->
	    "  {\n" <>
	    CDefTmpMatrix[m, scalarType, "tmpMat"] <> "\n" <>
	    "    reorder_diagonalize_symmetric(tmpMat, " <> ev <> ", " <>
		ToValidCSymbolString[u] <> ");\n" <>
	    "    " <> ToValidCSymbolString[u] <> ".transposeInPlace();\n" <>
	    "  }"
    ]
];

SVDToC[m_, f_, u_, v_, scalarType_] := Module[{
	d1, d2, ds, ev
    },
    ds = Min[{d1, d2} = Dimensions[m]];
    ev = ToCMassName[f];
    CMass[
	EigenDef ->
	    CEigenArrayType[ds] <> " " <> ev <> ";\n" <>
	    CEigenMatrixType[scalarType, d1, d1] <> " " <>
	    ToValidCSymbolString[u] <> ";\n" <>
	    CEigenMatrixType[scalarType, d2, d2] <> " " <>
	    ToValidCSymbolString[v] <> ";",
	SetStmt ->
	    "  {\n" <>
	    CDefTmpMatrix[m, scalarType, "tmpMat"] <> "\n" <>
	    "    reorder_svd(tmpMat, " <> ev <> ", " <>
		ToValidCSymbolString[u] <> ", " <> ToValidCSymbolString[v] <>
		");\n" <>
	    "    " <> ToValidCSymbolString[u] <> ".transposeInPlace();\n" <>
	    "  }"
    ]
];

HermitianToC[m_, f_, z_, scalarType_] := Module[{
	d, ev
    },
    {d, d} = Dimensions[m];
    ev = ToCMassName[f];
    CMass[
	EigenDef ->
	    CEigenArrayType[d] <> " " <> ev <> ";\n" <>
	    CEigenMatrixType[scalarType, d, d] <> " " <>
	    ToValidCSymbolString[z] <> ";",
	SetStmt ->
	    "  {\n" <>
	    CDefTmpMatrix[m, scalarType, "tmpMat"] <> "\n" <>
	    "    diagonalize_hermitian(tmpMat, " <> ev <> ", " <>
		ToValidCSymbolString[z] <> ");\n" <>
	    "    " <> ToValidCSymbolString[z] <> ".adjointInPlace();\n" <>
	    "  }"
    ]
];

CEigenMatrixType[scalarType_String, d1_Integer, d2_Integer] :=
    "Eigen::Matrix<" <> scalarType <> ", " <>
    ToString[d1] <> ", " <> ToString[d2] <> ">";

CEigenArrayType[scalarType_String, len_Integer] :=
    "Eigen::Array<" <> scalarType <> ", " <> ToString[len] <> ", 1>";

CEigenArrayType[len_Integer] := CEigenArrayType["double", len];

ToCMassName[field_Symbol] := ToString @ CForm @ MassN[field];

MassN[field_ /; FieldMassDimension[field] === 3/2] := Lattice`Private`M[field];

MassN[field_ /; FieldMassDimension[field] === 1] := Lattice`Private`M2[field];

FieldMassDimension[_?IsFermion] := 3/2;

FieldMassDimension[_] := 1;

CDefTmpMatrix[m_, scalarType_, name_] := Module[{
	d1, d2, i1, i2,
	re = If[scalarType === "double", ReExpandCExp, Expand]
    },
    {d1, d2} = Dimensions[m];
    "    " <> CEigenMatrixType[scalarType, d1, d2] <> " " <> name <> ";\n" <>
    "    " <> name <> " <<\n" <>
    Riffle[Table[
	Riffle[Table[{
	    "    /*", ToString[i1 - 1], ",", ToString[i2 - 1], "*/ ",
	    CExpToCFormString @ re @ ToCExp[m[[i1,i2]], x]}, {i2, d2}], ",\n"],
	{i1, d1}], ",\n"] <> ";"
];

FixDiagonalization[fsMassMatrices_List] := FixDiagonalization/@fsMassMatrices;

(*
   Diagonalization conventions of SARAH:

      SVD: m = u^T diag v,
	where u and v are the 1st and the 2nd mixing matrices from
	DEFINITION[_][MatterSector]

      hermitian: m = z^dagger diag z

   According to the SARAH documentation, the specification of the
   neutraliino mass matrix is indistinguishable from that of a
   hermitian matrix even though it must be diagonalized as

      symmetric: m = u^T diag u

   This leads to the following amendment:
 *)
FixDiagonalization[FSMassMatrix[m_, f_, z_Symbol]?MajoranaMassMatrixQ] :=
    FSMassMatrix[m, f, {z, z}];

FixDiagonalization[m_FSMassMatrix] := m;

MajoranaMassMatrixQ[FSMassMatrix[_?MatrixQ, _, _]?MajoranaMassQ] := True;

MajoranaMassMatrixQ[_FSMassMatrix] := False;

MajoranaMassQ[FSMassMatrix[_, _?MajoranaQ, _]] := True;

MajoranaMassQ[_FSMassMatrix] := False;

MajoranaQ[field_] := MemberQ[SARAH`MajoranaPart, field];

RealQ[z_] := PossibleZeroQ[ConjugateExpand[z - Conjugate[z]]];

RealMatrixQ[m_?MatrixQ] := And @@ (RealQ /@ Flatten[m]);

RealMatrixQ[_] := False;

conjugateExpandDispatch = Dispatch[{
    (* Schwarz reflection principle? *)
    Conjugate[z:(_Plus|_Times|
		 _Power|
		 _Sin|_ArcSin|
		 _Cos|_ArcCos|
		 _Tan|_ArcTan)] :> Conjugate /@ z,
    Conjugate[z:(_SARAH`Mass|_SARAH`Mass2)] :> z,
    Conjugate[z_?DeclaredRealQ] :> z
}];

ConjugateExpand[z_] := z //. conjugateExpandDispatch;

WriteMakefile[templateDir_, outputDir_, cppFiles_, templateRules_] :=
    Makefile`ReplaceInMakefiles[{
	{FileNameJoin[{templateDir, "lattice.mk.in"}],
	 FileNameJoin[{outputDir, "lattice.mk"}]}},
	cppFiles, templateRules];

EnumRules[parameters_List] := MapIndexed[
    #1 -> "l" <> ToString@First[#2] <> ToString[ToCExp[#1], CForm]&,
    parameters];

EnumParameters[enumRules_List] :=
    StringJoin["enum : size_t { l0t, ", {Last[#], ", "}& /@ enumRules,
	       "eftWidth };"];

SetToEnumSymbol[parameter_ -> enum_String] :=
    ToEnumSymbol[ToCExp[parameter]] = Symbol[enum];

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
    SelfApplyTrivialRules @
    Flatten[DifferentiateRule[#, parameters, abbrRules]& /@ rules]

DifferentiateRule[lhs_ -> rhs_, parameters_, abbrRules_] :=
    (Differentiate[lhs, #, abbrRules] -> Differentiate[rhs, #, abbrRules])& /@
    parameters;

SelfApplyTrivialRules[rules_] := FixedPoint[RewriteTrivialRules, rules];

RewriteTrivialRules[rules_] := Module[{
	trivialRules, nonTrivialRules
    },
    {trivialRules, nonTrivialRules} = SeparateTrivialRules[rules];
    SetRule /@ trivialRules;
    nonTrivialRules
];

SetRule[lhs_ -> rhs_] := lhs = rhs;

SeparateTrivialRules[rules_] := Flatten /@
    Last@Reap[Sow[#, NumericQ@Expand@Last[#]]& /@ rules, {True, False}];

CFxnsToCCode[cfxns_, chunkSize_:Infinity] := Module[{
	decls, defs
    },
    {decls, defs} = Transpose[
	({{ReturnType, " ", Name, Args, {" ATTR(",Attributes,")"}, ";\n"},
	  {ReturnType, " ", Scope, Name, Args, "\n", Body, "\n"}} /.
	 List@@# /. {Scope -> "CLASSNAME::", {___, Attributes, ___} -> {}})& /@
	Flatten[cfxns]];
    {StringJoin[decls], StringGroup[defs, chunkSize]}
];

StringGroup[strings_List, chunkSize_] := Module[{
	flattened = Flatten[strings],
	size = 0
    },
    StringJoin /@ Last@Reap[
	(Sow[#, Quotient[size, chunkSize]]; size += StringLength[#])& /@
	flattened]
];

DepNumRuleToC[lhs_ -> rhs_] :=
CFxn[
    ReturnType -> If[RealQ[rhs], "double", "std::complex<double>"],
    Scope -> "CLASSNAME::Interactions::",
    Name -> CExpToCFormString@ToCExp[lhs],
    Args -> "() const",
    Attributes -> "pure",
    Body -> "{\n" <>
    "  return " <> CExpToCFormString@ToCExp[rhs, x] <> ";\n" <>
    "}\n"
];

AbbrRuleToC[lhs_ -> rhs_] :=
CFxn[
    ReturnType -> "double",
    Name -> CExpToCFormString@ToCExp[lhs],
    Args -> "(const Eigen::VectorXd& x) const",
    Attributes -> "pure",
    Body -> "{\n" <>
    "  return " <> CExpToCFormString@ToCExp[rhs, x] <> ";\n" <>
    "}\n"
];

BetaFunctionRulesToC[betanLRules_, enumRules_, abbrRules_] := Flatten[{
Reap[
    CFxn[
	ReturnType -> "void",
	Name -> "dx",
	Args -> "(double a, const Eigen::VectorXd& x, Eigen::VectorXd& dx, size_t nloops) const",
	Body -> StringJoin["{\n",
	"  dx.setZero();\n",
	"  dx[l0t] = 1;\n",
	MapIndexed[{
	"\n  if (nloops < ", ToString@First[#2], ") return;\n",
	Module[{flattened = Flatten[#1], nRules, name},
	nRules = Length[flattened];
	MapIndexed[(
	WriteString["stdout",
		    "[",First[#2],"/",nRules,"] ","BETA"@@First[#1],":"];
	name = "d" <> CExpToCFormString@ToCExp@Last@First[#1] <> "_" <>
	       ToString@First@First[#1] <> "loop";
	Sow[CFxn[
	    ReturnType -> "void",
	    Name -> name,
	    Args -> "(double a, const Eigen::VectorXd& x, Eigen::VectorXd& dx) const",
	    Body -> StringJoin["{\n",
	    "  ", BetaFunctionRuleToCStmt[#1],
	    "}\n"]]
	];
	{"  ", name, "(a, x, dx);\n"})&,
	flattened]]}&, betanLRules],
	"}\n"]
    ]
],
Reap[
    CFxn[
	ReturnType -> "void",
	Name -> "ddx",
	Args -> "(double a, const Eigen::VectorXd& x, Eigen::MatrixXd& ddx, size_t nloops) const",
	Body -> StringJoin["{\n",
	"  ddx.setZero();\n",
	MapIndexed[{
	"\n  if (nloops < ", ToString@First[#2], ") return;\n",
	Module[{flattened = Flatten[#1], nRules, name},
	nRules = Length[flattened];
	MapIndexed[(
	name = "dd" <> CExpToCFormString@ToCExp@Last@First[#1] <> "_" <>
	ToString@First@First[#1] <> "loop";
	DoneLn[Sow[CFxn[
	    ReturnType -> "void",
	    Name -> name,
	    Args -> "(double a, const Eigen::VectorXd& x, Eigen::MatrixXd& ddx) const",
	    Body -> StringJoin["{\n",
	    BetaFunctionRuleToDerivCStmt[#1, enumRules, abbrRules],
	    "}\n"]]],
	    "[",First[#2],"/",nRules,"] ", "D[BETA"@@First[#1], "]... "];
	{"  ", name, "(a, x, ddx);\n"})&,
	flattened]]}&, betanLRules],
	"}\n"]
    ]
]}];

BetaFunctionRuleToCStmt[BETA[1, p:(Re|Im)[_]] -> rhs_] :=
    BetaFunctionRuleToAssignment[1, p, rhs, "="];

BetaFunctionRuleToCStmt[BETA[level_Integer, p:(Re|Im)[_]] -> rhs_] :=
    BetaFunctionRuleToAssignment[level, p, rhs, "+="];

BetaFunctionRuleToAssignment[_Integer, _, rhs_, _, _, _] := {} /;
    Expand[rhs] === 0;

BetaFunctionRuleToAssignment[level_Integer, p_, rhs_, op_] :=
    CExpToCFormString[ToCExp[p, dx]] <> " " <> op <> " " <>
    CExpToCFormString[CConversion`oneOver16PiSqr^level
			ToCExp[rhs, x]] <> ";\n";

BetaFunctionRuleToAssignment[level_Integer, p_, rhs_, op_] := Module[{
	rhsCExp = Done[ToCExp[rhs, x], " translating to CExp... "]
    },
    DoneLn[CExpToCFormString[ToCExp[p, dx]] <> " " <> op <> " " <>
	   CExpToCFormString[CConversion`oneOver16PiSqr^level rhsCExp] <>
	   ";\n",
	   " to C... "]
];

BetaFunctionRuleToDerivCStmt[BETA[1, p:(Re|Im)[_]] -> rhs_,
			     enumRules_, abbrRules_] :=
    BetaFunctionRuleToAssignments[1, p, rhs,
				  enumRules, abbrRules, "="];

BetaFunctionRuleToDerivCStmt[BETA[level_Integer, p:(Re|Im)[_]] -> rhs_,
			     enumRules_, abbrRules_] :=
    BetaFunctionRuleToAssignments[level, p, rhs,
				  enumRules, abbrRules, "+="];

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
	If[Expand[deriv] === 0, {},
	   {"  ddx(", qidx, ",", pidx, ") ", op, " ",
	    CExpToCFormString[CConversion`oneOver16PiSqr^level
			      ToCExp[deriv, x]],
	    ";\n"}]
    ]& /@ enumRules
];

toCExpDispatch = Dispatch[{
    Re[z_] :> Lattice`Private`Re[z],
    Im[z_] :> Lattice`Private`Im[z],
    HoldPattern[SARAH`Mass [f_ /; FieldMassDimension[f] === 3/2]] :>
	Lattice`Private`M[f],
    HoldPattern[SARAH`Mass [f_ /; FieldMassDimension[f] === 1  ]] :>
	Sqrt[Lattice`Private`M2[f]],
    HoldPattern[SARAH`Mass2[f_ /; FieldMassDimension[f] === 1  ]] :>
	Lattice`Private`M2[f],
    HoldPattern[SARAH`Mass2[f_ /; FieldMassDimension[f] === 3/2]] :>
	Lattice`Private`M[f]^2
}];

ToCExp[parametrization_] := parametrization //. toCExpDispatch;

ToCExp[parametrization_, array_Symbol] := ToCExp[parametrization] /.
    d:drv[(Lattice`Private`Re|Lattice`Private`Im)[_],
	  (Lattice`Private`Re|Lattice`Private`Im)[_]] :>
	Symbol[DrvToCFormString[d]][array] /.
    p:(Lattice`Private`Re|Lattice`Private`Im)[_] /; ValueQ@ToEnumSymbol[p] :>
	array@ToEnumSymbol[p] /.
    ap:(Lattice`Private`Re|Lattice`Private`Im)[abbr_Symbol] :> ap[array];

ReExpandCExp[cexp_] := Module[{
	expanded = Expand[cexp]
    },
    If[Position[expanded, I] === {}, expanded,
       WriteString["stdout",
		   "Failed to eliminate I from real expression: ", cexp,
		   ",\ntaking its real part\n"];
       Re[expanded]]
];

Differentiate[exp_, x_, abbrRules_] :=
    D[exp, x, NonConstants -> abbrRules[[All,1]]] /.
    HoldPattern@D[f_, y_, ___] -> drv[f, y]

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
    nestedTraceRules = AbbreviateTraces[
	{convertedBetaFunctions, convertedSarahAbbrs}];
    traceRules = Flatten[nestedTraceRules];
    convertedBetaFunctions = convertedBetaFunctions /. traceRules;
    sarahAbbrRules = ParametrizeSarahAbbrs[
	convertedSarahAbbrs, Join[parameterRules, traceRules]];
    nBetaFunctions = Length[convertedBetaFunctions];
    {MapIndexed[
	(WriteString["stdout",
		     "[", First[#2], "/", nBetaFunctions, "] expanding"];
	 ParametrizeBetaFunction[
	     #1, Join[parameterRules, traceRules, sarahAbbrRules[[All,1]]]])&,
	convertedBetaFunctions],
     Flatten[{ParametrizeTraces[nestedTraceRules, parameterRules],
	      sarahAbbrRules[[All,2]]}]}
];

ParametrizeBetaFunction[
    BetaFunction`BetaFunction[name_, _, betanLs_List], partRules_] :=
Module[{
	result
    },
    result =
       MapIndexed[
	   Flatten@ParametrizeBetanLRules[name, #1, First[#2], partRules]&,
	   betanLs];
    WriteString["stdout", "\n"];
    result
];

ParametrizeBetanLRules[name_, betanL_, n_, partRules_] := Module[{
	equations
    },
Done[
    equations = ParametrizeBetanL[name, betanL, n, partRules];
    EquationsToRules /@ equations,
	" BETA[",n ,", ", name, "]... "
]];

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
	    Union@Cases[equations, BETA[_Integer, (Re|Im)[__]], {0, Infinity}]
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

AbbreviateTraces[exp_] := Module[{
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
    traces -> Last@ParametrizeTraceAbbrRule[First[traces] -> abbr];

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

matrixOpRules = Dispatch[{
    SARAH`MatMul :> Dot,
    Parametrization`trp :> Transpose,
    Parametrization`cnj :> Conjugate,
    Parametrization`adj :> ConjugateTranspose,
    SARAH`trace[m__] :> Tr[Dot[m]]
}];

cExpToCFormStringDispatch = Dispatch[{
(*
    p:Power[_?NumericQ, _?NumericQ] :> N[p],
*)
    Power[a_,2]			    :> Global`Sqr[a],
    Power[a_,-2]		    :> 1/Global`Sqr[a]
}];

CExpToCFormString[expr_] :=
    ToString[expr //. cExpToCFormStringDispatch, CForm];

SetAttributes[Done, HoldFirst];

Done[exp_, msg__] := Module[{
	result,
	time
    },
    WriteString["stdout", msg];
    result = Timing[exp];
    If[(time = Round[First[result] 1*^3]) === 0,
       time = ToString[Round[First[result] 1*^6]] <> " us",
       time = ToString[time] <> " ms"];
    WriteString["stdout", time];
    Last[result]
];

SetAttributes[DoneLn, HoldFirst];

DoneLn[exp_, msg__] := Module[{
	result = Done[exp, msg]
    },
    WriteString["stdout", "\n"];
    result
];

End[] (* `Private` *)

EndPackage[]