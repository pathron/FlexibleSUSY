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

BeginPackage["Parametrization`", {"SARAH`"}]

SuperpotentialParameterRules::usage;
SusyBreakingParameterRules::usage;
ParameterRules::usage;
HasIndicesQ::usage;
UpdateValues::usage;
CouplingDimensions::usage;
Sphericalize::usage;

sarahOperatorReplacementRules::usage;
ConvertSarahTerms::usage;
RelevantTerms::usage;
TermsHolomorphicIn::usage;
RedundancyList::usage;
HermiticityConditions::usage;
CouplingPattern::usage;

trp::usage;
cnj::usage;
adj::usage;

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

ConvertSarahTerms[terms_] := Expand[terms] /. sarahOperatorReplacementRules;

ConvertSarahTerms[terms_, {}] := ConvertSarahTerms[terms];

ConvertSarahTerms[terms_, couplingPatterns_List] := Module[{
	$terms = ConvertSarahTerms[terms],
	oldTerms,
	newTerms
    },
    {oldTerms, newTerms} =
	Transpose[ConversionRelevantTo[#, $terms]& /@ couplingPatterns];
    $terms - Plus@@oldTerms + Plus@@newTerms
];

ConversionRelevantTo[couplingPattern_, terms_] := Module[{
	relevantTerms = RelevantTerms[couplingPattern, terms]
    },
    {relevantTerms, EnforceCommonIndices[couplingPattern, relevantTerms]}
];

RelevantTerms[couplingPattern_, terms_] :=
    Plus@@RelevantTermList[couplingPattern, terms];

TermsHolomorphicIn[couplingPattern_, terms_] :=
    Plus@@Select[RelevantTermList[couplingPattern, terms],
		 HolomorphicIn[couplingPattern, #]&];

HolomorphicIn[couplingPattern_, term_] :=
    ! DependsOnQ[cnj[couplingPattern], term];

RelevantTermList[couplingPattern_, terms_Plus] :=
    Extract[terms, Take[#, 1]& /@
	    Position[terms, couplingPattern, {0, Infinity}]];

RelevantTermList[couplingPattern_, term_] := {term} /;
    DependsOnQ[couplingPattern, term];

RelevantTermList[couplingPattern_, term_] := {};

RedundancyList[couplingPattern_, terms_] := Module[{
	firstTerm = FirstTerm[terms],
	indexedCoupling,
	solutions,
	s
    },
    indexedCoupling = IndexedCoupling[couplingPattern, firstTerm];
    solutions =
	QuietSolve[terms == (terms /. #), indexedCoupling /. #]& /@
	Rest@IndexPermutationRuleLists[couplingPattern, firstTerm];
    Select[Cases[solutions, {{ s:(_ -> _) }} -> s],
	   SelfDependentQ[Last[#], couplingPattern]&]
];

HermiticityConditions[couplingPattern_, terms_] := Module[{
	firstTerm = FirstTerm[terms],
	indexedCoupling,
	solutions,
	s
    },
    indexedCoupling = IndexedCoupling[couplingPattern, firstTerm];
    solutions =
	QuietSolve[terms == cnj[terms /. #], indexedCoupling /. #]& /@
	IndexPermutationRuleLists[couplingPattern, firstTerm];
    Select[Cases[solutions, {{ s:(_ -> _) }} -> s],
	   SelfDependentQ[Last[#], couplingPattern]&]
];

EnforceCommonIndices[couplingPattern : _[__] ? HasBlankQ, terms_Plus] :=
Module[{
	indexLists = IndexCollections[couplingPattern, FirstTerm[terms]]
    },
    (# /. Thread[Flatten@IndexCollections[couplingPattern, #] ->
		 Flatten@indexLists])& /@ terms
];

EnforceCommonIndices[_, term_] := term;

QuietSolve[args___] := Block[{
	(* SARAH`sum has some supernatural effect that breaks Solve[] *)
	SARAH`sum
    },
    Quiet[Solve[args], {Solve::nsmet}]
];

IndexPermutationRuleLists[couplingPattern_, term_] := Module[{
	indexLists = IndexCollections[couplingPattern, term]
    },
    (Thread[Flatten[indexLists] -> Flatten[#]])& /@ Permutations[indexLists]
];

IndexCollections[couplingPattern_, term_] := Module[{
	i
    },
    SingleCase[term, _[i:{___,#,___}] :> i, {0, Infinity}]& /@
    List@@IndexedCoupling[couplingPattern, term]
];

FirstTerm[terms_Plus] := First[terms];

FirstTerm[term_] := term;

SelfDependentQ[solution_, couplingPattern_] :=
    (Length[Variables[solution]] === 1) &&
    DependsOnQ[couplingPattern, solution];

DependsOnQ[couplingPattern_, exp_] :=
    Cases[exp, couplingPattern, {0, Infinity}] =!= {};

CouplingPattern[indexedCoupling : couplingHead_?CouplingHeadQ[__]] :=
    couplingHead @@ Table[_, {Length[indexedCoupling]}];

CouplingPattern[coupling_] := coupling;

CouplingHeadQ[couplingHead_] := CouplingDimensions[couplingHead] =!= Undefined;

IndexedCoupling[pattern_, term_] := SingleCase[term, pattern, {0, Infinity}];

HasBlankQ[pattern_] :=
    Cases[pattern, _Blank | _BlankSequence | _BlankNullSequence,
	  {0, Infinity}, Heads -> True] =!= {};

SingleCase[args__] := Module[{
	cases = Cases[args]
    },
    Assert[Length[cases] === 1];
    First[cases]
];

Sphericalize[parameterRules_] := Module[{
	matrices = Union@Cases[
	    Variables[parameterRules[[All, 2]]] /. Re|Im -> Identity,
	    m_[_, _] :> m],
	apparentlyYukawas,
	apparentlyTrilinears,
	i, j
    },
    apparentlyYukawas =
	Select[matrices, ApparentlyYukawaQ];
    apparentlyTrilinears =
	Select[matrices, ApparentlyYukawaTrilinearQ];
    (trp[#] = #; cnj[#] = #; adj[#] = #)& /@ matrices;
    parameterRules /.
	_Im | (Re[_[i_, j_]] /; i =!= j) |
	Alternatives@@(Except[#@@CouplingDimensions[#], #[_,_]]& /@
		       Join[apparentlyYukawas, apparentlyTrilinears]) -> 0
];

ApparentlyYukawaQ[matrix_Symbol] :=
    StringMatchQ[SymbolName[matrix], "Y" ~~ ___];

ApparentlyYukawaQ[_] := False;

ApparentlyYukawaTrilinearQ[T[matrix_?ApparentlyYukawaQ]] := True;

ApparentlyYukawaTrilinearQ[_] := False;

sarahOperatorReplacementRules := {
    SARAH`Tp -> trp,
    SARAH`Adj -> adj,
    SARAH`Conj | Susyno`LieGroups`conj -> cnj
};

UpdateValues[] := (

DownValues[cnj] =
    DownValues[Susyno`LieGroups`conj] /. sarahOperatorReplacementRules;
UpValues  [cnj] =
    UpValues  [Susyno`LieGroups`conj] /. sarahOperatorReplacementRules;

Re[cnj[z_]] ^:=  Re[z];
Im[cnj[z_]] ^:= -Im[z];
cnj[x_Re] := x;
cnj[x_Im] := x;

DownValues[trp] = DownValues[SARAH`Tp] /. sarahOperatorReplacementRules;
UpValues  [trp] = UpValues  [SARAH`Tp] /. sarahOperatorReplacementRules;

DownValues[adj] = DownValues[SARAH`Adj] /. sarahOperatorReplacementRules;
UpValues  [adj] = UpValues  [SARAH`Adj] /. sarahOperatorReplacementRules;

trp[adj[m_]] := cnj[m];
trp[cnj[m_]] := adj[m];
trp[trp[m_]] := m;

adj[cnj[m_]] := trp[m];
adj[trp[m_]] := cnj[m];
adj[adj[m_]] := m;

cnj[adj[m_]] := trp[m];
cnj[trp[m_]] := adj[m];
cnj[SARAH`trace[m__]] := cnj /@ SARAH`trace[m];

(* SARAH`getDimParameters[T] === {3, 3} *)

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

UpdateValues[];

End[] (* `Private` *)

EndPackage[]
