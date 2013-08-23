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

BeginPackage["IndexStructure`", {"SARAH`"}]

ConvertSarahTerms::usage;
RelevantTerms::usage;
TermsHolomorphicIn::usage;
RedundancyList::usage;
HermiticityConditions::usage;

Begin["`Private`"]

conj := Susyno`LieGroups`conj;

ConvertSarahTerms[{}, terms_] := Expand[terms];

ConvertSarahTerms[couplingPatterns_List, terms_] := Module[{
	terms$ = Expand[terms],
	oldTerms,
	newTerms
    },
    {oldTerms, newTerms} =
	Transpose[ConversionRelevantTo[#, terms$]& /@ couplingPatterns];
    terms$ - Plus@@oldTerms + Plus@@newTerms
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
    ! DependsOn[conj[couplingPattern], term];

RelevantTermList[couplingPattern_, terms_Plus] :=
    Extract[terms, Take[#, 1]& /@
	    Position[terms, couplingPattern, {0, Infinity}]];

RelevantTermList[couplingPattern_, term_] := {term} /;
    DependsOn[couplingPattern, term];

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
	   SelfDependent[Last[#], couplingPattern]&]
];

HermiticityConditions[couplingPattern_, terms_] := Module[{
	firstTerm = FirstTerm[terms],
	indexedCoupling,
	solutions,
	s
    },
    indexedCoupling = IndexedCoupling[couplingPattern, firstTerm];
    solutions =
	QuietSolve[terms == conj[terms /. #], indexedCoupling /. #]& /@
	IndexPermutationRuleLists[couplingPattern, firstTerm];
    Select[Cases[solutions, {{ s:(_ -> _) }} -> s],
	   SelfDependent[Last[#], couplingPattern]&]
];

EnforceCommonIndices[couplingPattern_, terms_Plus] := Module[{
	indexLists = IndexCollections[couplingPattern, FirstTerm[terms]]
    },
    (# /. Thread[Flatten@IndexCollections[couplingPattern, #] ->
		 Flatten@indexLists])& /@ terms
];

EnforceCommonIndices[_, term_] := term;

QuietSolve[eqs_, rest___] := Module[{
	dummy
    },
    (* SARAH`sum has some supernatural effect that breaks Solve[] *)
    Quiet[Solve[eqs /. SARAH`sum :> dummy, rest], Solve::nsmet]
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

SelfDependent[solution_, couplingPattern_] :=
    (Length[Variables[solution]] === 1) &&
    DependsOn[couplingPattern, solution];

DependsOn[couplingPattern_, exp_] :=
    Cases[exp, couplingPattern, {0, Infinity}] =!= {};

CouplingPattern[indexedCoupling_] :=
    indexedCoupling /. Alternatives@@indexedCoupling -> _;

IndexedCoupling[pattern_, term_] := SingleCase[term, pattern, {0, Infinity}];

SingleCase[args__] := Module[{
	cases = Cases[args]
    },
    Assert[Length[cases] === 1];
    First[cases]
];

End[] (* `Private` *)

EndPackage[]
