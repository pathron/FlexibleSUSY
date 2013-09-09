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
Needs["Lattice`", "Lattice.m"];

On[Assert];

Print["testing TraceSameQ[] ..."];

adj[mq2] = mq2;

TestEquality[Lattice`Private`TraceSameQ[
    SARAH`trace[mq2, adj[Yu], Yu, adj[Yd], Yd],
    cnj@SARAH`trace[mq2, adj[Yd], Yd, adj[Yu], Yu]], True];

Print["testing CExpToCFormString[] ..."];

REf := Lattice`Private`REf;
IMf := Lattice`Private`IMf;
drv := Lattice`Private`drv;
CExpToCFormString := Lattice`Private`CExpToCFormString;

TestEquality[CExpToCFormString@drv[REf[Tr11], REf[md2[1, 1]]],
	     "dRETr11dREmd211"];
TestEquality[CExpToCFormString@drv[REf[SARAH`trace[mq2]], REf[me2[3, 3]]],
	     "dREtracemq2dREme233"];

Print["testing ToCExp[] ..."];

ToCExp := Lattice`Private`ToCExp;

TestEquality[CExpToCFormString @
	     ToCExp[drv[Re[Tr11], Re[md2[1, 1]]], x],
	     "dRETr11dREmd211(x)"];
TestEquality[CExpToCFormString @
	     ToCExp[drv[Re[SARAH`trace[mq2]], Re[me2[3, 3]]], x]
	     "dREtracemq2dREme233(x)"];

PrintTestSummary[];
