
BeginPackage["Traces`", {"SARAH`", "CConversion`"}];

CreateDoubleTraceAbbrs::usage="takes a list of traces and returns a
two-component list, where the first entry is string of C/C++ variable
definitions that hold the trace values.  The second entry is a list of
rules to replace the traces by their C/C++ variables.";

FindMultipleTraces::usage="takes a list of expressions and returns a
list of traces that appear more than once in the list";

CreateTraceAbbr::usage="takes SARAH's `TraceAbbr' and returns a
two-component list, where the first entry is string of C/C++ variable
definitions that hold the trace values.  The second entry is a list of
rules to replace the traces by their C/C++ variables.";

Begin["Private`"];

CreateTraceAbbr[abbrs_] :=
    Module[{def = "", i, j, name, expr, rules = {}},
           For[i = 1, i <= Length[abbrs], i++,
               For[j = 1, j <= Length[abbrs[[i]]], j++,
                   {name, expr} = abbrs[[i,j]];
                   AppendTo[rules, Rule[name, ToValidCSymbol[name]]];
                   def = def <> "const double " <> ToValidCSymbolString[name]
                         <> " = " <> RValueToCFormString[expr] <> ";\n";
                  ];
              ];
           Return[{def, rules}];
          ];

FindMultipleTraces[list_List] :=
    Module[{traces},
           traces = Flatten[Cases[list, trace[__], Infinity]];
           traces = (#[[1]])& /@ Select[Tally[traces], (#[[2]] > 1)&];
           Return[traces];
          ];

CreateDoubleTraceAbbrs[traces_List] :=
    Module[{rules, decl = "", i},
           rules = (Rule[#, ToValidCSymbol[#]])& /@ traces;
           For[i = 1, i <= Length[traces], i++,
               decl = decl <> "const double " <>
                      ToValidCSymbolString[traces[[i]]] <>
                      " = " <> RValueToCFormString[traces[[i]]] <> ";\n";
              ];
           Return[{decl, rules}];
          ];

End[];

EndPackage[];