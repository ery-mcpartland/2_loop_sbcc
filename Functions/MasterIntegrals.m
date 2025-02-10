(* ::Package:: *)

(* ::Title:: *)
(*Master Integrals*)


(* ::Text:: *)
(*Code to convert from an amplitude expressed in terms of scalar integrals (in \!\(TraditionalForm\`*)
(*SubscriptBox[*)
(*StyleBox["P", "TI"], *)
(*StyleBox["i", "TI"]]\) basis) to a minimal set of master integrals*)


(* ::Section:: *)
(*Function Descriptions*)


(* ::Subsection:: *)
(*j Integral conversion*)


(* ::Text:: *)
(*Converts the scalar integrals to the form of j integrals. *)
(**)
(*There is a function that separates each amplitude into a list of integrals which can be converted to j integrals*)
(**)
(*Five functions, one for each class of diagram. Takes two arguments - type of diagram ("a" to "e") and single integral to be converted to j integral form. Output is a list, first entry is coefficient and second is a list of the powers of each of the propagators*)
(**)
(*Final function uses the previous two to convert from an amplitude in usual form to an amplitude in j integral form*)


(* ::Subsection::Closed:: *)
(*Master Integral Basis creation*)


(* ::Text:: *)
(*Generates the master integral basis and reduction rules for each type of diagram. Five functions, one for each class of diagram. Takes one argument - type of diagram ("a" to "e") - this will not be part of this package - the reduction rules will be included, each diagram has its own directory*)


(* ::Subsection:: *)
(*Master Integral Reduction*)


(* ::Text:: *)
(*Reduces an amplitude in terms of j integrals into the minimum set of master integrals. Five functions, one for each class of diagram. Takes two arguments - type of diagram ("a" to "e") and amplitude in terms of j integrals*)


(* ::Section:: *)
(*Functions*)


(* ::Subsection:: *)
(*Initialisation*)


Needs["LiteRed`"]


(* ::Subsection:: *)
(*j integrals*)


jIntegralConvert["a",sAmp_]:=


jIntegralConvert["b",sAmp_]:=


jIntegralConvert["c",sAmp_]:=


jIntegralConvert["d",sAmp_]:=


jIntegralConvert["e",sAmpList_]:=For[IntList={};i=1,i<(Length[sAmpList]+1),i++,
AppendTo[IntList,gettingPowersFromSingleTerm["e",Part[1/(mb^2(mb-q)(mb+q)) sAmpList,i]]]]
FullSimplify[Total[IntList/.{b_,{a1_,a2_,a3_,a4_,a5_,a6_,a7_}}->b j[e,a1,a2,a3,a4,a5,a6,a7]]/.q . q->q^2]


(* ::Subsection:: *)
(*Reduce to Master Integrals*)


MasterIntReduce["a",jAmp_]:=


MasterIntReduce["b",jAmp_]:=


MasterIntReduce["c",jAmp_]:=


MasterIntReduce["d",jAmp_]:=


MasterIntReduce["e",jAmp_]:=




(* ::Section:: *)
(*Appendix*)


(* ::Subsection:: *)
(*Testing*)


diagramE0ii={1/(mb^2 P2 P3^2 P4 (mb-q) (mb+q)) (-2+\[ScriptD]) \[LeftAngleBracket]\[ScriptU][p-q,0],Subscript[\[Gamma], \[Mu]],\[DoubleStruckCapitalP]L,\[ScriptU][p,mb]\[RightAngleBracket] (mb^2 (4 mc^2 (-P12+P3)+(-2+\[ScriptD]) (-P3 (P1+P3-P4)+P12 (P2+P3-P4)))+(4 mc^2 (P12+2 P13-P3+2 P7)-(-2+\[ScriptD]) (-P3 (P1+P3-P4)+P12 (P2+P3-P4)+2 P13 (P2+P3-P4)+2 (P2-P4) P7)) q^2+(4 mc^2-(-2+\[ScriptD]) (P2-P4)) (mb-q) (mb+q) q . q)+1/(mb P2 P3^2 P4 (mb-q)^2 (mb+q)^2) 2 ((2-\[ScriptD]) (4 mc^2-(-2+\[ScriptD]) (P2+P3-P4)) (mb^2 (P1-P12+2 P13-P2+P3)+(-P1+P12+2 P13+P2-P3) q^2)+(-2+\[ScriptD]) (4 mc^2-(-2+\[ScriptD]) (P2-P4)) (mb^2 (P1-P2-2 P7)-(mb^2+P1-P2+2 P7) q^2+q^4)) \[LeftAngleBracket]\[ScriptU][p-q,0],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket] Subscript[p, \[Mu]]+1/(mb P2 P3^2 P4 (mb-q)^2 (mb+q)^2) 2 (-2+\[ScriptD]) (q^2 (4 mc^2 (P12+2 P13-P3+2 P7-q^2)-(-2+\[ScriptD]) (-P1 P3-P3^2+P12 (P2+P3-P4)+2 P13 (P2+P3-P4)+P3 P4+2 P2 P7-2 P4 P7+(-P2+P4) q^2))+mb^2 (4 mc^2 (-P12+2 P13+P3+2 P7+q^2)+(-2+\[ScriptD]) (-P1 P3-P3^2+P12 (P2+P3-P4)-2 P13 (P2+P3-P4)+P3 P4-2 P2 P7+2 P4 P7+(-P2+P4) q^2))) \[LeftAngleBracket]\[ScriptU][p-q,0],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket] Subscript[q, \[Mu]]}


(* ::Section:: *)
(*Automating process*)


(* ::Subsection:: *)
(*Initialisation and defining functions*)


(* ::Input:: *)
(*ClearAll[f]*)
(*f=Replace[ExpandAll@#,Plus->List,1,Heads->True]&;*)


gettingPowersFromSingleTerm["a",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P2,1/P3,1/P4,1/P5,1/P8,1/P7,1/P9}];
coeff=Coefficient[singleTerm,(1/P2^#1 1/P3^#2 1/P4^#3 1/P5^#4 1/P8^#5 1/P7^#6 1/P9^#7) & @@ powers];
{coeff,powers}
]


gettingPowersFromSingleTerm["b",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P2,1/P3,1/P4,1/P10,1/P11,1/P7,1/P9}];
coeff=Coefficient[singleTerm,(1/P2^#1 1/P3^#2 1/P4^#3 1/P10^#4 1/P11^#5 1/P7^#6 1/P9^#7) & @@ powers];
{coeff,powers}
]


gettingPowersFromSingleTerm["c",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P1,1/P2,1/P3,1/P4,1/P5,1/P6,1/P7}];
coeff=Coefficient[singleTerm,(1/P1^#1 1/P2^#2 1/P3^#3 1/P4^#4 1/P5^#5 1/P6^#6 1/P7^#7) & @@ powers];
{coeff,powers}
]


gettingPowersFromSingleTerm["d",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P1,1/P2,1/P12,1/P4,1/P11,1/P6,1/P7}];
coeff=Coefficient[singleTerm,(1/P1^#1 1/P2^#2 1/P12^#3 1/P4^#4 1/P11^#5 1/P6^#6 1/P7^#7) & @@ powers];
{coeff,powers}
]


gettingPowersFromSingleTerm["e",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P1,1/P2,1/P3,1/P4,1/P12,1/P7,1/P13}];
coeff=Coefficient[singleTerm,(1/P1^#1 1/P2^#2 1/P3^#3 1/P4^#4 1/P12^#5 1/P7^#6 1/P13^#7) & @@ powers];
{coeff,powers}
]


(* ::Subsection:: *)
(*Extracting correct integral*)


(* ::Input:: *)
(*cTypeIntegral=Part[FullSimplify[(Coefficient[diagramE0ii,\[LeftAngleBracket]\[ScriptU][p-q,0],Subscript[\[Gamma], \[Mu]],\[DoubleStruckCapitalP]L,\[ScriptU][p,mb]\[RightAngleBracket] ])mb^2(mb-q)(mb+q)],1]*)


(* ::Input:: *)
(*1/(P2 P3^2 P4) (-2+\[ScriptD]) (mb^2 (4 mc^2 (-P12+P3)+(-P3 (P1+P3-P4)+P12 (P2+P3-P4)) (-2+\[ScriptD]))+q^2 (4 mc^2 (P12+2 P13-P3+2 P7)-(-P3 (P1+P3-P4)+P12 (P2+P3-P4)+2 P13 (P2+P3-P4)+2 (P2-P4) P7) (-2+\[ScriptD]))+(mb-q) (mb+q) (4 mc^2-(P2-P4) (-2+\[ScriptD])) q . q)*)


(* ::Input:: *)
(*oldIntegralList=Part[f/@{cTypeIntegral},1]*)
(**)


(* ::Input:: *)
(*For[newIntegralList={};i=1,i<(Length[oldIntegralList]+1),i++,AppendTo[newIntegralList,gettingPowersFromSingleTerm["e",Part[1/(mb^2(mb-q)(mb+q)) oldIntegralList,i]]]]*)


finalIntegral=FullSimplify[Total[newIntegralList/.{b_,{a1_,a2_,a3_,a4_,a5_,a6_,a7_}}->b j[e,a1,a2,a3,a4,a5,a6,a7]]/.q . q->q^2]


{x+2x^2,1+x,70x^2+3x^3}


Coefficient[{x+2x^2,1+x,70x^2},x^2]


Exponent[{x+2x^2,1+x,70x^2+3x^3},x]


gettingPowersFromSingleTerm["e",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P1,1/P2,1/P3,1/P4,1/P12,1/P7,1/P13}];
coeff=Coefficient[singleTerm,(1/P1^#1 1/P2^#2 1/P3^#3 1/P4^#4 1/P12^#5 1/P7^#6 1/P13^#7) & @@ powers];
{coeff,powers}
]


{-((4 mb^2 P12)/(P2 P3^2)),(4 \[ScriptD] mb^2 P12)/(P2 P3^2),-((\[ScriptD]^2 mb^2 P12)/(P2 P3^2))}


gettingPowersFromSingleTerm["e",{-((4 mb^2 P12)/(P2 P3^2)),(4 \[ScriptD] mb^2 P12)/(P2 P3^2),-((\[ScriptD]^2 mb^2 P12)/(P2 P3^2))}]



cTypeIntegral=1/(P2 P3^2 P4) (-2+\[ScriptD]) (mb^2 (4 mc^2 (-P12+P3)+(-P3 (P1+P3-P4)+P12 (P2+P3-P4)) (-2+\[ScriptD]))+
q^2 (4 mc^2 (P12+2 P13-P3+2 P7)-(-P3 (P1+P3-P4)+P12 (P2+P3-P4)+2 P13 (P2+P3-P4)+2 (P2-P4) P7) (-2+\[ScriptD]))+
(mb-q) (mb+q) (4 mc^2-(P2-P4) (-2+\[ScriptD])) q . q)


e0iiAmpList=Part[f/@{cTypeIntegral},1]


jIntegralConvert["e",e0iiAmpList]
