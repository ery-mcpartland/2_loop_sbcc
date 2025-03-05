(* ::Package:: *)

(* ::Title:: *)
(*Scalar Integrals*)


(* ::Text:: *)
(*Code to convert from tensor integrals to scalar integral (via tensor reduction). After application of this function scalar integrals are written only in terms of functions of P_i, mb, mc and q2*)


(* ::Section:: *)
(*Defining Functions*)


(* ::Subsection:: *)
(*Tensor Reduction*)


(* ::Text:: *)
(*Five functions, one for each class of diagram.  Contains the Passarion-Veltman rules for each diagram family. Takes a tensor integrand with all scalar products written in terms of P_i, mc, mb and q2 and converts to a scalar integrand using Passarino-Veltman. Takes two arguments , type of diagram ("a" to "e") and tensor integral to reduce. These rules were generated in the notebook Determine_Functions.nb*)


(* ::Subsection:: *)
(*Reduce to Scalar*)


(* ::Text:: *)
(*One function, takes two arguments - diagram family and tensor integral to reduce. Applies Passarino-Veltman replacement rules; performs any remaining Dirac algebra and applies equations of motion to get final result.*)


(* ::Section:: *)
(*Functions*)


(* ::Subsection:: *)
(*Initialisation*)


Needs["X`"]


(* ::Text:: *)
(*Below we hard code which of our terms are scalars (all Pi's, mc, mb and q2)*)


LScalarQ[P1] = True;
LScalarQ[P2] = True;
LScalarQ[P3] = True;
LScalarQ[P4] = True;
LScalarQ[P5] = True;
LScalarQ[P6] = True;
LScalarQ[P7] = True;
LScalarQ[P8] = True;
LScalarQ[P9] = True;
LScalarQ[P10] = True;
LScalarQ[P11] = True;
LScalarQ[P12] = True;
LScalarQ[P13] = True;
LScalarQ[mc] = True;
LScalarQ[mb] = True;
LScalarQ[q2] = True;
LScalarQ[t] = True;


(* ::Subsection:: *)
(*Tensor Reductions*)


TensorReduction["a",int_]:=int/.{
l->(-(((-3 mc^2-3 P2+2 P7+P9-q2) q2+mb^2 (mc^2+P2-P9+q2)) p)+((-2 mc^2-2 P2+P7+P9-q2) q2+mb^2 (P7-P9+q2)) q)/t^2,
r->(-((mb^4+mb^2 (P5-P8-q2)+(-2 P4+P5+P8) q2)p)+(mb^4+(-P4+P8) q2-mb^2 (P4-2 P5+P8+q2)) q)/t^2}


TensorReduction["b",int_]:=int/.{
l->(-(((-3 mc^2-3 P2+2 P7+P9-q2) q2+mb^2 (mc^2+P2-P9+q2)) p)+((-2 mc^2-2 P2+P7+P9-q2) q2+mb^2 (P7-P9+q2)) q)/t^2,
r->(-((mb^4+(P10+P11-2 P4) q2+mb^2 (P10-P11+q2)) p)+(2 mb^4+mb^2 (2 P10-P11-P4)+(P11-P4) q2) q)/t^2}


TensorReduction["c",int_]:=int/.{
l->((mb^2 (P1-P2-q2)+q2 (2 mc^2-P1+3 P2-2 P7+q2)) p-(mb^2 (mc^2+P1-P7-q2)+q2 (mc^2-P1+2 P2-P7+q2)) q)/t^2,
r->((-mb^2 (P4-P6+q2)+q2 (3 P4-2 P5-P6+q2)) p+((-2 P4+P5+P6-q2) q2+mb^2 (P5-P6+q2)) q)/t^2}


TensorReduction["d",int_]:=int/.{
l->((mb^2 (P1-P2-q2)+q2 (2 mc^2-P1+3 P2-2 P7+q2)) p-(mb^2 (mc^2+P1-P7-q2)+q2 (mc^2-P1+2 P2-P7+q2)) q)/t^2,
r->(-((q2 (2 P11-P4-P6+q2)+mb^2 (P4-P6+q2)) p)+((P11-P4) q2+mb^2 (P11+P4-2 P6+2 q2)) q)/t^2}


TensorReduction["e",int_]:=int/.{
l->((mb^2 (P1-P2-q2)+q2 (2 mc^2-P1+3 P2-2 P7+q2)) p-(mb^2 (mc^2+P1-P7-q2)+q2 (mc^2-P1+2 P2-P7+q2)) q)/t^2,
r->1/t^2 ((mb^2 (-P1+P12+P2-P3)+(P1-P12-2 P13-P2+P3+2 P4) q2)p+(mb^2 (P1-P12+P13-P2+P3-P4)+(-P1+P12+P13+P2-P3-P4) q2) q)}


(* ::Subsection:: *)
(*Reduce to Scalar*)


ReduceToScalar[i_,int_]:=Simplify[FermionLineExpand[TensorReduction[i,int],ChisholmExpand->False,
GordonIdentity->False]/.{LDot[p,p]->mb^2,LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2}]


(* ::Chapter:: *)
(*New Attempt*)


(* ::Input::Initialization:: *)
\!\(\*
TagBox[
RowBox[{"finalProjVec", "=", 
StyleBox[
RowBox[{"List", "[", 
RowBox[{
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"-", "2"}], ",", "d"}], "]"}], ",", 
RowBox[{"-", "1"}]}], "]"}], ",", 
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", "q2"}], "]"}]}], "]"}], ",", 
RowBox[{"-", "3"}]}], "]"}], ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "2"}], ",", "q2"}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{"d", ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}], ",", "q2"}], "]"}]}], "]"}]}], "]"}], ",", 
RowBox[{"DiracMatrix", "[", "]"}], ",", 
RowBox[{"LTensor", "[", 
RowBox[{"p", ",", "\\[Mu]"}], "]"}]}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{"mb", ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", 
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}]}], "]"}], ",", "q2"}], "]"}], ",", 
RowBox[{"DiracMatrix", "[", 
RowBox[{"LTensor", "[", 
RowBox[{"DiracG", ",", "\\[Mu]"}], "]"}], "]"}]}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "2"}], ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", "d"}], "]"}], ",", "mb", ",", 
RowBox[{"DiracMatrix", "[", "]"}], ",", 
RowBox[{"LTensor", "[", 
RowBox[{"q", ",", "\\[Mu]"}], "]"}]}], "]"}]}], "]"}]}], "]"}]}], "]"}]}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"-", "2"}], ",", "d"}], "]"}], ",", 
RowBox[{"-", "1"}]}], "]"}], ",", 
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", "q2"}], "]"}]}], "]"}], ",", 
RowBox[{"-", "3"}]}], "]"}], ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "2"}], ",", "q2"}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{"d", ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}], ",", "q2"}], "]"}]}], "]"}]}], "]"}], ",", 
RowBox[{"DiracMatrix", "[", "DiracG5", "]"}], ",", 
RowBox[{"LTensor", "[", 
RowBox[{"p", ",", "\\[Mu]"}], "]"}]}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{"mb", ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", "q2"}], "]"}]}], "]"}], ",", 
RowBox[{"DiracMatrix", "[", 
RowBox[{
RowBox[{"LTensor", "[", 
RowBox[{"DiracG", ",", "\\[Mu]"}], "]"}], ",", "DiracG5"}], "]"}]}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{"2", ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", "d"}], "]"}], ",", "mb", ",", 
RowBox[{"DiracMatrix", "[", "DiracG5", "]"}], ",", 
RowBox[{"LTensor", "[", 
RowBox[{"q", ",", "\\[Mu]"}], "]"}]}], "]"}]}], "]"}]}], "]"}]}], "]"}]}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"-", "2"}], ",", "d"}], "]"}], ",", 
RowBox[{"-", "1"}]}], "]"}], ",", 
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", "q2"}], "]"}]}], "]"}], ",", 
RowBox[{"-", "3"}]}], "]"}], ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Times", "[", 
RowBox[{"mb", ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", "q2"}], "]"}]}], "]"}], ",", 
RowBox[{"DiracMatrix", "[", 
RowBox[{"LTensor", "[", 
RowBox[{"DiracG", ",", "\\[Mu]"}], "]"}], "]"}]}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "2"}], ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"-", "2"}], ",", "d"}], "]"}], ",", "q2"}], "]"}]}], "]"}], ",", 
RowBox[{"DiracMatrix", "[", "]"}], ",", 
RowBox[{"LTensor", "[", 
RowBox[{"p", ",", "\\[Mu]"}], "]"}]}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "2"}], ",", "q2"}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{"d", ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}], ",", "q2"}], "]"}]}], "]"}]}], "]"}], ",", 
RowBox[{"DiracMatrix", "[", "]"}], ",", 
RowBox[{"LTensor", "[", 
RowBox[{"q", ",", "\\[Mu]"}], "]"}]}], "]"}]}], "]"}]}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"-", "2"}], ",", "d"}], "]"}], ",", 
RowBox[{"-", "1"}]}], "]"}], ",", 
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", "q2"}], "]"}]}], "]"}], ",", 
RowBox[{"-", "3"}]}], "]"}], ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Times", "[", 
RowBox[{"mb", ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", 
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}]}], "]"}], ",", "q2"}], "]"}], ",", 
RowBox[{"DiracMatrix", "[", 
RowBox[{
RowBox[{"LTensor", "[", 
RowBox[{"DiracG", ",", "\\[Mu]"}], "]"}], ",", "DiracG5"}], "]"}]}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{"2", ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"-", "2"}], ",", "d"}], "]"}], ",", "q2"}], "]"}]}], "]"}], ",", 
RowBox[{"DiracMatrix", "[", "DiracG5", "]"}], ",", 
RowBox[{"LTensor", "[", 
RowBox[{"p", ",", "\\[Mu]"}], "]"}]}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "2"}], ",", "q2"}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{"d", ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}], ",", "q2"}], "]"}]}], "]"}]}], "]"}], ",", 
RowBox[{"DiracMatrix", "[", "DiracG5", "]"}], ",", 
RowBox[{"LTensor", "[", 
RowBox[{"q", ",", "\\[Mu]"}], "]"}]}], "]"}]}], "]"}]}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"Rational", "[", 
RowBox[{"1", ",", "2"}], "]"}], ",", 
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"-", "2"}], ",", "d"}], "]"}], ",", 
RowBox[{"-", "1"}]}], "]"}], ",", 
RowBox[{"Power", "[", 
RowBox[{"mb", ",", 
RowBox[{"-", "1"}]}], "]"}], ",", 
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", "q2"}], "]"}]}], "]"}], ",", 
RowBox[{"-", "2"}]}], "]"}], ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", 
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}]}], "]"}], ",", "q2"}], "]"}], ",", 
RowBox[{"DiracMatrix", "[", 
RowBox[{"LTensor", "[", 
RowBox[{"DiracG", ",", "\\[Mu]"}], "]"}], "]"}]}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{"2", ",", "mb", ",", 
RowBox[{"DiracMatrix", "[", "]"}], ",", 
RowBox[{"LTensor", "[", 
RowBox[{"p", ",", "\\[Mu]"}], "]"}]}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "2"}], ",", "mb", ",", 
RowBox[{"DiracMatrix", "[", "]"}], ",", 
RowBox[{"LTensor", "[", 
RowBox[{"q", ",", "\\[Mu]"}], "]"}]}], "]"}]}], "]"}]}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"Rational", "[", 
RowBox[{"1", ",", "2"}], "]"}], ",", 
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"-", "2"}], ",", "d"}], "]"}], ",", 
RowBox[{"-", "1"}]}], "]"}], ",", 
RowBox[{"Power", "[", 
RowBox[{"mb", ",", 
RowBox[{"-", "1"}]}], "]"}], ",", 
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", "q2"}], "]"}]}], "]"}], ",", 
RowBox[{"-", "2"}]}], "]"}], ",", 
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", 
RowBox[{"Power", "[", 
RowBox[{"mb", ",", "2"}], "]"}]}], "]"}], ",", "q2"}], "]"}], ",", 
RowBox[{"DiracMatrix", "[", 
RowBox[{
RowBox[{"LTensor", "[", 
RowBox[{"DiracG", ",", "\\[Mu]"}], "]"}], ",", "DiracG5"}], "]"}]}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{"2", ",", "mb", ",", 
RowBox[{"DiracMatrix", "[", "DiracG5", "]"}], ",", 
RowBox[{"LTensor", "[", 
RowBox[{"p", ",", "\\[Mu]"}], "]"}]}], "]"}], ",", 
RowBox[{"Times", "[", 
RowBox[{
RowBox[{"-", "2"}], ",", "mb", ",", 
RowBox[{"DiracMatrix", "[", "DiracG5", "]"}], ",", 
RowBox[{"LTensor", "[", 
RowBox[{"q", ",", "\\[Mu]"}], "]"}]}], "]"}]}], "]"}]}], "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True]}],
FullForm]\);


(* ::Input::Initialization:: *)
ReduceToScalarTest[amp_]:=amp/. FermionLine[s1_,s2_,x_DiracMatrix]:> Simplify[Table[Simplify[Contract[Spur[finalProjVec[[i]],LDot[p-q,\[Gamma]],x,LDot[p,\[Gamma]]+mb \[DoubleStruckOne]]]/.{q . q->q2,p . p->mb^2,p . q->(mb^2+q2)/2,\[ScriptD]->d}],{i,1,6}]/.{LTensor[LeviCivitaE,{l},{r},{p},{q}]->0}]


(* ::Input:: *)
(*a3Op1=1/(mb^2 P2 P3 P4 P8) ((24 CFa mb^2 Qs-10 CFa \[ScriptD] mb^2 Qs+CFa \[ScriptD]^2 mb^2 Qs) \[LeftAngleBracket]\[ScriptU][p-q,0],Subscript[\[Gamma], \[Mu]],\[Gamma] . l,\[Gamma] . r,\[DoubleStruckCapitalP]L,\[ScriptU][p,mb]\[RightAngleBracket]+\[LeftAngleBracket]\[ScriptU][p-q,0],Subscript[\[Gamma], \[Mu]],\[Gamma] . r,\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket] (-4 CFa mb mc^2 Qs+4 CFa \[ScriptD] mb mc^2 Qs-CFa \[ScriptD]^2 mb mc^2 Qs+8 CFa mb Qs l . l-6 CFa \[ScriptD] mb Qs l . l+CFa \[ScriptD]^2 mb Qs l . l+8 CFa mb Qs l . p-8 CFa mb Qs l . r+4 CFa \[ScriptD] mb Qs l . r)+\[LeftAngleBracket]\[ScriptU][p-q,0],Subscript[\[Gamma], \[Mu]],\[Gamma] . l,\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket] (-8 CFa mb Qs l . p+4 CFa \[ScriptD] mb Qs l . p-8 CFa mb Qs l . r+4 CFa \[ScriptD] mb Qs l . r-16 CFa mb Qs p . r+4 CFa \[ScriptD] mb Qs p . r+8 CFa mb Qs r . r-6 CFa \[ScriptD] mb Qs r . r+CFa \[ScriptD]^2 mb Qs r . r)+\[LeftAngleBracket]\[ScriptU][p-q,0],Subscript[\[Gamma], \[Mu]],\[DoubleStruckCapitalP]L,\[ScriptU][p,mb]\[RightAngleBracket] (4 CFa mb^2 mc^2 Qs-4 CFa \[ScriptD] mb^2 mc^2 Qs+CFa \[ScriptD]^2 mb^2 mc^2 Qs-8 CFa mb^2 Qs l . l+6 CFa \[ScriptD] mb^2 Qs l . l-CFa \[ScriptD]^2 mb^2 Qs l . l+16 CFa Qs (l . p)^2-8 CFa \[ScriptD] Qs (l . p)^2-32 CFa mb^2 Qs l . r+16 CFa \[ScriptD] mb^2 Qs l . r-2 CFa \[ScriptD]^2 mb^2 Qs l . r+16 CFa Qs l . p l . r-8 CFa \[ScriptD] Qs l . p l . r+8 CFa mc^2 Qs p . r-8 CFa \[ScriptD] mc^2 Qs p . r+2 CFa \[ScriptD]^2 mc^2 Qs p . r-16 CFa Qs l . l p . r+12 CFa \[ScriptD] Qs l . l p . r-2 CFa \[ScriptD]^2 Qs l . l p . r+16 CFa Qs l . p p . r-8 CFa \[ScriptD] Qs l . p p . r+16 CFa Qs l . r p . r-8 CFa \[ScriptD] Qs l . r p . r-16 CFa Qs l . p r . r+12 CFa \[ScriptD] Qs l . p r . r-2 CFa \[ScriptD]^2 Qs l . p r . r))*)


ReduceToScalarTest[a3Op1]
