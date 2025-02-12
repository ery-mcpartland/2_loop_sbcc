(* ::Package:: *)

(* ::Title:: *)
(*Scalar Integrals*)


(* ::Text:: *)
(*Code to convert from tensor integrals to scalar integral (via tensor reduction). After application of this function scalar integrals are written only in terms of P_i*)


(* ::Section:: *)
(*Defining Functions*)


(* ::Subsection:: *)
(*Tensor Reductions*)


(* ::Text:: *)
(*Five functions, one for each class of diagram. Takes a tensor integrand with all scalar products written in terms of P_i, mc, mb and q2 and converts to a scalar integrand using Passarino-Veltman. Takes two arguments , type of diagram ("a" to "e") and tensor integral to reduce. *)


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


(* ::Subsection:: *)
(*Tensor Reductions*)


TensorReduction["a",int_]:=int/.{
l->(-(((-3 mc^2-3 P2+2 P7+P9-q2) q2+mb^2 (mc^2+P2-P9+q2)) p)+((-2 mc^2-2 P2+P7+P9-q2) q2+mb^2 (P7-P9+q2)) q)/t^2,
r->(-((mb^4+mb^2 (P5-P8-q2)+(-2 P4+P5+P8) q2) Subscript[p, \[Nu]])+(mb^4+(-P4+P8) q2-mb^2 (P4-2 P5+P8+q2)) Subscript[q, \[Nu]])/t^2}


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
r->1/t^2 ((mb^2 (-P1+P12+P2-P3)+(P1-P12-2 P13-P2+P3+2 P4) q2) Subscript[p, r]+(mb^2 (P1-P12+P13-P2+P3-P4)+(-P1+P12+P13+P2-P3-P4) q2) q)}


ReduceToScalar[i_,int_]:=Simplify[FermionLineExpand[TensorReduction[i,int],
ChisholmExpand->False,GordonIdentity->False]]
