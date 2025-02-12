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


TensorReduction["a",int_]:=int/.{r->P1 p,l->P2 q}


ReduceToScalar[i_,int_]:=Simplify[FermionLineExpand[TensorReduction[i,int],
ChisholmExpand->False,GordonIdentity->False]]
