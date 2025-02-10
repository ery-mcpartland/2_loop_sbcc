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
(*Five functions, one for each class of diagram. Takes a tensor integrand with all scalars written in terms of P_i and converts to a scalar integrand using Passarino-Veltman. Takes two arguments , type of diagram ("a" to "e") and tensor integral to reduce. *)


(* ::Section:: *)
(*Functions*)


(* ::Subsection:: *)
(*Initialisation*)


Needs["X`"]


(* ::Subsection::Closed:: *)
(*Reductions (redundant)*)


ReduceToScalar["a",pAmp_]:=Collect[FermionLineExpand[(pAmp /.{LTensor[l, \[Mu]]->LTensor[p, \[Mu]]((P7)/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(1/2 mb^2-1/2 q^2) ((P7+P9)-mb^2 (P7)/(1/2 mb^2-1/2 q^2)),
LTensor[r, \[Mu]]->LTensor[p, \[Mu]]((1/2 (-P4+P5))/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(1/2 mb^2-1/2 q^2) ((1/2 (-mb^2-P4+P8))-mb^2 (1/2 (-P4+P5))/(1/2 mb^2-1/2 q^2))}
/.{LTensor[\[Sigma], \[Mu],{r}]->LTensor[\[Sigma], \[Mu],\[Nu]] LTensor[r, \[Nu]],LTensor[\[Sigma], \[Mu],{l}]->LTensor[\[Sigma], \[Mu],\[Nu]] LTensor[l, \[Nu]]}/.{LTensor[l, \[Nu]]->LTensor[p, \[Nu]]((P7)/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Nu]]-LTensor[q, \[Nu]]) 1/(1/2 mb^2-1/2 q^2) ((P7+P9)-mb^2 (P7)/(1/2 mb^2-1/2 q^2)),
LTensor[r, \[Nu]]->LTensor[p, \[Nu]]((1/2 (-P4+P5))/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Nu]]-LTensor[q, \[Nu]]) 1/(1/2 mb^2-1/2 q^2) ((1/2 (-mb^2-P4+P8))-mb^2 (1/2 (-P4+P5))/(1/2 mb^2-1/2 q^2))})
/.LTensor[q, \[Nu]]->LTensor[p, \[Nu]]-LTensor[k, \[Nu]]/.p-q->k//Contract,GordonIdentity->False]/.k->p-q,{LTensor[p, \[Mu]],LTensor[q, \[Mu]],LTensor[\[Gamma], \[Mu]]},FullSimplify]


ReduceToScalar["b",pAmp_]:=Collect[FermionLineExpand[(pAmp /.{LTensor[l, \[Mu]]->LTensor[p, \[Mu]]((P7)/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(1/2 mb^2-1/2 q^2) ((P7+P9)-mb^2 (P7)/(1/2 mb^2-1/2 q^2)),
LTensor[r, \[Mu]]->LTensor[p, \[Mu]]((1/2 (mb^2+P10-P4))/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(1/2 mb^2-1/2 q^2) (((P11-P4)/2)-mb^2 (1/2 (mb^2+P10-P4))/(1/2 mb^2-1/2 q^2))}
/.{LTensor[\[Sigma], \[Mu],{r}]->LTensor[\[Sigma], \[Mu],\[Nu]] LTensor[r, \[Nu]],LTensor[\[Sigma], \[Mu],{l}]->LTensor[\[Sigma], \[Mu],\[Nu]] LTensor[l, \[Nu]]}/.{LTensor[l, \[Nu]]->LTensor[p, \[Nu]]((P7)/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Nu]]-LTensor[q, \[Nu]]) 1/(1/2 mb^2-1/2 q^2) ((P7+P9)-mb^2 (P7)/(1/2 mb^2-1/2 q^2)),
LTensor[r, \[Nu]]->LTensor[p, \[Nu]]((1/2 (mb^2+P10-P4))/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Nu]]-LTensor[q, \[Nu]]) 1/(1/2 mb^2-1/2 q^2) (((P11-P4)/2)-mb^2 (1/2 (mb^2+P10-P4))/(1/2 mb^2-1/2 q^2))})
/.LTensor[q, \[Nu]]->LTensor[p, \[Nu]]-LTensor[k, \[Nu]]/.p-q->k//Contract,GordonIdentity->False]/.k->p-q,{LTensor[p, \[Mu]],LTensor[q, \[Mu]],LTensor[\[Gamma], \[Mu]]},FullSimplify]


ReduceToScalar["c",pAmp_]:=Collect[FermionLineExpand[(pAmp /.{LTensor[l, \[Mu]]->LTensor[p, \[Mu]]((P7)/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(1/2 mb^2-1/2 q^2) ((1/2 (P1-P2+2 P7-q . q))-mb^2 (P7)/(1/2 mb^2-1/2 q^2)),
LTensor[r, \[Mu]]->LTensor[p, \[Mu]]((1/2 (-P4+P5))/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(1/2 mb^2-1/2 q^2) ((1/2 (-P4+P5)+P6)-mb^2 (1/2 (-P4+P5))/(1/2 mb^2-1/2 q^2))}
/.{LTensor[\[Sigma], \[Mu],{r}]->LTensor[\[Sigma], \[Mu],\[Nu]] LTensor[r, \[Nu]],LTensor[\[Sigma], \[Mu],{l}]->LTensor[\[Sigma], \[Mu],\[Nu]] LTensor[l, \[Nu]]}/.{LTensor[l, \[Nu]]->LTensor[p, \[Nu]]((P7)/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Nu]]-LTensor[q, \[Nu]]) 1/(1/2 mb^2-1/2 q^2) ((1/2 (P1-P2+2 P7-q . q))-mb^2 (P7)/(1/2 mb^2-1/2 q^2)),
LTensor[r, \[Nu]]->LTensor[p, \[Nu]]((1/2 (-P4+P5))/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Nu]]-LTensor[q, \[Nu]]) 1/(1/2 mb^2-1/2 q^2) ((1/2 (-P4+P5)+P6)-mb^2 (1/2 (-P4+P5))/(1/2 mb^2-1/2 q^2))})
/.LTensor[q, \[Nu]]->LTensor[p, \[Nu]]-LTensor[k, \[Nu]]/.p-q->k//Contract,GordonIdentity->False]/.k->p-q,{LTensor[p, \[Mu]],LTensor[q, \[Mu]],LTensor[\[Gamma], \[Mu]]},FullSimplify]


ReduceToScalar["d",pAmp_]:=Collect[FermionLineExpand[(pAmp /.{SLTensor[l, \[Mu]]->LTensor[p, \[Mu]]((P7)/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(1/2 mb^2-1/2 q^2) ((1/2 (P1-P2+2 P7-q . q))-mb^2 (P7)/(1/2 mb^2-1/2 q^2)),
LTensor[r, \[Mu]]->LTensor[p, \[Mu]]((1/2 (P11-P4-2 P6))/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(1/2 mb^2-1/2 q^2) (((P11-P4)/2)-mb^2 (1/2 (P11-P4-2 P6))/(1/2 mb^2-1/2 q^2))}
/.{LTensor[\[Sigma], \[Mu],{r}]->LTensor[\[Sigma], \[Mu],\[Nu]] LTensor[r, \[Nu]],LTensor[\[Sigma], \[Mu],{l}]->LTensor[\[Sigma], \[Mu],\[Nu]] LTensor[l, \[Nu]]}/.{LTensor[l, \[Nu]]->LTensor[p, \[Nu]]((P7)/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Nu]]-LTensor[q, \[Nu]]) 1/(1/2 mb^2-1/2 q^2) ((1/2 (P1-P2+2 P7-q . q))-mb^2 (P7)/(1/2 mb^2-1/2 q^2)),
LTensor[r, \[Nu]]->LTensor[p, \[Nu]]((1/2 (P11-P4-2 P6))/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Nu]]-LTensor[q, \[Nu]]) 1/(1/2 mb^2-1/2 q^2) (((P11-P4)/2)-mb^2 (1/2 (P11-P4-2 P6))/(1/2 mb^2-1/2 q^2))})
/.LTensor[q, \[Nu]]->LTensor[p, \[Nu]]-LTensor[k, \[Nu]]/.p-q->k//Contract,GordonIdentity->False]/.k->p-q,{LTensor[p, \[Mu]],LTensor[q, \[Mu]],LTensor[\[Gamma], \[Mu]]},FullSimplify]


ReduceToScalar["e",pAmp_]:=Collect[FermionLineExpand[(pAmp /.{LTensor[l, \[Mu]]->LTensor[p, \[Mu]](P7/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(1/2 mb^2-1/2 q^2) (P7+1/2 (P1-P2-q^2)-mb^2 P7/(1/2 mb^2-1/2 q^2)),
LTensor[r, \[Mu]]->LTensor[p, \[Mu]](P13/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(1/2 mb^2-1/2 q^2) (P13+1/2 (P12-P3-P1+P2)-mb^2 P13/(1/2 mb^2-1/2 q^2))}
/.{LTensor[\[Sigma], \[Mu],{r}]->LTensor[\[Sigma], \[Mu],\[Nu]] LTensor[r, \[Nu]],LTensor[\[Sigma], \[Mu],{l}]->LTensor[\[Sigma], \[Mu],\[Nu]] LTensor[l, \[Nu]]}/.{LTensor[l, \[Nu]]->LTensor[p, \[Nu]](P7/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Nu]]-LTensor[q, \[Nu]]) 1/(1/2 mb^2-1/2 q^2) (P7+1/2 (P1-P2-q^2)-mb^2 P7/(1/2 mb^2-1/2 q^2)),
LTensor[r, \[Nu]]->LTensor[p, \[Nu]](P13/(1/2 mb^2-1/2 q^2))+(LTensor[p, \[Nu]]-LTensor[q, \[Nu]]) 1/(1/2 mb^2-1/2 q^2) (P13+1/2 (P12-P3-P1+P2)-mb^2 P13/(1/2 mb^2-1/2 q^2))})
/.LTensor[q, \[Nu]]->LTensor[p, \[Nu]]-LTensor[k, \[Nu]]/.p-q->k//Contract,GordonIdentity->False]/.k->p-q,{LTensor[p, \[Mu]],LTensor[q, \[Mu]],LTensor[\[Gamma], \[Mu]]},FullSimplify]


(* ::Subsection:: *)
(*Tensor Reductions*)


ReduceToScalar["a",pAmp_]:=FermionLineExpand[Collect[FermionLineExpand[pAmp/.{LDot[DiracG,r_]->LTensor[DiracG,\[Nu]]LTensor[r,\[Nu]]}/.{HoldPattern[LTensor[DiracS, List[e_],List[f_]]]->LTensor[DiracS,\[Lambda],\[Rho]]LTensor[e,\[Lambda]]LTensor[f,\[Rho]]}
/.{HoldPattern[LTensor[DiracS, \[Mu]_,List[a_]]]->LTensor[DiracS,\[Mu],\[Alpha]]LTensor[a,\[Alpha]],HoldPattern[LTensor[DiracS, List[c_],\[Mu]_]]->LTensor[DiracS,\[Beta],\[Mu]]LTensor[c,\[Beta]]}
/.{HoldPattern[LTensor[LeviCivitaE,\[Mu]_,\[Nu]_,List[a_],List[b_]]]->LTensor[LeviCivitaE,\[Mu],\[Nu],\[Alpha],\[Beta]]LTensor[a,\[Alpha]]LTensor[b,\[Beta]]}/.{LTensor[l, \[Mu]_]->LTensor[p, \[Mu]]((1/2 (-mcsq-P2+P7))/(s))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(s) ((1/2 (-2 mcsq-2 P2+P7+P9-qsq))-mbsq (1/2 (-mcsq-P2+P7))/(s)),
LTensor[r, \[Mu]_]->LTensor[p, \[Mu]]((1/2 (-P4+P5))/(s))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(s) ((1/2 (-mbsq-P4+P8))-mbsq (1/2 (-P4+P5))/(s))}/.LTensor[q, \[Nu]]->LTensor[p, \[Nu]]-LTensor[k, \[Nu]]
/.p-q->k//Contract,GordonIdentity->False]/.k->p-q,{LTensor[p, \[Mu]],LTensor[q, \[Mu]],LTensor[\[Gamma], \[Mu]]},Simplify]//Contract,GordonIdentity->False]/.{p . q->1/2 (mbsq+qsq),p . p->mbsq}/.{q . q->qsq}


ReduceToScalar["b",pAmp_]:=FermionLineExpand[Collect[FermionLineExpand[pAmp/.{LDot[DiracG,r_]->LTensor[DiracG,\[Nu]]LTensor[r,\[Nu]]}/.{HoldPattern[LTensor[DiracS, List[e_],List[f_]]]->LTensor[DiracS,\[Lambda],\[Rho]]LTensor[e,\[Lambda]]LTensor[f,\[Rho]]}
/.{HoldPattern[LTensor[DiracS, \[Mu]_,List[a_]]]->LTensor[DiracS,\[Mu],\[Kappa]]LTensor[a,\[Kappa]],HoldPattern[LTensor[DiracS, List[c_],\[Mu]_]]->LTensor[DiracS,\[Beta],\[Mu]]LTensor[c,\[Beta]]}
/.{HoldPattern[LTensor[LeviCivitaE,\[Mu]_,\[Nu]_,List[a_],List[b_]]]->LTensor[LeviCivitaE,\[Mu],\[Nu],\[Delta],\[Eta]]LTensor[a,\[Delta]]LTensor[b,\[Eta]]}/.{LTensor[l, \[Mu]_]->LTensor[p, \[Mu]]((1/2 (-mcsq-P2+P7))/(s))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(s) ((1/2 (-2 mcsq-2 P2+P7+P9-qsq))-mbsq (1/2 (-mcsq-P2+P7))/(s)),
LTensor[r, \[Mu]_]->LTensor[p, \[Mu]]((1/2 (mbsq+P10-P4))/(s))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(s) (((P11-P4)/2)-mbsq (1/2 (mbsq+P10-P4))/(s))}/.LTensor[q, \[Nu]_]->LTensor[p, \[Nu]]-LTensor[k, \[Nu]]
/.p-q->k//Contract,GordonIdentity->False]/.k->p-q,{LTensor[p, \[Mu]],LTensor[q, \[Mu]],LTensor[\[Gamma], \[Mu]]},Simplify]//Contract,GordonIdentity->False]/.{p . q->1/2 (mbsq+qsq),p . p->mbsq}/.{q . q->qsq}


ReduceToScalar["c",pAmp_]:=FermionLineExpand[Collect[FermionLineExpand[pAmp/.{LDot[DiracG,r_]->LTensor[DiracG,\[Nu]]LTensor[r,\[Nu]]}/.{HoldPattern[LTensor[DiracS, List[e_],List[f_]]]->LTensor[DiracS,\[Lambda],\[Rho]]LTensor[e,\[Lambda]]LTensor[f,\[Rho]]}
/.{HoldPattern[LTensor[DiracS, \[Mu]_,List[a_]]]->LTensor[DiracS,\[Mu],\[Alpha]]LTensor[a,\[Alpha]],HoldPattern[LTensor[DiracS, List[c_],\[Mu]_]]->LTensor[DiracS,\[Beta],\[Mu]]LTensor[c,\[Beta]]}
/.{HoldPattern[LTensor[LeviCivitaE,\[Mu]_,\[Nu]_,List[a_],List[b_]]]->LTensor[LeviCivitaE,\[Mu],\[Nu],\[Alpha],\[Beta]]LTensor[a,\[Alpha]]LTensor[b,\[Beta]]}/.{LTensor[l, \[Mu]_]->LTensor[p, \[Mu]]((1/2 (-mcsq-P2+P7))/(s))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(s) ((1/2 (-mcsq+P1-2 P2+P7-qsq))-mbsq (1/2 (-mcsq-P2+P7))/(s)),
LTensor[r, \[Mu]_]->LTensor[p, \[Mu]]((1/2 (-P4+P5))/(s))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(s) ((1/2 (-2 P4+P5+P6-qsq))-mbsq (1/2 (-P4+P5))/(s))}/.LTensor[q, \[Nu]]->LTensor[p, \[Nu]]-LTensor[k, \[Nu]]
/.p-q->k//Contract,GordonIdentity->False]/.k->p-q,{LTensor[p, \[Mu]],LTensor[q, \[Mu]],LTensor[\[Gamma], \[Mu]]},Simplify]//Contract,GordonIdentity->False]/.{p . q->1/2 (mbsq+qsq),p . p->mbsq}/.{q . q->qsq}


ReduceToScalar["d",pAmp_]:=FermionLineExpand[Collect[FermionLineExpand[pAmp/.{LDot[DiracG,r_]->LTensor[DiracG,\[Nu]]LTensor[r,\[Nu]]}/.{HoldPattern[LTensor[DiracS, List[e_],List[f_]]]->LTensor[DiracS,\[Lambda],\[Rho]]LTensor[e,\[Lambda]]LTensor[f,\[Rho]]}
/.{HoldPattern[LTensor[DiracS, \[Mu]_,List[a_]]]->LTensor[DiracS,\[Mu],\[Alpha]]LTensor[a,\[Alpha]],HoldPattern[LTensor[DiracS, List[c_],\[Mu]_]]->LTensor[DiracS,\[Beta],\[Mu]]LTensor[c,\[Beta]]}
/.{HoldPattern[LTensor[LeviCivitaE,\[Mu]_,\[Nu]_,List[a_],List[b_]]]->LTensor[LeviCivitaE,\[Mu],\[Nu],\[Delta],\[Eta]]LTensor[a,\[Delta]]LTensor[b,\[Eta]]}/.{LTensor[l, \[Mu]_]->LTensor[p, \[Mu]]((1/2 (-mcsq-P2+P7))/(s))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(s) ((1/2 (-mcsq+P1-2 P2+P7-qsq))-mbsq (1/2 (-mcsq-P2+P7))/(s)),
LTensor[r, \[Mu]_]->LTensor[p, \[Mu]]((1/2 (P11-P6+qsq))/(s))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(s) (((P11-P4)/2)-mbsq (1/2 (P11-P6+qsq))/(s))}/.LTensor[q, \[Nu]_]->LTensor[p, \[Nu]]-LTensor[k, \[Nu]]
/.p-q->k//Contract,GordonIdentity->False]/.k->p-q,{LTensor[p, \[Mu]],LTensor[q, \[Mu]],LTensor[\[Gamma], \[Mu]]},Simplify]//Contract,GordonIdentity->False]/.{p . q->1/2 (mbsq+qsq),p . p->mbsq}/.{q . q->qsq}


ReduceToScalar["e",pAmp_]:=FermionLineExpand[
Collect[
FermionLineExpand[
pAmp/.{LDot[DiracG,r_]->LTensor[DiracG,\[Nu]]LTensor[r,\[Nu]]}
/.{HoldPattern[LTensor[DiracS, List[e_],List[f_]]]->LTensor[DiracS,\[Lambda],\[Rho]]LTensor[e,\[Lambda]]LTensor[f,\[Rho]]}
/.{
HoldPattern[LTensor[DiracS, \[Mu]_,List[a_]]]->LTensor[DiracS,\[Mu],\[Alpha]]LTensor[a,\[Alpha]],
HoldPattern[LTensor[DiracS, List[c_],\[Mu]_]]->LTensor[DiracS,\[Beta],\[Mu]]LTensor[c,\[Beta]]
}
/.{
HoldPattern[LTensor[LeviCivitaE,\[Mu]_,\[Nu]_,List[a_],List[b_]]]->LTensor[LeviCivitaE,\[Mu],\[Nu],\[Alpha],\[Beta]]LTensor[a,\[Alpha]]LTensor[b,\[Beta]]
}
/.{
LTensor[l, \[Mu]_]->LTensor[p, \[Mu]]((1/2 (-P2+P7))/(s))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(s) ((1/2 (P1-2 P2+P7-qsq))-mbsq (1/2 (-P2+P7))/(s)),
LTensor[r, \[Mu]_]->LTensor[p, \[Mu]](((P13-P4)/2)/(s))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(s) ((1/2 (-P1+P12+P13+P2-P3-P4))-mbsq ((P13-P4)/2)/(s))
}
/.LTensor[q, \[Nu]]->LTensor[p, \[Nu]]-LTensor[k, \[Nu]]
/.p-q->k//Contract,GordonIdentity->False]/.k->p-q,{LTensor[p, \[Mu]],LTensor[q, \[Mu]],LTensor[\[Gamma], \[Mu]]},Simplify]
//Contract,GordonIdentity->False]/.{p . q->1/2 (mbsq+qsq),p . p->mbsq}/.{q . q->qsq}


(* ::Section:: *)
(*Appendix*)


(* ::Subsection:: *)
(*Generate Tensor Reduction Rules*)


(* ::Text:: *)
(*Once evaluated, a general tensor integral, I^{mu}=A l^{mu} or I^{mu}=B r^{mu}, can be expressed as *)
(*I^{mu}=p^{mu} I_p + (p^{mu}-q^{mu}) I_{pq}*)
(*as this is a complete linearly independent set of external momenta. *)
(**)
(*Below, we determine the value of p_{mu} I^{mu} *)


FullSimplify[Contract[LTensor[p, \[Mu]]((LTensor[p, \[Mu]]-LTensor[q, \[Mu]])Ipq+LTensor[p, \[Mu]]Ip)]/.{p . p->mb^2,(p-q) . (p-q)->ms^2,p . q->1/2 (mb^2-ms^2+q^2)}]/.ms^2->0


(* ::Text:: *)
(*and (p - q) _ {mu} I^{mu}*)


Simplify[Collect[FullSimplify[Contract[(LTensor[p, \[Mu]]-LTensor[q, \[Mu]])((LTensor[p, \[Mu]]-LTensor[q, \[Mu]])Ipq+LTensor[p, \[Mu]]Ip)]/.{p . p->mb^2,(p-q) . (p-q)->ms^2}]/.{p . q->1/2 (mb^2-ms^2+q . q)}/.{ms^2->0,q . q->q^2},{ILpq,ILp}]]


(* ::Text:: *)
(*In following calculations we shall set t=1/2 (mb^2-q^2) for simplicity, so*)
(*p_{mu}I^{mu}=mbsq I_p +t I_{pq} and (p-q)_{mu} I^{mu}=t I_p.*)
(**)
(*This gives us*)
(*1.  If I^{mu} = A l^{mu}:*)
(*A l.p = mbsq I_p +t I_{pq} and A l.(p-q) = t I_p,*)
(*and so*)


Solve[l . p == Ip mb^2+Ipq t && l . (p-q)==Ip t,{Ip, Ipq} ]


Simplify[(Ip LTensor[p,\[Mu]] + Ipq LTensor[(p-q),\[Mu]])/.{Ip->-((-l . p+l . q)/t),Ipq->-((mb^2 l . p-t l . p-mb^2 l . q)/t^2)}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->P7+P9,p . r->1/2 (-mb^2-P4+P8),l . q->P9,
q . r->1/2 (-mb^2-P5+P8),p . q->1/2 (mb^2+q . q),p . p->mb^2}]


Simplify[((mb^2 P9-(2 P7+P9) q^2) Subscript[p, \[Mu]]+(mb^2 (P7-P9)+(P7+P9) q^2) Subscript[q, \[Mu]])/(2 t^2)-((-mb^2 P7+(2 P7+P9) t) Subscript[p, \[Mu]]+(mb^2 P7-(P7+P9) t) Subscript[q, \[Mu]])/t^2]/.t->1/2(mb^2-q^2)


(* ::Text:: *)
(*i.e. in our replacement rule we can put l^{mu}-> l.(p-q)/t p^{mu} + (t l.p -mbsq l.(p-q))/t^2 (p-q)^{mu}.*)
(**)
(*2. If I^{mu}=B r^{mu}*)
(*B r.p = mbsq I_p + t I_{pq} and B r.(p-q)=t I_p,*)
(*and so*)


Solve[ r . p == Ip mb^2+ Ipq t && r . (p-q)==Ip t,{Ip, Ipq}]


(* ::Text:: *)
(*i.e. in our replacement rule we can put r^{mu}-> r.(p-q)/t p^{mu} + (t r.p -mbsq r.(p-q))/t^2 (p-q)^{mu}.*)
(**)
(*All we have left to do, then, is to find the values of (p-q).l, p.l, (p-q).r and p.r for each type of diagram. Happily, we've already done most of the work for this in Tensor_Integrals.m*)
(**)


Simplify[(Ip LTensor[p,\[Mu]] + Ipq LTensor[(p-q),\[Mu]])/.{Ip->-((-p . r+q . r)/t),Ipq->-((mb^2 p . r-t p . r-mb^2 q . r)/t^2)}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-mcsq+P1-2 P2+P7-qsq),
p . r->1/2 (-P1+P12+P13+P2-P3-P4),l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P1+P12+P2-P3),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


FullSimplify[(-((mb^2 (mbsq+P5-P8)+(-mbsq-2 P4+P5+P8) q^2) Subscript[p, \[Mu]])+(mb^2 (mbsq-P4+2 P5-P8)-(mbsq+P4-P8) q^2) Subscript[q, \[Mu]])/(4 t^2)-((mb^2 (-P13+P4)+(-P1+P12+2 P13+P2-P3-2 P4) t) Subscript[p, \[Mu]]+(mb^2 (P13-P4)+(P1-P12-P13-P2+P3+P4) t) Subscript[q, \[Mu]])/(2 t^2)]/.t->1/2(mb^2-q^2)/.mbsq->mb^2


(* ::Subsubsection:: *)
(*Diagram a*)


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->P7+P9,p . r->1/2 (-mb^2-P4+P8),l . q->P9,
q . r->1/2 (-mb^2-P5+P8),p . q->1/2 (mb^2+q . q),p . p->mb^2}]


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-2 mcsq-2 P2+P7+P9-qsq),
p . r->1/2 (-mbsq-P4+P8),l . q->1/2 (-mcsq-P2+P9-qsq),q . r->1/2 (-mbsq-P5+P8),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram b*)


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->P7+P9,p . r->(P11-P4)/2,l . q->P9,q . r->1/2 (-mb^2-P10+P11),
p . q->1/2 (mb^2+q . q),p . p->mb^2}]


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-2 mcsq-2 P2+P7+P9-qsq),
p . r->(P11-P4)/2,l . q->1/2 (-mcsq-P2+P9-qsq),q . r->1/2 (-mbsq-P10+P11),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram c*)


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (P1-P2+2 P7-q . q),
p . r->1/2 (-P4+P5+2 P6),l . q->1/2 (P1-P2-q . q),q . r->P6,p . q->1/2 (mb^2+q . q),p . p->mb^2}]


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-mcsq+P1-2 P2+P7-qsq),
p . r->1/2 (-2 P4+P5+P6-qsq),l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P4+P6-qsq),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram d*)


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P1+P12-P4-2 P6),l . p->1/2 (P1-P2+2 P7-q . q),
p . r->(P11-P4)/2,l . q->1/2 (P1-P2-q . q),q . r->P6,p . q->1/2 (mb^2+q . q),p . p->mb^2}]


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P1+P12-P6+qsq),l . p->1/2 (-mcsq+P1-2 P2+P7-qsq),
p . r->(P11-P4)/2,l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P4+P6-qsq),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram e*)


FullSimplify[{l . (p-q),p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (P1-2 P2+P7-qsq),
p . r->1/2 (-P1+P12+P13+P2-P3-P4),l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P1+P12+P2-P3),p . p->mbsq,p . q->(mbsq+qsq)/2,q . q->qsq}]


(* ::Subsection:: *)
(*Testing*)


pAmpE0i=((-2+\[ScriptD]) (2 (-2+\[ScriptD]) P13 (P2+P3-P4)+2 (-2+\[ScriptD]) (P2-P4) P7-8 mc^2 (P13+P7)) \[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Gamma], \[Mu]],\[DoubleStruckCapitalP]L,\[ScriptU][p,mb]\[RightAngleBracket])/(mb^2 P2 P3^2 P4)+
1/(mb^2 P2 P3^2 P4) (-2+\[ScriptD]) (I (-2+\[ScriptD]) mb (P2-P4) \[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Sigma], \[Mu],{l}],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket]+I (-2+\[ScriptD]) mb (P2+P3-P4) \[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Sigma], \[Mu],{r}],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket]-
4 I mb mc^2 (\[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Sigma], \[Mu],{l}],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket]+\[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Sigma], \[Mu],{r}],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket]))+((-2+\[ScriptD]) (-4 mc^2+(-2+\[ScriptD]) (P2-P4)) \[LeftAngleBracket]\[ScriptU][p-q,0],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket] LTensor[l, \[Mu]])/(mb P2 P3^2 P4)+
((-2+\[ScriptD]) (-4 mc^2+(-2+\[ScriptD]) (P2+P3-P4)) \[LeftAngleBracket]\[ScriptU][p-q,0],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket] LTensor[r, \[Mu]])/(mb P2 P3^2 P4)


ReduceToScalar["e",pAmpE0i]


(* ::Section::Closed:: *)
(*Appendix 2*)


(* ::Subsection:: *)
(*Generate Tensor Reduction Rules*)


(* ::Text:: *)
(*Once evaluated, a general tensor integral, I^{mu}=A l^{mu} or I^{mu}=B r^{mu}, can be expressed as *)
(*I^{mu}=p^{mu} I_p*)
(*as this is a complete linearly independent set of external momenta. *)
(**)
(*Below, we determine the value of p_{mu} I^{mu} *)


FullSimplify[Contract[LTensor[p, \[Mu]](LTensor[p, \[Mu]]Ip)]/.{p . p->mb^2,(p-q) . (p-q)->ms^2,p . q->1/2 (mb^2-ms^2+q^2)}]/.ms^2->0


(* ::Text:: *)
(*and (p - q) _ {mu} I^{mu}*)


Simplify[Collect[FullSimplify[Contract[(LTensor[p, \[Mu]]-LTensor[q, \[Mu]])((LTensor[p, \[Mu]]-LTensor[q, \[Mu]])Ipq+LTensor[p, \[Mu]]Ip)]/.{p . p->mb^2,(p-q) . (p-q)->ms^2}]/.{p . q->1/2 (mb^2-ms^2+q . q)}/.{ms^2->0,q . q->q^2},{ILpq,ILp}]]


(* ::Text:: *)
(*In following calculations we shall set t=1/2 (mb^2-q^2) for simplicity, so*)
(*p_{mu}I^{mu}=mbsq I_p +t I_{pq} and (p-q)_{mu} I^{mu}=t I_p.*)
(**)
(*This gives us*)
(*1.  If I^{mu} = A l^{mu}:*)
(*A l.p = mbsq I_p +t I_{pq} and A l.(p-q) = t I_p,*)
(*and so*)


Solve[r . p == mbsq Ip,{Ip}]/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-2 mcsq-2 P2+P7+P9-qsq),
p . r->1/2 (-mbsq-P4+P8),l . q->1/2 (-mcsq-P2+P9-qsq),q . r->1/2 (-mbsq-P5+P8),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}


Simplify[(l . (p-q)/t LTensor[p,\[Mu]] + (t l . p -mbsq l . (p-q))/t^2 LTensor[(p-q),\[Mu]])/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->P7+P9,p . r->1/2 (-mb^2-P4+P8),l . q->P9,
q . r->1/2 (-mb^2-P5+P8),p . q->1/2 (mb^2+q . q),p . p->mb^2}]


(* ::Text:: *)
(*i.e. in our replacement rule we can put l^{mu}-> l.(p-q)/t p^{mu} + (t l.p -mbsq l.(p-q))/t^2 (p-q)^{mu}.*)
(**)
(*2. If I^{mu}=B r^{mu}*)
(*B r.p = mbsq I_p + t I_{pq} and B r.(p-q)=t I_p,*)
(*and so*)


Solve[ r . p == mbsq Ip +t Ipq &&  r . (p-q)==t Ip,{Ip, Ipq} ]


(* ::Text:: *)
(*i.e. in our replacement rule we can put r^{mu}-> r.(p-q)/t p^{mu} + (t r.p -mbsq r.(p-q))/t^2 (p-q)^{mu}.*)
(**)
(*All we have left to do, then, is to find the values of (p-q).l, p.l, (p-q).r and p.r for each type of diagram. Happily, we've already done most of the work for this in Tensor_Integrals.m*)
(**)


Simplify[r . p/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-mcsq+P1-2 P2+P7-qsq),
p . r->1/2 (-P1+P12+P13+P2-P3-P4),l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P1+P12+P2-P3),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram a*)


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->P7+P9,p . r->1/2 (-mb^2-P4+P8),l . q->P9,
q . r->1/2 (-mb^2-P5+P8),p . q->1/2 (mb^2+q . q),p . p->mb^2}]


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-2 mcsq-2 P2+P7+P9-qsq),
p . r->1/2 (-mbsq-P4+P8),l . q->1/2 (-mcsq-P2+P9-qsq),q . r->1/2 (-mbsq-P5+P8),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram b*)


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->P7+P9,p . r->(P11-P4)/2,l . q->P9,q . r->1/2 (-mb^2-P10+P11),
p . q->1/2 (mb^2+q . q),p . p->mb^2}]


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-2 mcsq-2 P2+P7+P9-qsq),
p . r->(P11-P4)/2,l . q->1/2 (-mcsq-P2+P9-qsq),q . r->1/2 (-mbsq-P10+P11),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram c*)


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (P1-P2+2 P7-q . q),
p . r->1/2 (-P4+P5+2 P6),l . q->1/2 (P1-P2-q . q),q . r->P6,p . q->1/2 (mb^2+q . q),p . p->mb^2}]


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-mcsq+P1-2 P2+P7-qsq),
p . r->1/2 (-2 P4+P5+P6-qsq),l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P4+P6-qsq),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram d*)


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P1+P12-P4-2 P6),l . p->1/2 (P1-P2+2 P7-q . q),
p . r->(P11-P4)/2,l . q->1/2 (P1-P2-q . q),q . r->P6,p . q->1/2 (mb^2+q . q),p . p->mb^2}]


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P1+P12-P6+qsq),l . p->1/2 (-mcsq+P1-2 P2+P7-qsq),
p . r->(P11-P4)/2,l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P4+P6-qsq),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram e*)


FullSimplify[{l . (p-q),p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (P1-2 P2+P7-qsq),
p . r->1/2 (-P1+P12+P13+P2-P3-P4),l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P1+P12+P2-P3),p . p->mbsq,p . q->(mbsq+qsq)/2,q . q->qsq}]


(* ::Subsection:: *)
(*Testing*)


pAmpE0i=((-2+\[ScriptD]) (2 (-2+\[ScriptD]) P13 (P2+P3-P4)+2 (-2+\[ScriptD]) (P2-P4) P7-8 mc^2 (P13+P7)) \[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Gamma], \[Mu]],\[DoubleStruckCapitalP]L,\[ScriptU][p,mb]\[RightAngleBracket])/(mb^2 P2 P3^2 P4)+
1/(mb^2 P2 P3^2 P4) (-2+\[ScriptD]) (I (-2+\[ScriptD]) mb (P2-P4) \[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Sigma], \[Mu],{l}],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket]+I (-2+\[ScriptD]) mb (P2+P3-P4) \[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Sigma], \[Mu],{r}],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket]-
4 I mb mc^2 (\[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Sigma], \[Mu],{l}],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket]+\[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Sigma], \[Mu],{r}],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket]))+((-2+\[ScriptD]) (-4 mc^2+(-2+\[ScriptD]) (P2-P4)) \[LeftAngleBracket]\[ScriptU][p-q,0],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket] LTensor[l, \[Mu]])/(mb P2 P3^2 P4)+
((-2+\[ScriptD]) (-4 mc^2+(-2+\[ScriptD]) (P2+P3-P4)) \[LeftAngleBracket]\[ScriptU][p-q,0],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket] LTensor[r, \[Mu]])/(mb P2 P3^2 P4)


ReduceToScalar["e",pAmpE0i]


(* ::Section:: *)
(*Appendix 3*)


(* ::Subsection:: *)
(*Generate Tensor Reduction Rules*)


(* ::Text:: *)
(*Once evaluated, a general tensor integral, I^{mu}=A l^{mu} or I^{mu}=B r^{mu}, can be expressed as *)
(*I^{mu}=p^{mu} I_p + q^{mu} I_{q}*)
(*as this is a complete linearly independent set of external momenta. *)
(**)
(*Below, we determine the value of p_{mu} I^{mu} *)


FullSimplify[Contract[LTensor[p, \[Mu]](LTensor[q, \[Mu]]Iq+LTensor[p, \[Mu]]Ip)]/.{p . p->mb^2,(p-q) . (p-q)->ms^2,p . q->1/2 (mb^2-ms^2+q^2)}]/.ms^2->0


(* ::Text:: *)
(*and (q) _ {mu} I^{mu}*)


Simplify[Collect[FullSimplify[Contract[LTensor[q, \[Mu]]((LTensor[q, \[Mu]])Iq+LTensor[p, \[Mu]]Ip)]/.{p . p->mb^2,(p-q) . (p-q)->ms^2}]/.{p . q->1/2 (mb^2-ms^2+q . q)}/.{ms^2->0,q . q->q^2},{ILpq,ILp}]]


Solve[l . p == Ip mb^2+1/2 Iq (mb^2+q^2) && l . (q)==Iq q^2+1/2 Ip (mb^2+q^2),{Ip, Iq} ]


Simplify[(Ip LTensor[p,\[Mu]] + Iq LTensor[(q),\[Mu]])/.{Ip->(2 (-2 q^2 l . p+mb^2 l . q+q^2 l . q))/(mb^2-q^2)^2,Iq->(2 (mb^2 l . p+q^2 l . p-2 mb^2 l . q))/(-mb^2+q^2)^2}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->P7+P9,p . r->1/2 (-mb^2-P4+P8),l . q->P9,
q . r->1/2 (-mb^2-P5+P8),p . q->1/2 (mb^2+q . q),p . p->mb^2}]/.(mb^2-q^2)->2t


(* ::Text:: *)
(*In following calculations we shall set t=1/2 (mb^2-q^2) for simplicity, so*)
(*p_{mu}I^{mu}=mbsq I_p +t I_{pq} and (p-q)_{mu} I^{mu}=t I_p.*)
(**)
(*This gives us*)
(*1.  If I^{mu} = A l^{mu}:*)
(*A l.p = mbsq I_p +t I_{pq} and A l.(p-q) = t I_p,*)
(*and so*)


Solve[r . p == Ip mb^2+1/2 Iq (mb^2+q^2) && r . (q)== Iq q^2+1/2 Ip (mb^2+q^2),{Ip, Iq} ]/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-2 mcsq-2 P2+P7+P9-qsq),
p . r->1/2 (-mbsq-P4+P8),l . q->1/2 (-mcsq-P2+P9-qsq),q . r->1/2 (-mbsq-P5+P8),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}/.{mcsq->mc^2,qsq->q^2}


Simplify[Ip Subscript[p, \[Mu]] + Iq Subscript[q, \[Mu]]/.{Ip->(2 (1/2 mb^2 (-mbsq-P5+P8)-(-mbsq-P4+P8) q^2+1/2 (-mbsq-P5+P8) q^2))/(mb^2-q^2)^2,Iq->(2 (1/2 mb^2 (-mbsq-P4+P8)-mb^2 (-mbsq-P5+P8)+1/2 (-mbsq-P4+P8) q^2))/(-mb^2+q^2)^2}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-2 mcsq-2 P2+P7+P9-qsq),
p . r->1/2 (-mbsq-P4+P8),l . q->1/2 (-mcsq-P2+P9-qsq),q . r->1/2 (-mbsq-P5+P8),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}/.{mcsq->mc^2,qsq->q^2}]/.mb^2-q^2->2t


Collect[FullSimplify[Simplify[LTensor[p, \[Mu]]((1/2 (-z mbsq-P2+P7))/(t))+(LTensor[p, \[Mu]]-LTensor[q, \[Mu]]) 1/(t) ((1/2 (-2 z mbsq-2 P2+P7+P9-s mbsq))-mbsq ((1/2 (-z mbsq-P2+P7))/(t)))/.s->q^2/mbsq/.z->mc^2/mbsq/.mbsq->mb^2/.t->1/2(mb^2-q^2)]],{Subscript[p, \[Mu]],Subscript[q, \[Mu]]}]


(* ::Input:: *)
(*Simplify[(2 ((mb^2 P9-(2 P7+P9) q^2) Subscript[p, \[Mu]]+(mb^2 (P7-P9)+(P7+P9) q^2) Subscript[q, \[Mu]]))/(mb^2-q^2)^2/.{mb^2->mbsq,q^2->s mbsq}]*)


Simplify[(-((mb^2 (mbsq+P5-P8)+(-mbsq-2 P4+P5+P8) q^2) Subscript[p, \[Mu]])+(mb^2 (mbsq-P4+2 P5-P8)-(mbsq+P4-P8) q^2) Subscript[q, \[Mu]])/(mb^2-q^2)^2/.{mb^2->mbsq,q^2->s mbsq}]


Simplify[(l . (p-q)/t LTensor[p,\[Mu]] + (t l . p -mbsq l . (p-q))/t^2 LTensor[(p-q),\[Mu]])/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->P7+P9,p . r->1/2 (-mb^2-P4+P8),l . q->P9,
q . r->1/2 (-mb^2-P5+P8),p . q->1/2 (mb^2+q . q),p . p->mb^2}]


(* ::Text:: *)
(*i.e. in our replacement rule we can put l^{mu}-> l.(p-q)/t p^{mu} + (t l.p -mbsq l.(p-q))/t^2 (p-q)^{mu}.*)
(**)
(*2. If I^{mu}=B r^{mu}*)
(*B r.p = mbsq I_p + t I_{pq} and B r.(p-q)=t I_p,*)
(*and so*)


Solve[ r . p == mbsq Ip +t Ipq &&  r . (p-q)==t Ip,{Ip, Ipq} ]


(* ::Text:: *)
(*i.e. in our replacement rule we can put r^{mu}-> r.(p-q)/t p^{mu} + (t r.p -mbsq r.(p-q))/t^2 (p-q)^{mu}.*)
(**)
(*All we have left to do, then, is to find the values of (p-q).l, p.l, (p-q).r and p.r for each type of diagram. Happily, we've already done most of the work for this in Tensor_Integrals.m*)
(**)


Simplify[r . p/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-mcsq+P1-2 P2+P7-qsq),
p . r->1/2 (-P1+P12+P13+P2-P3-P4),l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P1+P12+P2-P3),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram a*)


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->P7+P9,p . r->1/2 (-mb^2-P4+P8),l . q->P9,
q . r->1/2 (-mb^2-P5+P8),p . q->1/2 (mb^2+q . q),p . p->mb^2}]


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-2 mcsq-2 P2+P7+P9-qsq),
p . r->1/2 (-mbsq-P4+P8),l . q->1/2 (-mcsq-P2+P9-qsq),q . r->1/2 (-mbsq-P5+P8),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram b*)


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->P7+P9,p . r->(P11-P4)/2,l . q->P9,q . r->1/2 (-mb^2-P10+P11),
p . q->1/2 (mb^2+q . q),p . p->mb^2}]


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-2 mcsq-2 P2+P7+P9-qsq),
p . r->(P11-P4)/2,l . q->1/2 (-mcsq-P2+P9-qsq),q . r->1/2 (-mbsq-P10+P11),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram c*)


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (P1-P2+2 P7-q . q),
p . r->1/2 (-P4+P5+2 P6),l . q->1/2 (P1-P2-q . q),q . r->P6,p . q->1/2 (mb^2+q . q),p . p->mb^2}]


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-mcsq+P1-2 P2+P7-qsq),
p . r->1/2 (-2 P4+P5+P6-qsq),l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P4+P6-qsq),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram d*)


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P1+P12-P4-2 P6),l . p->1/2 (P1-P2+2 P7-q . q),
p . r->(P11-P4)/2,l . q->1/2 (P1-P2-q . q),q . r->P6,p . q->1/2 (mb^2+q . q),p . p->mb^2}]


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P1+P12-P6+qsq),l . p->1/2 (-mcsq+P1-2 P2+P7-qsq),
p . r->(P11-P4)/2,l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P4+P6-qsq),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram e*)


FullSimplify[{l . (p-q),p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (P1-2 P2+P7-qsq),
p . r->1/2 (-P1+P12+P13+P2-P3-P4),l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P1+P12+P2-P3),p . p->mbsq,p . q->(mbsq+qsq)/2,q . q->qsq}]


(* ::Subsection:: *)
(*Testing*)


pAmpE0i=((-2+\[ScriptD]) (2 (-2+\[ScriptD]) P13 (P2+P3-P4)+2 (-2+\[ScriptD]) (P2-P4) P7-8 mc^2 (P13+P7)) \[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Gamma], \[Mu]],\[DoubleStruckCapitalP]L,\[ScriptU][p,mb]\[RightAngleBracket])/(mb^2 P2 P3^2 P4)+
1/(mb^2 P2 P3^2 P4) (-2+\[ScriptD]) (I (-2+\[ScriptD]) mb (P2-P4) \[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Sigma], \[Mu],{l}],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket]+I (-2+\[ScriptD]) mb (P2+P3-P4) \[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Sigma], \[Mu],{r}],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket]-
4 I mb mc^2 (\[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Sigma], \[Mu],{l}],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket]+\[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Sigma], \[Mu],{r}],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket]))+((-2+\[ScriptD]) (-4 mc^2+(-2+\[ScriptD]) (P2-P4)) \[LeftAngleBracket]\[ScriptU][p-q,0],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket] LTensor[l, \[Mu]])/(mb P2 P3^2 P4)+
((-2+\[ScriptD]) (-4 mc^2+(-2+\[ScriptD]) (P2+P3-P4)) \[LeftAngleBracket]\[ScriptU][p-q,0],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket] LTensor[r, \[Mu]])/(mb P2 P3^2 P4)


ReduceToScalar["e",pAmpE0i]


(* ::Section:: *)
(*Appendix 4*)


(* ::Subsection:: *)
(*Generate Tensor Reduction Rules*)


(* ::Text:: *)
(*Once evaluated, a general tensor integral, I^{mu}=A l^{mu} or I^{mu}=B r^{mu}, can be expressed as *)
(*I^{mu}=(p^{mu}-q^{mu}) I_{pq}*)
(*as this is a complete linearly independent set of external momenta. *)
(**)
(*Below, we determine the value of (p - q) _ {mu} I^{mu}*)


Simplify[Collect[FullSimplify[Contract[(LTensor[p, \[Mu]]-LTensor[q, \[Mu]])((LTensor[p, \[Mu]]-LTensor[q, \[Mu]])Ipq)]/.{p . p->mb^2,(p-q) . (p-q)->ms^2}]/.{p . q->1/2 (mb^2-ms^2+q . q)}/.{ms^2->0,q . q->q^2},{ILpq,ILp}]]


(* ::Text:: *)
(*In following calculations we shall set t=1/2 (mb^2-q^2) for simplicity, so*)
(*p_{mu}I^{mu}=mbsq I_p +t I_{pq} and (p-q)_{mu} I^{mu}=t I_p.*)
(**)
(*This gives us*)
(*1.  If I^{mu} = A l^{mu}:*)
(*A l.p = mbsq I_p +t I_{pq} and A l.(p-q) = t I_p,*)
(*and so*)


Solve[l . p == Ip mb^2+1/2 Ipq (mb^2-q^2) && l . (p-q)==1/2 Ip (mb^2-q^2),{Ip, Ipq} ]


Simplify[(Ip LTensor[p,\[Mu]] + Ipq LTensor[(p-q),\[Mu]])/.{Ip->(2 (l . p-l . q))/(mb^2-q^2),Ipq->-((2 (mb^2 l . p+q^2 l . p-2 mb^2 l . q))/(mb^2-q^2)^2)}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->P7+P9,p . r->1/2 (-mb^2-P4+P8),l . q->P9,
q . r->1/2 (-mb^2-P5+P8),p . q->1/2 (mb^2+q . q),p . p->mb^2}]


(* ::Text:: *)
(*i.e. in our replacement rule we can put l^{mu}-> l.(p-q)/t p^{mu} + (t l.p -mbsq l.(p-q))/t^2 (p-q)^{mu}.*)
(**)
(*2. If I^{mu}=B r^{mu}*)
(*B r.p = mbsq I_p + t I_{pq} and B r.(p-q)=t I_p,*)
(*and so*)


Solve[ r . p == mbsq Ip +t Ipq &&  r . (p-q)==t Ip,{Ip, Ipq} ]


(* ::Text:: *)
(*i.e. in our replacement rule we can put r^{mu}-> r.(p-q)/t p^{mu} + (t r.p -mbsq r.(p-q))/t^2 (p-q)^{mu}.*)
(**)
(*All we have left to do, then, is to find the values of (p-q).l, p.l, (p-q).r and p.r for each type of diagram. Happily, we've already done most of the work for this in Tensor_Integrals.m*)
(**)


Simplify[r . p/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-mcsq+P1-2 P2+P7-qsq),
p . r->1/2 (-P1+P12+P13+P2-P3-P4),l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P1+P12+P2-P3),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram a*)


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->P7+P9,p . r->1/2 (-mb^2-P4+P8),l . q->P9,
q . r->1/2 (-mb^2-P5+P8),p . q->1/2 (mb^2+q . q),p . p->mb^2}]


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-2 mcsq-2 P2+P7+P9-qsq),
p . r->1/2 (-mbsq-P4+P8),l . q->1/2 (-mcsq-P2+P9-qsq),q . r->1/2 (-mbsq-P5+P8),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram b*)


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->P7+P9,p . r->(P11-P4)/2,l . q->P9,q . r->1/2 (-mb^2-P10+P11),
p . q->1/2 (mb^2+q . q),p . p->mb^2}]


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-2 mcsq-2 P2+P7+P9-qsq),
p . r->(P11-P4)/2,l . q->1/2 (-mcsq-P2+P9-qsq),q . r->1/2 (-mbsq-P10+P11),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram c*)


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (P1-P2+2 P7-q . q),
p . r->1/2 (-P4+P5+2 P6),l . q->1/2 (P1-P2-q . q),q . r->P6,p . q->1/2 (mb^2+q . q),p . p->mb^2}]


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-mcsq+P1-2 P2+P7-qsq),
p . r->1/2 (-2 P4+P5+P6-qsq),l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P4+P6-qsq),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram d*)


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P1+P12-P4-2 P6),l . p->1/2 (P1-P2+2 P7-q . q),
p . r->(P11-P4)/2,l . q->1/2 (P1-P2-q . q),q . r->P6,p . q->1/2 (mb^2+q . q),p . p->mb^2}]


FullSimplify[{(p-q) . l,p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P1+P12-P6+qsq),l . p->1/2 (-mcsq+P1-2 P2+P7-qsq),
p . r->(P11-P4)/2,l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P4+P6-qsq),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Subsubsection:: *)
(*Diagram e*)


FullSimplify[{l . (p-q),p . l,(p-q) . r,p . r}/.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (P1-2 P2+P7-qsq),
p . r->1/2 (-P1+P12+P13+P2-P3-P4),l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P1+P12+P2-P3),p . p->mbsq,p . q->(mbsq+qsq)/2,q . q->qsq}]


(* ::Subsection:: *)
(*Testing*)


pAmpE0i=((-2+\[ScriptD]) (2 (-2+\[ScriptD]) P13 (P2+P3-P4)+2 (-2+\[ScriptD]) (P2-P4) P7-8 mc^2 (P13+P7)) \[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Gamma], \[Mu]],\[DoubleStruckCapitalP]L,\[ScriptU][p,mb]\[RightAngleBracket])/(mb^2 P2 P3^2 P4)+
1/(mb^2 P2 P3^2 P4) (-2+\[ScriptD]) (I (-2+\[ScriptD]) mb (P2-P4) \[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Sigma], \[Mu],{l}],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket]+I (-2+\[ScriptD]) mb (P2+P3-P4) \[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Sigma], \[Mu],{r}],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket]-
4 I mb mc^2 (\[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Sigma], \[Mu],{l}],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket]+\[LeftAngleBracket]\[ScriptU][p-q,0],LTensor[\[Sigma], \[Mu],{r}],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket]))+((-2+\[ScriptD]) (-4 mc^2+(-2+\[ScriptD]) (P2-P4)) \[LeftAngleBracket]\[ScriptU][p-q,0],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket] LTensor[l, \[Mu]])/(mb P2 P3^2 P4)+
((-2+\[ScriptD]) (-4 mc^2+(-2+\[ScriptD]) (P2+P3-P4)) \[LeftAngleBracket]\[ScriptU][p-q,0],\[DoubleStruckCapitalP]R,\[ScriptU][p,mb]\[RightAngleBracket] LTensor[r, \[Mu]])/(mb P2 P3^2 P4)


ReduceToScalar["e",pAmpE0i]
