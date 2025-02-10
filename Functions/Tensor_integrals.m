(* ::Package:: *)

(* ::Title:: *)
(*Tensor Integrals*)


(* ::Text:: *)
(*Automated code to apply EoMs and to convert all scalars in terms of momenta into a basis of P_i propagators*)


(* ::Section:: *)
(*Function Descriptions*)


(* ::Subsection:: *)
(*Amplitude creation*)


(* ::Text:: *)
(*Creates amplitude and applies EoM. Takes two arguments - numerator without external propagators and denominator (denominator can be in terms of momenta or P_i*)


(* ::Subsection:: *)
(*Propagator Replacements*)


(* ::Text:: *)
(*Five functions. One for each diagram; function applies rules to convert scalar propagators in amplitude into P_i basis (takes diagram type and amplitude to reduce as arguments)*)


(* ::Section:: *)
(*Functions*)


(* ::Subsection:: *)
(*Initialisation*)


Needs["X`"]


(* ::Subsection:: *)
(*Amplitudes*)


CreateAmplitude[num_,denom_]:=FullSimplify[(\[LeftAngleBracket]\[ScriptU][p-q,0], num ,\[ScriptU][p,mb]\[RightAngleBracket]//FermionLineExpand)/denom]


(* ::Subsection:: *)
(*Propagator Replacements*)


PropagatorReplace["a",amp_]:=FullSimplify[amp /. {l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-2 mcsq-2 P2+P7+P9-qsq),
p . r->1/2 (-mbsq-P4+P8),l . q->1/2 (-mcsq-P2+P9-qsq),q . r->1/2 (-mbsq-P5+P8),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


PropagatorReplace["b",amp_]:=FullSimplify[amp /. {l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-2 mcsq-2 P2+P7+P9-qsq),
p . r->(P11-P4)/2,l . q->1/2 (-mcsq-P2+P9-qsq),q . r->1/2 (-mbsq-P10+P11),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


PropagatorReplace["c",amp_]:=FullSimplify[amp /. {l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-mcsq+P1-2 P2+P7-qsq),
p . r->1/2 (-2 P4+P5+P6-qsq),l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P4+P6-qsq),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


PropagatorReplace["d",amp_]:=FullSimplify[amp /. {l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P1+P12-P6+qsq),l . p->1/2 (-mcsq+P1-2 P2+P7-qsq),
p . r->(P11-P4)/2,l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P4+P6-qsq),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


PropagatorReplace["e",amp_]:=FullSimplify[amp /.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (P1-2 P2+P7-qsq),
p . r->1/2 (-P1+P12+P13+P2-P3-P4),l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P1+P12+P2-P3),p . p->mbsq,p . q->s,q . q->qsq}]


(* ::Subsection:: *)
(*Replacements*)


PropagatorReplace["a",amp_]:=FullSimplify[amp /. {l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->P7+P9,p . r->1/2 (-mb^2-P4+P8),
l . q->P9,q . r->1/2 (-mb^2-P5+P8),p . q->1/2 (mb^2+q . q),p . p->mb^2}]


PropagatorReplace["b",amp_]:=FullSimplify[amp /. {l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->P7+P9,p . r->(P11-P4)/2,l . q->P9,
q . r->1/2 (-mb^2-P10+P11),p . q->1/2 (mb^2+q . q),p . p->mb^2}]


PropagatorReplace["c",amp_]:=FullSimplify[amp /. {l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (P1-P2+2 P7-q . q),
p . r->1/2 (-P4+P5+2 P6),l . q->1/2 (P1-P2-q . q),q . r->P6,p . q->1/2 (mb^2+q . q),p . p->mb^2}]


PropagatorReplace["d",amp_]:=FullSimplify[amp /. {l . l->mc^2+P2,r . r->P4,l . r->1/2 (-P1+P12-P4-2 P6),l . p->1/2 (P1-P2+2 P7-q . q),
p . r->(P11-P4)/2,l . q->1/2 (P1-P2-q . q),q . r->P6,p . q->1/2 (mb^2+q . q),p . p->mb^2}]


PropagatorReplace["e",amp_]:=FullSimplify[amp /.{l . l->mcsq+P2,r . r->P4,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-mcsq+P1-2 P2+P7-qsq),
p . r->1/2 (-P1+P12+P13+P2-P3-P4),l . q->1/2 (P1-P2-qsq),q . r->1/2 (-P1+P12+P2-P3),p . q->(mbsq+qsq)/2,p . p->mbsq,q . q->qsq}]


(* ::Section:: *)
(*Appendix*)


(* ::Subsection:: *)
(*Generate Replacement rules*)


(* ::Subsubsection:: *)
(*Diagram a*)


Solve[P2==l . l-mcsq&&P3==(l+r) . (l+r)-mcsq&&P4==r . r&&P5==(r+p-q) . (r+p-q)&&P8==(r+p) . (r+p)&&P7==(l+p-q) . (l+p-q)&&
P9==(l+q) . (l+q)&&(p-q) . (p-q)==0&&(p . p)==mbsq&&q . q==qsq,{l . l,r . r,l . r,l . p,r . p,l . q,r . q,p . q,p . p,q . q}]


(* ::Subsubsection:: *)
(*Diagram b*)


Solve[P2==l . l-mcsq&&P3==(l+r) . (l+r)-mcsq&&P4==r . r&&P10==(r+p-q) . (r+p-q)-mbsq&&P11==(r+p) . (r+p)-mbsq&&
P7==(l+p-q) . (l+p-q)&&P9==(l+q) . (l+q)&&(p-q) . (p-q)==0&&(p . p)==mbsq&&q . q==qsq,{l . l,r . r,l . r,l . p,r . p,l . q,r . q,p . q,p . p,q . q}]


(* ::Subsubsection:: *)
(*Diagram c*)


Solve[P1==(l+q) . (l+q)-mcsq&&P2==l . l-mcsq&&P3==(l+r) . (l+r)-mcsq&&P4==r . r&&P5==(r+p-q) . (r+p-q)&&P6==(r+q) . (r+q)&&
P7==(l+p-q) . (l+p-q)&&(p-q) . (p-q)==0&&(p . p)==mbsq&&q . q==qsq,{l . l,r . r,l . r,l . p,r . p,l . q,r . q,p . q,p . p,q . q}]


(* ::Subsubsection:: *)
(*Diagram d*)


Solve[P1==(l+q) . (l+q)-mcsq&&P2==l . l-mcsq&&P12==(l+r+q) . (l+r+q)-mcsq&&P4==r . r&&P11==(r+p) . (r+p)-mbsq&&
P6==(r+q) . (r+q)&&P7==(l+p-q) . (l+p-q)&&(p-q) . (p-q)==0&&(p . p)==mbsq&&q . q==qsq,{l . l,r . r,l . r,l . p,r . p,l . q,r . q,p . q,p . p,q . q}]


(* ::Subsubsection:: *)
(*Diagram e*)


Solve[P1==(l+q) . (l+q)-mcsq&&P2==l . l-mcsq&&P3==(l+r) . (l+r)-mcsq&&P4==r . r&&P12==(l+r+q) . (l+r+q)-mcsq&&
P13==(r+p-q) . (r+p-q)&&P7==(l+p-q) . (l+p-q)&&(p-q) . (p-q)==0&&(p . p)==mbsq
&&q . q==qsq,{l . l,r . r,l . r,l . p,r . p,l . q,r . q,p . q,p . p,q . q}]


(* ::Subsection:: *)
(*Testing*)


numeratorE0I = FullSimplify[DiracMatrix[LTensor[\[Gamma], \[Alpha]],\[DoubleStruckCapitalP]L,\[Gamma] . (l+r)+mc \[DoubleStruckOne],LTensor[\[Gamma], \[Rho]],(\[Gamma] . l+mc \[DoubleStruckOne]),LTensor[\[Gamma], \[Rho]],\[Gamma] . (l+r)+mc \[DoubleStruckOne],LTensor[\[Gamma], \[Alpha]],\[DoubleStruckCapitalP]L,\[Gamma] . (p-q)+mb \[DoubleStruckOne],LTensor[\[Gamma], \[Mu]]]]


CreateAmplitude[numeratorE0I,P2 (P3)^2 P4 mb^2]


a = l . l + r . q


PropagatorReplace["e",CreateAmplitude[numeratorE0I,P2 (P3)^2 P4 mb^2]]
