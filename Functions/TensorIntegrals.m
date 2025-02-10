(* ::Package:: *)

(* ::Title:: *)
(*Tensor Integrals*)


(* ::Text:: *)
(*Automated code to convert all scalars in terms of momenta into a basis of P_i propagators*)


(* ::Section:: *)
(*Function Descriptions*)


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
(*Propagator Replacements*)


PropagatorReplace["a",amp_]:=FullSimplify[amp /. {l . l->mc^2+P2,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-2 mc^2-2 P2+P7+P9-q2),
l . q->1/2 (-mc^2-P2+P9-q2),r . r->P4,p . r->1/2 (-mb^2-P4+P8),q . r->1/2 (-mb^2-P5+P8),p . p->mb^2,p . q->1/2 (mb^2+q2),q . q->q2}]


PropagatorReplace["b",amp_]:=FullSimplify[amp /. {l . l->mc^2+P2,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-2 mc^2-2 P2+P7+P9-q2),
l . q->1/2 (-mc^2-P2+P9-q2),r . r->P4,p . r->(P11-P4)/2,q . r->1/2 (-mb^2-P10+P11),p . p->mb^2,p . q->1/2 (mb^2+q2),q . q->q2}]


PropagatorReplace["c",amp_]:=FullSimplify[amp /. {l . l->mc^2+P2,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-mc^2+P1-2 P2+P7-q2),
l . q->1/2 (P1-P2-q2),r . r->P4,p . r->1/2 (-2 P4+P5+P6-q2),q . r->1/2 (-P4+P6-q2),p . p->mb^2,p . q->1/2 (mb^2+q2),q . q->q2}]


PropagatorReplace["d",amp_]:=FullSimplify[amp /.{l . l->mc^2+P2,l . r->1/2 (-P1+P12-P6+q2),l . p->1/2 (-mc^2+P1-2 P2+P7-q2),
l . q->1/2 (P1-P2-q2),r . r->P4,p . r->(P11-P4)/2,q . r->1/2 (-P4+P6-q2),p . p->mb^2,p . q->1/2 (mb^2+q2),q . q->q2} ]


PropagatorReplace["e",amp_]:=FullSimplify[amp /.{l . l->mc^2+P2,l . r->1/2 (-P2+P3-P4),l . p->1/2 (-mc^2+P1-2 P2+P7-q2),
l . q->1/2 (P1-P2-q2),r . r->P4,p . r->1/2 (-P1+P12+P13+P2-P3-P4),q . r->1/2 (-P1+P12+P2-P3),p . p->mb^2,p . q->1/2 (mb^2+q2),q . q->q2}]


test["a",x_]:=4 x


test["b",x_]:=3 x
