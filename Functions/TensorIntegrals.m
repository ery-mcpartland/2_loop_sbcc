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
(*Five functions. One for each diagram; function applies Mathematica replacement rules to convert scalar products in the numerator of the integral into P_i basis (takes diagram type and amplitude to reduce as arguments). The rules were generated in the notebook Determine_Functions.nb*)


(* ::Section:: *)
(*Functions*)


(* ::Subsection:: *)
(*Initialisation*)


Needs["X`"]


(* ::Subsection:: *)
(*Propagator Replacements*)


PropagatorReplace["a",amp_]:=FullSimplify[amp /. {LDot[l,l]->mc^2+P2,LDot[l,r]->1/2 (-P2+P3-P4),
LDot[l,p]->1/2 (-2 mc^2-2 P2+P7+P9-q2),LDot[l,q]->1/2 (-mc^2-P2+P9-q2),LDot[r,r]->P4,LDot[p,r]->1/2 (-mb^2-P4+P8),
LDot[q,r]->1/2 (-mb^2-P5+P8),LDot[p,p]->mb^2,LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2}]


PropagatorReplace["b",amp_]:=FullSimplify[amp /. {LDot[l,l]->mc^2+P2,LDot[l,r]->1/2 (-P2+P3-P4),
LDot[l,p]->1/2 (-2 mc^2-2 P2+P7+P9-q2),LDot[l,q]->1/2 (-mc^2-P2+P9-q2),LDot[r,r]->P4,LDot[p,r]->(P11-P4)/2,
LDot[q,r]->1/2 (-mb^2-P10+P11),LDot[p,p]->mb^2,LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2}]


PropagatorReplace["c",amp_]:=FullSimplify[amp /. {LDot[l,l]->mc^2+P2,LDot[l,r]->1/2 (-P2+P3-P4),
LDot[l,p]->1/2 (-mc^2+P1-2 P2+P7-q2),LDot[l,q]->1/2 (P1-P2-q2),LDot[r,r]->P4,LDot[p,r]->1/2 (-2 P4+P5+P6-q2),
LDot[q,r]->1/2 (-P4+P6-q2),LDot[p,p]->mb^2,LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2}]


PropagatorReplace["d",amp_]:=FullSimplify[amp /.{LDot[l,l]->mc^2+P2,LDot[l,r]->1/2 (-P1+P12-P6+q2),
LDot[l,p]->1/2 (-mc^2+P1-2 P2+P7-q2),LDot[l,q]->1/2 (P1-P2-q2),LDot[r,r]->P4,LDot[p,r]->(P11-P4)/2,
LDot[q,r]->1/2 (-P4+P6-q2),LDot[p,p]->mb^2,LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2} ]


PropagatorReplace["e",amp_]:=FullSimplify[amp /.{LDot[l,l]->mc^2+P2,LDot[l,r]->1/2 (-P2+P3-P4),
LDot[l,p]->1/2 (-mc^2+P1-2 P2+P7-q2),LDot[l,q]->1/2 (P1-P2-q2),LDot[r,r]->P4,LDot[p,r]->1/2 (-P1+P12+P13+P2-P3-P4),
LDot[q,r]->1/2 (-P1+P12+P2-P3),LDot[p,p]->mb^2,LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2}]
