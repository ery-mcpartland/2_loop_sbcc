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


PropagatorReplace["a",amp_]:=amp /. {LDot[l,l]->mc^2+P2,LDot[l,r]->1/2 (-P2+P3-P4),
LDot[l,p]->1/2 (-2 mc^2-2 P2+P7+P9-q2),LDot[l,q]->1/2 (-mc^2-P2+P9-q2),LDot[r,r]->P4,LDot[p,r]->1/2 (-mb^2-P4+P8),
LDot[q,r]->1/2 (-mb^2-P5+P8),LDot[p,p]->mb^2,LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2}


PropagatorReplace["ahat",amp_]:=amp /. {LDot[l,l]->P2hat,LDot[l,r]->1/2 (-P2hat+P3hat-P4),LDot[l,p]->1/2 (-2 P2hat+P7+P9-q2),
LDot[l,q]->1/2 (-P2hat+P9-q2),LDot[r,r]->P4,LDot[p,r]->1/2 (-mb^2-P4+P8),LDot[q,r]->1/2 (-mb^2-P5+P8),LDot[p,p]->mb^2,
LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2}


PropagatorReplace["amb",amp_]:=amp /. {LDot[l,l]->mb^2+P2mb,LDot[l,r]->1/2 (-P2mb+P3mb-P4),
LDot[l,p]->1/2 (-2 mb^2-2 P2mb+P7+P9-q2),LDot[l,q]->1/2 (-mb^2-P2mb+P9-q2),LDot[r,r]->P4,LDot[p,r]->1/2 (-mb^2-P4+P8),
LDot[q,r]->1/2 (-mb^2-P5+P8),LDot[p,p]->mb^2,LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2}


PropagatorReplace["b",amp_]:=amp /. {LDot[l,l]->mc^2+P2,LDot[l,r]->1/2 (-P2+P3-P4),
LDot[l,p]->1/2 (-2 mc^2-2 P2+P7+P9-q2),LDot[l,q]->1/2 (-mc^2-P2+P9-q2),LDot[r,r]->P4,LDot[p,r]->(P11-P4)/2,
LDot[q,r]->1/2 (-mb^2-P10+P11),LDot[p,p]->mb^2,LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2}


PropagatorReplace["bhat",amp_]:=amp /. {LDot[l,l]->P2hat,LDot[l,r]->1/2 (-P2hat+P3hat-P4),LDot[l,p]->1/2 (-2 P2hat+P7+P9-q2),
LDot[l,q]->1/2 (-P2hat+P9-q2),LDot[r,r]->P4,LDot[p,r]->(P11-P4)/2,LDot[q,r]->1/2 (-mb^2-P10+P11),LDot[p,p]->mb^2,
LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2}


PropagatorReplace["bmb",amp_]:=amp /. {LDot[l,l]->mb^2+P2mb,LDot[l,r]->1/2 (-P2mb+P3mb-P4),
LDot[l,p]->1/2 (-2 mb^2-2 P2mb+P7+P9-q2),LDot[l,q]->1/2 (-mb^2-P2mb+P9-q2),LDot[r,r]->P4,LDot[p,r]->(P11-P4)/2,
LDot[q,r]->1/2 (-mb^2-P10+P11),LDot[p,p]->mb^2,LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2}


PropagatorReplace["c",amp_]:=amp /. {LDot[l,l]->mc^2+P2,LDot[l,r]->1/2 (-P2+P3-P4),
LDot[l,p]->1/2 (-mc^2+P1-2 P2+P7-q2),LDot[l,q]->1/2 (P1-P2-q2),LDot[r,r]->P4,LDot[p,r]->1/2 (-2 P4+P5+P6-q2),
LDot[q,r]->1/2 (-P4+P6-q2),LDot[p,p]->mb^2,LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2}


PropagatorReplace["chat",amp_]:=amp /. {LDot[l,l]->P2hat,LDot[l,r]->1/2 (-P2hat+P3hat-P4),
LDot[l,p]->1/2 (P1hat-2 P2hat+P7-q2),LDot[l,q]->1/2 (P1hat-P2hat-q2),LDot[r,r]->P4,LDot[p,r]->1/2 (-2 P4+P5+P6-q2),
LDot[q,r]->1/2 (-P4+P6-q2),LDot[p,p]->mb^2,LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2}


PropagatorReplace["cmb",amp_]:=amp /. {LDot[l,l]->mb^2+P2mb,LDot[l,r]->1/2 (-P2mb+P3mb-P4),
LDot[l,p]->1/2 (-mb^2+P1mb-2 P2mb+P7-q2),LDot[l,q]->1/2 (P1mb-P2mb-q2),LDot[r,r]->P4,LDot[p,r]->1/2 (-2 P4+P5+P6-q2),
LDot[q,r]->1/2 (-P4+P6-q2),LDot[p,p]->mb^2,LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2}


PropagatorReplace["d",amp_]:=amp /.{LDot[l,l]->mc^2+P2,LDot[l,r]->1/2 (-P1+P12-P6+q2),
LDot[l,p]->1/2 (-mc^2+P1-2 P2+P7-q2),LDot[l,q]->1/2 (P1-P2-q2),LDot[r,r]->P4,LDot[p,r]->(P11-P4)/2,
LDot[q,r]->1/2 (-P4+P6-q2),LDot[p,p]->mb^2,LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2} 


PropagatorReplace["dhat",amp_]:=amp /.{LDot[l,l]->P2hat,LDot[l,r]->1/2 (P12hat-P1hat-P6+q2),
LDot[l,p]->1/2 (P1hat-2 P2hat+P7-q2),LDot[l,q]->1/2 (P1hat-P2hat-q2),LDot[r,r]->P4,LDot[p,r]->(P11-P4)/2,
LDot[q,r]->1/2 (-P4+P6-q2),LDot[p,p]->mb^2,LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2}


PropagatorReplace["dmb",amp_]:=amp /.{LDot[l,l]->mb^2+P2mb,LDot[l,r]->1/2 (P12mb-P1mb-P6+q2),
LDot[l,p]->1/2 (-mb^2+P1mb-2 P2mb+P7-q2),LDot[l,q]->1/2 (P1mb-P2mb-q2),LDot[r,r]->P4,LDot[p,r]->(P11-P4)/2,
LDot[q,r]->1/2 (-P4+P6-q2),LDot[p,p]->mb^2,LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2}


PropagatorReplace["e",amp_]:=amp /.{LDot[l,l]->mc^2+P2,LDot[l,r]->1/2(-P2+P3-P4),LDot[l,p]->1/2(-mc^2+P1-2P2+P7-q2), 
LDot[l,q]->1/2(P1-P2-q2),LDot[r,r]->P4,LDot[p,r]->1/2(-P1+P12+P13+P2-P3-P4),LDot[q,r]->1/2(-P1+P12+P2-P3),
LDot[p,p]->mb^2,LDot[p,q]->1/2(mb^2+q2),LDot[q,q]->q2}


PropagatorReplace["ehat",amp_]:=amp /.{LDot[l,l]->P2hat,LDot[l,r]->1/2 (-P2hat+P3hat-P4),LDot[l,p]->1/2 (P1hat-2 P2hat+P7-q2),
LDot[l,q]->1/2 (P1hat-P2hat-q2),LDot[r,r]->P4,LDot[p,r]->1/2 (P12hat+P13-P1hat+P2hat-P3hat-P4),
LDot[q,r]->1/2 (P12hat-P1hat+P2hat-P3hat),LDot[p,p]->mb^2,LDot[p,q]->1/2 (mb^2+q2),LDot[q,q]->q2}


PropagatorReplace["emb",amp_]:=amp /.{LDot[l,l]->mb^2+P2mb,LDot[l,r]->1/2(-P2mb+P3mb-P4),
LDot[l,p]->1/2(-mb^2+P1mb-2P2mb+P7-q2),LDot[l,q]->1/2(P1mb-P2mb-q2),LDot[r,r]->P4,
LDot[p,r]->1/2(P12mb+P13-P1mb+P2mb-P3mb-P4),LDot[q,r]->1/2(P12mb-P1mb+P2mb-P3mb),LDot[p,p]->mb^2,LDot[p,q]->1/2(mb^2+q2),
LDot[q,q]->q2}
