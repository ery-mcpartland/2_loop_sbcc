(* ::Package:: *)

(* ::Title:: *)
(*j Integrals*)


(* ::Text:: *)
(*Code to convert from scalar integrals written in terms of powers of P_i into j-integrals of the form i[ni1,ni2,ni3,ni4,ni5,ni6,ni7] - where i is the diagram family and  nij is the power of the jth propagator in family i. *)


(* ::Section:: *)
(*Defining Functions*)


(* ::Subsection:: *)
(*Getting Powers From Single Term*)


(* ::Text:: *)
(*Five functions, one for each class of diagram.  Takes a single term of the form a(q2,mb,mc)*P_i1^{n_i1}* .... *P_i7^{n_i7} and converts a term of the form a(q2,mb,mc)*{n_i1,n_i2,n_i3,n_i4,n_i5,n_i6,n_i7}.*)


(* ::Subsection:: *)
(*j integral form*)


(* ::Text:: *)
(*Takes a list of a(q2,mb,mc)*P_i1^{n_i1}* .... *P_i7^{n_i7} terms, applies GettingPowersFromSingleTerm to them each in turn, converts the result to the form a(q2,mb,mc)*i[n_i1,n_i2,n_i3,n_i4,n_i5,n_i6,n_i7] then returns the total of all the terms.*)


(* ::Section:: *)
(*Functions*)


(* ::Subsection:: *)
(*Getting Powers From Single Term*)


gettingPowersFromSingleTerm["a",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P2,1/P3,1/P4,1/P5,1/P8,1/P7,1/P9}];
coeff=If[powers=={0,0,0,0,0,0,0},singleTerm,Coefficient[singleTerm,(1/P2^#1 1/P3^#2 1/P4^#3 1/P5^#4 1/P8^#5 
1/P7^#6 1/P9^#7) & @@ powers]];
{coeff,powers}
]


gettingPowersFromSingleTerm["ahat",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P2hat,1/P3hat,1/P4,1/P5,1/P8,1/P7,1/P9}];
coeff=If[powers=={0,0,0,0,0,0,0},singleTerm,Coefficient[singleTerm,(1/P2hat^#1 1/P3hat^#2 1/P4^#3 1/P5^#4 1/P8^#5 
1/P7^#6 1/P9^#7) & @@ powers]];
{coeff,powers}
]


gettingPowersFromSingleTerm["amb",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P2mb,1/P3mb,1/P4,1/P5,1/P8,1/P7,1/P9}];
coeff=If[powers=={0,0,0,0,0,0,0},singleTerm,Coefficient[singleTerm,(1/P2mb^#1 1/P3mb^#2 1/P4^#3 1/P5^#4 1/P8^#5 
1/P7^#6 1/P9^#7) & @@ powers]];
{coeff,powers}
]


gettingPowersFromSingleTerm["b",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P2,1/P3,1/P4,1/P10,1/P11,1/P7,1/P9}];
coeff=If[powers=={0,0,0,0,0,0,0},singleTerm,Coefficient[singleTerm,(1/P2^#1 1/P3^#2 1/P4^#3 1/P10^#4 1/P11^#5
 1/P7^#6 1/P9^#7) & @@ powers]];
{coeff,powers}
]


gettingPowersFromSingleTerm["bhat",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P2hat,1/P3hat,1/P4,1/P10,1/P11,1/P7,1/P9}];
coeff=If[powers=={0,0,0,0,0,0,0},singleTerm,Coefficient[singleTerm,(1/P2hat^#1 1/P3hat^#2 1/P4^#3 1/P10^#4 1/P11^#5
 1/P7^#6 1/P9^#7) & @@ powers]];
{coeff,powers}
]


gettingPowersFromSingleTerm["bmb",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P2mb,1/P3mb,1/P4,1/P10,1/P11,1/P7,1/P9}];
coeff=If[powers=={0,0,0,0,0,0,0},singleTerm,Coefficient[singleTerm,(1/P2mb^#1 1/P3mb^#2 1/P4^#3 1/P10^#4 1/P11^#5
 1/P7^#6 1/P9^#7) & @@ powers]];
{coeff,powers}
]


gettingPowersFromSingleTerm["c",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P1,1/P2,1/P3,1/P4,1/P5,1/P6,1/P7}];
coeff=If[powers=={0,0,0,0,0,0,0},singleTerm,Coefficient[singleTerm,(1/P1^#1 1/P2^#2 1/P3^#3 1/P4^#4 1/P5^#5
 1/P6^#6 1/P7^#7) & @@ powers]];
{coeff,powers}
]


gettingPowersFromSingleTerm["chat",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P1hat,1/P2hat,1/P3hat,1/P4,1/P5,1/P6,1/P7}];
coeff=If[powers=={0,0,0,0,0,0,0},singleTerm,Coefficient[singleTerm,(1/P1hat^#1 1/P2hat^#2 1/P3hat^#3 1/P4^#4 1/P5^#5
 1/P6^#6 1/P7^#7) & @@ powers]];
{coeff,powers}
]


gettingPowersFromSingleTerm["cmb",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P1mb,1/P2mb,1/P3mb,1/P4,1/P5,1/P6,1/P7}];
coeff=If[powers=={0,0,0,0,0,0,0},singleTerm,Coefficient[singleTerm,(1/P1mb^#1 1/P2mb^#2 1/P3mb^#3 1/P4^#4 1/P5^#5
 1/P6^#6 1/P7^#7) & @@ powers]];
{coeff,powers}
]


gettingPowersFromSingleTerm["d",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P1,1/P2,1/P12,1/P4,1/P11,1/P6,1/P7}];
coeff=If[powers=={0,0,0,0,0,0,0},singleTerm,Coefficient[singleTerm,(1/P1^#1 1/P2^#2 1/P12^#3 1/P4^#4 1/P11^#5
 1/P6^#6 1/P7^#7) & @@ powers]];
{coeff,powers}
]


gettingPowersFromSingleTerm["dhat",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P1hat,1/P2hat,1/P12hat,1/P4,1/P11,1/P6,1/P7}];
coeff=If[powers=={0,0,0,0,0,0,0},singleTerm,Coefficient[singleTerm,(1/P1hat^#1 1/P2hat^#2 1/P12hat^#3 1/P4^#4 1/P11^#5
 1/P6^#6 1/P7^#7) & @@ powers]];
{coeff,powers}
]


gettingPowersFromSingleTerm["dmb",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P1mb,1/P2mb,1/P12mb,1/P4,1/P11,1/P6,1/P7}];
coeff=If[powers=={0,0,0,0,0,0,0},singleTerm,Coefficient[singleTerm,(1/P1mb^#1 1/P2mb^#2 1/P12mb^#3 1/P4^#4 1/P11^#5
 1/P6^#6 1/P7^#7) & @@ powers]];
{coeff,powers}
]


gettingPowersFromSingleTerm["e",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P1,1/P2,1/P3,1/P4,1/P12,1/P7,1/P13}];
coeff=If[powers=={0,0,0,0,0,0,0},singleTerm,Coefficient[singleTerm,(1/P1^#1 1/P2^#2 1/P3^#3 1/P4^#4 1/P12^#5
 1/P7^#6 1/P13^#7) & @@ powers]];
{coeff,powers}
]


gettingPowersFromSingleTerm["ehat",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P1hat,1/P2hat,1/P3hat,1/P4,1/P12hat,1/P7,1/P13}];
coeff=If[powers=={0,0,0,0,0,0,0},singleTerm,Coefficient[singleTerm,(1/P1hat^#1 1/P2hat^#2 1/P3hat^#3 1/P4^#4 1/P12hat^#5
 1/P7^#6 1/P13^#7) & @@ powers]];
{coeff,powers}
]


gettingPowersFromSingleTerm["emb",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P1mb,1/P2mb,1/P3mb,1/P4,1/P12mb,1/P7,1/P13}];
coeff=If[powers=={0,0,0,0,0,0,0},singleTerm,Coefficient[singleTerm,(1/P1mb^#1 1/P2mb^#2 1/P3mb^#3 1/P4^#4 1/P12mb^#5
 1/P7^#6 1/P13^#7) & @@ powers]];
{coeff,powers}
]


(* ::Subsection:: *)
(*j integral form*)


jIntegralForm[diag_,expr_]:=Total[gettingPowersFromSingleTerm[diag,#]&/@(List@@Expand[expr])
/.{con_,{aa1_,aa2_,aa3_,a4_,a5_,a6_,a7_}}->con diag[aa1,aa2,aa3,a4,a5,a6,a7]];
