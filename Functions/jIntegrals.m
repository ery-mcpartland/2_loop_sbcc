(* ::Package:: *)

gettingPowersFromSingleTerm["a",singleTerm_]:= Block[{powers,coeff},
powers=Exponent[singleTerm,{1/P2,1/P3,1/P4,1/P5,1/P8,1/P7,1/P9}];<<MasterIntegralReplacements`
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
coeff=If[powers=={0,0,0,0,0,0,0},singleTerm,Coefficient[singleTerm,(1/P1^#1 1/P2^#2 1/P3^#3 1/P4^#4 1/P12^#5 1/P7^#6 1/P13^#7) & @@ powers]];
{coeff,powers}
]


jIntegralForm[diag_,int_]:=Simplify[Total[gettingPowersFromSingleTerm[diag,#]&/@int
/.{b_,{aa1_,aa2_,aa3_,a4_,a5_,a6_,a7_}}->b diag[aa1,aa2,aa3,a4,a5,a6,a7]]];
