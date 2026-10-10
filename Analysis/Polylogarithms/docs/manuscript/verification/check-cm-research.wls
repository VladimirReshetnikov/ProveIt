base=DirectoryName[$InputFileName];wp=90;tol=10^-60;checks={};
ew[w_,tau_]:=1-(2w/BernoulliB[w]) Sum[DivisorSigma[w-1,k] Exp[2Pi I tau k],{k,1,100}];
g[w_,tau_]:=2Zeta[w] ew[w,N[tau,wp]];
forms[d_]:=Switch[d,15,{{1,1,4},{2,1,2}},20,{{1,0,5},{2,2,3}},
 23,{{1,1,6},{2,-1,3},{2,1,3}},39,{{1,1,10},{2,-1,5},{2,1,5},{3,3,4}},
 47,{{1,1,12},{2,-1,6},{2,1,6},{3,-1,4},{3,1,4}}];
tau[d_,q_]:=(-q[[2]]+I Sqrt[d])/(2q[[1]]);
record[name_,lhs_,rhs_]:=Module[{err},err=Abs[N[lhs/rhs-1,wp]];
 AppendTo[checks,<|"name"->name,"relative_residual"->ToString[N[err,16],InputForm],
  "tolerance"->"1e-60","passed"->TrueQ[NumericQ[err]&&err<tol]|>];Print[name,": ",Last[checks]["passed"]]];
res[d_]:=Switch[d,15,{1,2,4,8},20,{1,3,7,9},23,{1,2,3,4,6,8,9,12,13,16,18},
 39,{1,2,4,5,8,10,11,16,20,22,25,32},47,{1,2,3,4,6,7,8,9,12,14,16,17,18,21,24,25,27,28,32,34,36,37,42}];
pd[d_]:=Times@@(Gamma[#/d]&/@res[d]);
roots[d_,w_]:=Switch[{d,w},{15,4},(3^6 5^3 11^3)^(1/3),{20,4},(2^12 5^3 11^3)^(1/3),
 {23,4},(5^9 11^3 17^3)^(1/3),{39,4},(3^15 17^3 23^3 29^3)^(1/3),{47,4},(5^15 11^6 23^3 29^3)^(1/3),
 {15,6},Sqrt[3^6 7^4 11^2],{20,6},Sqrt[2^16 11^2 19^2],{23,6},Sqrt[7^6 11^4 19^2 23],
 {39,6},Sqrt[3^12 7^8 19^4 23^2],{47,6},Sqrt[11^6 19^4 23^4 31^2 43^2 47]];
Do[h=Length[forms[d]];aa=Times@@forms[d][[All,1]];phi=EulerPhi[d];cc=If[MemberQ[{23,47},d],d,1];
 Do[actual=Times@@(Abs[g[w,tau[d,#]]]&/@forms[d]);
 expected=(Abs[BernoulliB[w]]/w!)^h (aa/d^h)^(w/2) cc^(w/4) (2Pi)^(w(2h-phi)/4) pd[d]^w roots[d,w];
 record["CM absolute product D="<>ToString[-d]<>" w="<>ToString[w],actual,expected],{w,{4,6}}],{d,{15,20,23,39,47}}];
parseRat[s_String]:=If[StringMatchQ[s,RegularExpression["-?[0-9]+(/[0-9]+)?"]],ToExpression[s],$Failed];
data=Import[FileNameJoin[{base,"CM-genus-extensions.json"}],"RawJSON"];
Do[d=-row["D"];w=row["weight"];e=row["positive_discriminant"];
 expected=parseRat[row["value"]["rational_coefficient"]]+parseRat[row["value"]["sqrt_coefficient"]]Sqrt[e];
 vals=Abs[g[w,tau[d,#]]]&/@forms[d];actual=If[d==39,vals[[1]]vals[[4]]/(vals[[2]]vals[[3]]),vals[[1]]/vals[[2]]];
 record["New genus ratio D="<>ToString[-d]<>" w="<>ToString[w],actual,expected],{row,data["new_ratio_formulas"]}];
record["G4 at 2i",g[4,2I],11Gamma[1/4]^8/(15360Pi^2)];
record["G6 at 2i",g[6,2I],Gamma[1/4]^12/(2^14 5Pi^3)];
record["G4 at i sqrt(2)",g[4,I Sqrt[2]],Gamma[1/8]^4 Gamma[3/8]^4/(4608Pi^2)];
record["G6 at i sqrt(2)",g[6,I Sqrt[2]],Gamma[1/8]^6 Gamma[3/8]^6/(2^12 3^3 5Pi^3)];
record["D=-15 weight-four real projection",Re[g[4,(-1+I Sqrt[15])/4]],7Abs[g[4,(-1+I Sqrt[15])/4]]/8];
record["D=-15 weight-six real projection",Re[g[6,(-1+I Sqrt[15])/4]],11Abs[g[6,(-1+I Sqrt[15])/4]]/16];
out=<|"engine"->$Version,"working_precision"->wp,"q_terms"->100,"checks"->checks,
 "all_pass"->And@@Lookup[checks,"passed"],"scope"->"Independent native Fourier/gamma diagnostics; analytic CM normalization, rational bounds and interval class-polynomial proofs are separate."|>;
Export[FileNameJoin[{base,"CM-native-results.json"}],out,"RawJSON"];
Exit[If[TrueQ[out["all_pass"]],0,1]];
