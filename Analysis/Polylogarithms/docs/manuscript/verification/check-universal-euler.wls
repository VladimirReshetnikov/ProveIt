base=DirectoryName[$InputFileName];wp=90;checks={};
parseRat[s_String]:=If[StringMatchQ[s,RegularExpression["-?[0-9]+(/[0-9]+)?"]],ToExpression[s],$Failed];
data=Import[FileNameJoin[{base,"universal-Euler-certificates.json"}],"RawJSON"];
f0[b_,z_]:=z PolyLog[b,z]/(1-z);
integrand[a_,b_,x_?NumericQ]:=Im[f0[b,I Exp[-x^(1/a)]]]/Gamma[a+1];
Do[a=parseRat[row["a"]];b=parseRat[row["b"]];
 actual=If[a==0,Im[N[f0[b,I],wp]],
   TimeConstrained[NIntegrate[integrand[a,b,x],{x,0,1,2,Infinity},
     WorkingPrecision->wp,AccuracyGoal->65,PrecisionGoal->65,MaxRecursion->35,
     Method->{"GlobalAdaptive","SymbolicProcessing"->0}],180,$Failed]];
 lower=parseRat[row["Gaussian_interval"]["lower"]];
 upper=parseRat[row["Gaussian_interval"]["upper"]];
 passed=TrueQ[NumericQ[actual]&&lower<actual<upper];
 tailChecks=Table[n=tail["N"];
   weights=Table[(-1)^k Sum[Binomial[n,j],{j,k+1,n}],{k,0,n-1}];
   en=Sum[weights[[k+1]] HarmonicNumber[2k,b]/(2k+1)^a,{k,0,n-1}]/2^n;
   scaled=N[2^n(en-actual),wp];
   sl=parseRat[tail["scaled_error_interval"]["lower"]];
   su=parseRat[tail["scaled_error_interval"]["upper"]];
   <|"N"->n,"scaled_error"->ToString[N[scaled,60],InputForm],
     "within_exact_interval"->TrueQ[NumericQ[scaled]&&sl<scaled<su]|>,
   {tail,row["tails"]}];
 AppendTo[checks,<|"a"->row["a"],"b"->row["b"],"value"->ToString[N[actual,60],InputForm],
   "within_exact_interval"->passed,"tails"->tailChecks,
   "method"->If[a==0,"Native axis polylogarithm","Native outer Gamma integral"]|>];
 Print["Universal Euler a=",a," b=",b," Gaussian: ",passed," tails: ",And@@Lookup[tailChecks,"within_exact_interval"]],
 {row,data["Gaussian_cases"]}];
out=<|"engine"->$Version,"working_precision"->wp,"checks"->checks,
 "all_pass"->And@@Flatten[Table[Join[{row["within_exact_interval"]},Lookup[row["tails"],"within_exact_interval"]],{row,checks}]],
 "scope"->"Independent native numerical diagnostics against exact rational Gaussian and Euler-tail enclosures. Quadrature rounding is not interval-certified; universal claims rest on the written contraction proof."|>;
Export[FileNameJoin[{base,"universal-Euler-native.json"}],out,"RawJSON"];
Exit[If[TrueQ[out["all_pass"]],0,1]];
