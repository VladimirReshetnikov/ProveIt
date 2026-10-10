base=DirectoryName[$InputFileName];wp=100;checks={};
parseRat[s_String]:=If[StringMatchQ[s,RegularExpression["-?[0-9]+(/[0-9]+)?"]],ToExpression[s],$Failed];
data=Import[FileNameJoin[{base,"subcritical-difference-certificates.json"}],"RawJSON"];
f0[b_,z_]:=z PolyLog[b,z]/(1-z);
integrand[a_,b_,x_?NumericQ]:=Im[f0[b,I Exp[-x^(1/a)]]]/Gamma[a+1];
Do[a=parseRat[row["a"]];b=parseRat[row["b"]];
 actual=If[a==0,Im[N[f0[b,I],wp]],
   TimeConstrained[NIntegrate[integrand[a,b,x],{x,0,1,2,Infinity},
     WorkingPrecision->wp,AccuracyGoal->75,PrecisionGoal->75,MaxRecursion->35,
     Method->{"GlobalAdaptive","SymbolicProcessing"->0}],180,$Failed]];
 lower=parseRat[row["analytic_Gaussian_interval"]["lower"]];
 upper=parseRat[row["analytic_Gaussian_interval"]["upper"]];
 passed=TrueQ[NumericQ[actual]&&lower<actual<upper];
 AppendTo[checks,<|"a"->row["a"],"b"->row["b"],"value"->ToString[N[actual,75],InputForm],
   "within_exact_interval"->passed,"method"->If[a==0,"Native axis polylogarithm","Native outer Gamma integral of depth-one polylogarithm"]|>];
 Print["Gaussian a=",a," b=",b," within exact interval: ",passed],{row,data["Gaussian_cases"]}];
out=<|"engine"->$Version,"working_precision"->wp,"checks"->checks,
 "all_pass"->And@@Lookup[checks,"within_exact_interval"],
 "scope"->"Independent native numerical diagnostics against exact rational Euler enclosures. This is not interval quadrature or a substitute for the written all-parameter Stieltjes proof."|>;
Export[FileNameJoin[{base,"subcritical-native-results.json"}],out,"RawJSON"];
Exit[If[TrueQ[out["all_pass"]],0,1]];
