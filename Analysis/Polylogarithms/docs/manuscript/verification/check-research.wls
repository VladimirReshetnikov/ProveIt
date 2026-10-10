base = DirectoryName[$InputFileName];
wp = 80; tol = 10^-45; checks = {};
record[name_, value_, expected_] := Module[{err},
 err = Abs[N[value - expected, wp]];
 AppendTo[checks, <|"name" -> name, "absolute_residual" -> ToString[N[err,16],InputForm],
   "tolerance" -> "1e-45", "passed" -> TrueQ[NumericQ[err] && err < tol]|>];
 Print[name, ": ", Last[checks]["passed"]]];
si[t_?NumericQ] := If[t == 0, 0, Log[t] Log[1+t^2]/(1+t^2)];
gi[t_?NumericQ] := If[t == 0, 0, -Log[t] Im[-I Log[1-I t]/(1-I t)]];
s2 = NIntegrate[si[t], {t,0,1/2,1}, WorkingPrecision->wp,
 AccuracyGoal->60,PrecisionGoal->55,MaxRecursion->30,
 Method->{"GlobalAdaptive","SymbolicProcessing"->0}];
g21 = NIntegrate[gi[t], {t,0,1/2,1}, WorkingPrecision->wp,
 AccuracyGoal->60,PrecisionGoal->55,MaxRecursion->30,
 Method->{"GlobalAdaptive","SymbolicProcessing"->0}];
record["S2 double-coordinate formula",s2,-2g21+Pi^3/32-2Catalan Log[2]];
record["S2 classical half-point formula",s2,
 2Im[PolyLog[3,(1+I)/2]]-Catalan Log[2]-Pi Log[2]^2/16-Pi^3/64];
g[a_,b_] := g[a,b] = NIntegrate[If[t==0,0,(-Log[t])^(a-1) Im[I PolyLog[b,I t]/(1-I t)]/(a-1)!],{t,0,1/2,1},WorkingPrecision->wp, AccuracyGoal->60,PrecisionGoal->55,MaxRecursion->30, Method->{"GlobalAdaptive","SymbolicProcessing"->0}];
record["Weight-seven Gaussian coordinate change",g[2,5],30g[6,1]+15g[5,2]+5g[4,3]-15Catalan Zeta[5]/512+3Im[PolyLog[4,I]]Zeta[3]/16-11Pi^7/368640];
report = <|"engine"->$Version,"working_precision"->wp,"checks"->checks,
 "all_pass"->And@@Lookup[checks,"passed"],
 "scope"->"Independent defining-integral numerical diagnostics; the S2 proof is the exact word certificate and its analytic relation schemas."|>;
Export[FileNameJoin[{base,"research-native-results.json"}],report,"RawJSON"];
Exit[If[TrueQ[report["all_pass"]],0,1]];
