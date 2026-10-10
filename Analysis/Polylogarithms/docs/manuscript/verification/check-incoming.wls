base = DirectoryName[$InputFileName];
wp = 70; tol = 10^-40; checks = {};
record[name_, value_, expected_] := Module[{err},
 err = If[value === $Failed, Infinity, Abs[N[value - expected, wp]]];
 AppendTo[checks, <|"name" -> name, "absolute_residual" -> ToString[N[err,16],InputForm],
   "tolerance" -> "1e-40", "passed" -> TrueQ[NumericQ[err] && err < tol]|>];
 Print[name, ": ", Last[checks]["passed"]]];
gIntegrand[a_,b_,t_?NumericQ] := If[t==0,0,(-Log[t])^(a-1) Im[I PolyLog[b,I t]/(1-I t)]/(a-1)!];
g[a_,b_] := g[a,b] = NIntegrate[gIntegrand[a,b,t],{t,0,1/2,1},WorkingPrecision->wp,
 AccuracyGoal->52,PrecisionGoal->48,MaxRecursion->30,Method->{"GlobalAdaptive","SymbolicProcessing"->0}];
sIntegrand[t_?NumericQ] := If[t==0,0,-(-Log[t])^3 Log[1+t^2]/(6(1+t^2))];
s4 = TimeConstrained[Quiet[NIntegrate[sIntegrand[t],{t,0,1/2,1},WorkingPrecision->wp,
 AccuracyGoal->52,PrecisionGoal->48,MaxRecursion->30,Method->{"GlobalAdaptive","SymbolicProcessing"->0}]],120,$Failed];
rhs = TimeConstrained[Quiet[(4g[4,1]-3g[3,2]-9g[2,3])/7+Pi^5/224-27Catalan Zeta[3]/224-2Im[PolyLog[4,I]]Log[2]],120,$Failed];
record["S4 independent defining integrals",s4,rhs];
ram[q_,b_] := Total[(# MoebiusMu[q/#])& /@ Divisors[GCD[q,b]]];
sg[n_,b_,q_] := sg[n,b,q] = N[StieltjesGamma[n,b/q],wp];
traceJet[q_,n_] := (-1)^n/q Sum[ram[q,b] Sum[Binomial[n,j] Log[q]^(n-j) sg[j,b,q],{j,0,n}],{b,1,q}];
Do[record["principal level-30 trace order "<>ToString[n],
 TimeConstrained[Quiet[traceJet[30,n]],180,$Failed],If[n<2,0,-2Log[2]Log[3]Log[5]]],{n,0,2}];
lm[x_?NumericQ] := If[x==0 || x==1,0,Log[Gamma[x]]Log[Gamma[1-x]]];
m11 = TimeConstrained[Quiet[NIntegrate[lm[x],{x,0,1/2,1},WorkingPrecision->wp,
 AccuracyGoal->52,PrecisionGoal->48,MaxRecursion->30,Method->{"GlobalAdaptive","SymbolicProcessing"->0}]],120,$Failed];
L = Log[2Pi]; A = EulerGamma+L;
m2 = EulerGamma^2/12+Pi^2/48+EulerGamma L/6+L^2/3-A Derivative[1][Zeta][2]/Pi^2+Derivative[2][Zeta][2]/(2Pi^2);
record["reflected moment M11 Appell identity",m11,L^2/2+Zeta[2]/4-m2];
report = <|"engine"->$Version,"working_precision"->wp,"checks"->checks,
 "all_pass"->And@@Lookup[checks,"passed"],"scope"->"Independent numerical audits; exact S4 proof is the separate rational word certificate."|>;
Export[FileNameJoin[{base,"incoming-native-results.json"}],report,"RawJSON"];
Exit[If[TrueQ[report["all_pass"]],0,1]];
