(* Focused independent Wolfram checks of corrected and retained identities. *)
$MaxExtraPrecision = 200;
wp = 70;
checks = {};
check[name_, lhs_, rhs_, tol_:10^-45] := Module[{r},
 r = Quiet[TimeConstrained[Abs[N[lhs - rhs, wp]], 90, $Failed]];
 AppendTo[checks, <|"name" -> name, "residual" -> ToString[r, InputForm],
   "pass" -> TrueQ[NumberQ[r] && r < tol]|>];
 Print[name, " ", Last[checks]["pass"], " ", r];
];
cl[k_, x_] := If[EvenQ[k], Im[PolyLog[k, Exp[I x]]], Re[PolyLog[k, Exp[I x]]]];
be[k_] := Im[PolyLog[k, I]];
check["external rational dilogarithm correction", 6 PolyLog[2, 1/3] - PolyLog[2, 1/9], Pi^2/3 - Log[3]^2];
check["MZV convention", MultipleZeta[{2,1,1}], Zeta[4]];
check["HPL leading zero", HarmonicPolyLog[{0,1}, 2/5], PolyLog[2,2/5]];
check["HPL reflection alphabet", HarmonicPolyLog[{-1}, 1-2/5], Log[2-2/5]];
Do[check["even sum S"<>ToString[p],
 -NIntegrate[(-Log[x])^(p-1) Log[1+x^2]/(1+x^2), {x,0,1},
   WorkingPrecision->wp, PrecisionGoal->55, AccuracyGoal->55]/Factorial[p-1],
 Switch[p,1,be[2]-Pi Log[2]/2,
 3,3be[4]-Pi^3 Log[2]/16-7Pi Zeta[3]/16,
 5,(-5Pi^5 Log[2]-42Pi^3 Zeta[3]-372Pi Zeta[5]+3840be[6])/768,
 7,(-61Pi^7 Log[2]-525Pi^5 Zeta[3]-5580Pi^3 Zeta[5]-45720Pi Zeta[7]+645120be[8])/92160]],{p,{1,3,5,7}}];
Do[check["trigamma DFT q="<>ToString[q]<>" p="<>ToString[p],PolyGamma[1,p/q],
 Pi^2/(2Sin[Pi p/q]^2)+2q Sum[Sin[2Pi j p/q]cl[2,2Pi j/q],{j,1,Floor[(q-1)/2]}]],
 {q,{3,4,5,8,12}},{p,Select[Range[q-1],CoprimeQ[#,q]&]}];
check["Gaussian mixed weight two", MultiplePolyLog[{1,1},{I,-I}],-PolyLog[2,(1-I)/2]];
check["Gaussian g51 from iterated integral", 2048Im[NIntegrate[(-Log[x])^3 Log[1-I x]^2/x,{x,0,1},
 WorkingPrecision->wp,PrecisionGoal->55,AccuracyGoal->55]/12],
 -64Pi^3 Zeta[3]-527Pi Zeta[5]+4096be[6]];
check["Gamma trig-root", Gamma[2/7]Gamma[11/42]/Gamma[1/21],
 8Sin[Pi/7] Sqrt[Pi Sin[Pi/21]Sin[4Pi/21]Sin[5Pi/21]]/(2^(1/42)7^(1/3)3^(9/28))];
u[t_] := t/(Sqrt[1+t^2]+1);
chi2[t_] := (PolyLog[2,t]-PolyLog[2,-t])/2;
check["Lee mixed integral",NIntegrate[ArcTan[2Sin[x]]ArcTan[2Sin[x]/Sqrt[5]],{x,0,Pi/2},
 WorkingPrecision->wp,PrecisionGoal->55],Pi chi2[u[2]u[2/Sqrt[5]]]];
check["loggamma quarter",PolyGamma[-2,1/4],3/32+Log[2]/8+Log[Pi]/8+Catalan/(4Pi)-9Zeta'[-1]/8];
check["CM square G4", 2Zeta[4](1+240Sum[n^3 Exp[-2Pi n]/(1-Exp[-2Pi n]),{n,1,50}]),
 Gamma[1/4]^8/(960Pi^2)];
check["CM hexagonal G6",2Zeta[6](1-504Sum[n^5 Exp[2Pi I Exp[I Pi/3]n]/(1-Exp[2Pi I Exp[I Pi/3]n]),{n,1,50}]),
 Gamma[1/3]^18/(8960Pi^6)];
Export[FileNameJoin[{DirectoryName[$InputFileName],"wolfram-results.json"}],
 <|"engine"->$Version,"working_precision"->wp,"checks"->checks,
 "all_pass"->And@@Lookup[checks,"pass"]|>,"RawJSON"];
If[!And@@Lookup[checks,"pass"],Exit[1]];
