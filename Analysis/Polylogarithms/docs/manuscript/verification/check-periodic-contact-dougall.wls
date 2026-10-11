$MaxExtraPrecision=2000;
ClearAll[x,y,a,p,q,u,nn,v,z,ff,kk,hh];
exact=Table[TrueQ[Together[Sum[Binomial[k+j-1,j]/(x+y)^(k+j)/x^(2-j),{j,0,1}]+Sum[(j+1)/(x+y)^(2+j)/y^(k-j),{j,0,k-1}]-1/(x^2 y^k)]===0],{k,2,16}];
eta=a/2;d0=a-1-p-q;
c1=-Total[BernoulliB[3,#]& /@ {eta,1+p-eta,1+q-eta,d0-u-eta}]/3;
AppendTo[exact,TrueQ[Expand[(c1/.u->-1)+d0 p q]===0]];
AppendTo[exact,TrueQ[Expand[(D[c1,u]/.u->-1)/2-BernoulliB[2,eta]/2+d0(p+q)/2]===0]];
rows={};
(* Separate the exact endpoint Laurent terms and integrate only smooth
   shifted polygamma/Stieltjes functions. Taylor sums have 150 terms.
   The omitted phase tail is bounded by omega^151/151!/(1-omega/152).
   Quadrature residuals are diagnostic, not interval certificates. *)
Do[omega=2 Pi k;ll=EulerGamma+Log[omega];
 f0[t_?NumericQ]:=-PolyGamma[0,1+t](Exp[-I omega t]-1);
 f1[t_?NumericQ]:=StieltjesGamma[1,1+t](Exp[-I omega t]-1);
 fp[t_?NumericQ]:=-PolyGamma[1,1+t]Exp[-I omega t];
 t0=N[Sum[(-I omega)^j/(j! j),{j,1,150}],100]+NIntegrate[f0[x],{x,0,1/4,1/2,1},WorkingPrecision->60,AccuracyGoal->35,PrecisionGoal->35];
 t1=-N[Sum[(-I omega)^j/(j! j^2),{j,1,150}],100]+NIntegrate[f1[x],{x,0,1/4,1/2,1},WorkingPrecision->60,AccuracyGoal->35,PrecisionGoal->35,MaxRecursion->25];
 tp=1-N[Sum[(-I omega)^j/(j!(j-1)),{j,2,150}],100]+NIntegrate[fp[x],{x,0,1/4,1/2,1},WorkingPrecision->60,AccuracyGoal->35,PrecisionGoal->35];
 targets={-ll-I Pi/2,((ll+I Pi/2)^2+Zeta[2])/2,I omega(1-ll-I Pi/2)};
 vals={t0,t1,tp};
 Do[err=Abs[vals[[j]]-N[targets[[j]],60]];AppendTo[rows,<|"kind"->"coordinate-Fourier-moment","frequency"->k,"moment"->j,"absolute_residual"->ToString[err,InputForm],"passed"->TrueQ[err<10^-30]|>],{j,1,3}];
 err=Abs[Abs[t0]^2-2 Re[t1]-N[Pi^2/3,60]];
 AppendTo[rows,<|"kind"->"digamma-collision-contact","frequency"->k,"absolute_residual"->ToString[err,InputForm],"passed"->TrueQ[err<10^-30]|>];
 fz[t_?NumericQ]:=If[t==0,0,4 Sin[omega t/2]^4(1/t^3-PolyGamma[2,1+t]/2)];
 val=NIntegrate[fz[x],{x,0,1/4,1/2,1},WorkingPrecision->60,AccuracyGoal->35,PrecisionGoal->35];
 err=Abs[val-N[4 Pi^2 k^2 Log[2],60]];
 AppendTo[rows,<|"kind"->"ordinary-weighted-Hurwitz-three","frequency"->k,"absolute_residual"->ToString[err,InputForm],"passed"->TrueQ[err<10^-30]|>];
 Print[<|"frequency_completed"->k,"checks_completed"->Length[rows]|>],{k,{1,2}}];
phasebound=N[(4 Pi)^151/151!/(1-4 Pi/152),60];
record=<|"engine"->$Version,"exact_checks"->Length[exact],"exact_passed"->And@@exact,"exact_results"->exact,"numerical_checks"->Length[rows],"rows"->rows,"working_precision"->60,"endpoint_phase_terms"->150,"phase_tail_upper_bound"->ToString[phasebound,InputForm],"phase_tail_bound_passed"->TrueQ[phasebound<10^-80],"interval_certified"->False,"missing_atom_control"-><|"omitted_atom_mean"->ToString[-Pi^2/3,InputForm],"restored_mean"->FullSimplify[-Pi^2/3+Pi^2/3],"rejected"->TrueQ[Pi^2/3!=0]|>,"all_pass"->(And@@exact&&And@@Lookup[rows,"passed"]&&TrueQ[phasebound<10^-80]),"scope"->"Native exact Euler partial fractions and first-resonance Bernoulli constants; independent ordinary/subtracted Fourier moments with smooth endpoint splits and an exact phase-series tail bound. Four independently refined double-Laplace quadratures are recorded separately in dougall-gauss-native.json. Numerical agreement is diagnostic, not interval accuracy or the all-index analytic proof."|>;
Export[FileNameJoin[{DirectoryName[$InputFileName],"periodic-contact-dougall-native.json"}],record,"RawJSON"];
Print[<|"exact_checks"->Length[exact],"numerical_checks"->Length[rows],"all_pass"->record["all_pass"]|>];Exit[If[TrueQ[record["all_pass"]],0,1]];
