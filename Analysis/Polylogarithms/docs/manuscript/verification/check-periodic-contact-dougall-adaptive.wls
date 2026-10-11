ClearAll[x,y,a,p,q,u,nn,v,z,ff,kk,hh];
exact=Table[TrueQ[Together[Sum[Binomial[k+j-1,j]/(x+y)^(k+j)/x^(2-j),{j,0,1}]+Sum[(j+1)/(x+y)^(2+j)/y^(k-j),{j,0,k-1}]-1/(x^2 y^k)]===0],{k,2,16}];
eta=a/2;d0=a-1-p-q;
c1=-Total[BernoulliB[3,#]& /@ {eta,1+p-eta,1+q-eta,d0-u-eta}]/3;
AppendTo[exact,TrueQ[Expand[(c1/.u->-1)+d0 p q]===0]];
AppendTo[exact,TrueQ[Expand[(D[c1,u]/.u->-1)/2-BernoulliB[2,eta]/2+d0(p+q)/2]===0]];
rows={};
Do[omega=2 Pi k;ll=EulerGamma+Log[omega];
 f0[t_?NumericQ]:=If[t==0,-I omega,-PolyGamma[0,t](Exp[-I omega t]-1)];
 f1[t_?NumericQ]:=If[t==0,0,StieltjesGamma[1,t](Exp[-I omega t]-1)];
 fp[t_?NumericQ]:=If[t==0,-Zeta[2]+omega^2/2,-PolyGamma[1,1+t]Exp[-I omega t]-(Exp[-I omega t]-1+I omega t)/t^2];
 t0=NIntegrate[f0[x],{x,0,1/4,1/2,1},WorkingPrecision->60,AccuracyGoal->35,PrecisionGoal->35];
 t1=NIntegrate[f1[x],{x,0,1/4,1/2,1},WorkingPrecision->60,AccuracyGoal->35,PrecisionGoal->35,MaxRecursion->25];
 tp=1+NIntegrate[fp[x],{x,0,1/4,1/2,1},WorkingPrecision->60,AccuracyGoal->35,PrecisionGoal->35];
 targets={-ll-I Pi/2,((ll+I Pi/2)^2+Zeta[2])/2,I omega(1-ll-I Pi/2)};
 vals={t0,t1,tp};
 Do[err=Abs[vals[[j]]-N[targets[[j]],60]];AppendTo[rows,<|"kind"->"coordinate-Fourier-moment","frequency"->k,"moment"->j,"absolute_residual"->ToString[err,InputForm],"passed"->TrueQ[err<10^-30]|>],{j,1,3}];
 err=Abs[Abs[t0]^2-2 Re[t1]-N[Pi^2/3,60]];
 AppendTo[rows,<|"kind"->"digamma-collision-contact","frequency"->k,"absolute_residual"->ToString[err,InputForm],"passed"->TrueQ[err<10^-30]|>];
 fz[t_?NumericQ]:=If[t==0,0,-(1-Cos[omega t])^2 PolyGamma[2,t]/2];
 val=NIntegrate[fz[x],{x,0,1/4,1/2,1},WorkingPrecision->60,AccuracyGoal->35,PrecisionGoal->35];
 err=Abs[val-N[4 Pi^2 k^2 Log[2],60]];
 AppendTo[rows,<|"kind"->"ordinary-weighted-Hurwitz-three","frequency"->k,"absolute_residual"->ToString[err,InputForm],"passed"->TrueQ[err<10^-30]|>],{k,{1,2}}];
ff[alpha_,t_?NumericQ]:=If[t==0,0,t(Exp[-alpha t]-Exp[-t])/(1-Exp[-t])];
kk[alpha_,t_?NumericQ]:=Exp[-t]/(1-Exp[-t])^2+alpha/(2(1-Exp[-t]));
hh[alpha_,t_?NumericQ,z_?NumericQ]:=If[t==0||z==0||z==1,0,t ff[alpha,t z]ff[alpha,t(1-z)]kk[alpha,t]];
(* Finite v cutoff avoids an ill-conditioned unbounded multidimensional
   adaptive map. With mu=Min[a,1], M=Max[1,Abs[a-1]], the outer tail is
   at most M^2(1+a)Exp[-mu T](T^3/mu+3T^2/mu^2+6T/mu^3+6/mu^4)/6.
   This follows from |f_a(t)|<=M t Exp[-mu t] and Integrate[z(1-z),0,1]=1/6.
   It bounds truncation only; floating quadrature remains diagnostic. *)
cut=200;
Do[val=NIntegrate[hh[aa,v,z],{v,0,1,4,16,64,cut},{z,0,1/2,1},WorkingPrecision->55,AccuracyGoal->28,PrecisionGoal->28,MaxRecursion->20,Method->{"LocalAdaptive","SymbolicProcessing"->0}];
 target=(aa-1)PolyGamma[2,aa]/4+(PolyGamma[1,aa]-Zeta[2])/2+3(aa-1)Zeta[3]/2;
 err=Abs[val-N[target,55]];
 mu=Min[aa,1];mm=Max[1,Abs[aa-1]];bound=mm^2(1+aa)Exp[-mu cut](cut^3/mu+3cut^2/mu^2+6cut/mu^3+6/mu^4)/6;
 AppendTo[rows,<|"kind"->"trigamma-square-double-Laplace","shift"->ToString[aa,InputForm],"absolute_residual"->ToString[err,InputForm],"analytic_tail_bound"->ToString[N[bound,55],InputForm],"passed"->TrueQ[err<10^-24&&bound<10^-30]|>],{aa,{1/2,3/2,4/3,1+Sqrt[2]}}];
record=<|"engine"->$Version,"exact_checks"->Length[exact],"exact_passed"->And@@exact,"exact_results"->exact,"numerical_checks"->Length[rows],"rows"->rows,"contact_working_precision"->60,"double_Laplace_working_precision"->55,"finite_laplace_cutoff"->cut,"interval_certified"->False,"missing_atom_control"-><|"omitted_atom_mean"->ToString[-Pi^2/3,InputForm],"restored_mean"->FullSimplify[-Pi^2/3+Pi^2/3],"rejected"->TrueQ[Pi^2/3!=0]|>,"all_pass"->(And@@exact&&And@@Lookup[rows,"passed"]),"scope"->"Native exact Euler partial fractions and first-resonance Bernoulli constants; independent ordinary/subtracted Fourier moments and finite double-Laplace quadratures with analytic exponential-tail bounds. Endpoint point values of integrable singular callbacks do not affect integrals. Numerical agreement is diagnostic, not interval accuracy or the all-index analytic proof."|>;
Export[FileNameJoin[{DirectoryName[$InputFileName],"periodic-contact-dougall-native.json"}],record,"RawJSON"];
Print[<|"exact_checks"->Length[exact],"numerical_checks"->Length[rows],"all_pass"->record["all_pass"]|>];Exit[If[TrueQ[record["all_pass"]],0,1]];
