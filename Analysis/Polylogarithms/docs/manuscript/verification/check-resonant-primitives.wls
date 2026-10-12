baseDirectory=DirectoryName[$InputFileName];
d[m_,e_]:=Product[1+e/j,{j,1,m}]/Gamma[1-e];
j0=-Log[1-Exp[-t]];
j1=Zeta[2]-PolyLog[2,Exp[-t]]-t;
j2=2(PolyLog[3,Exp[-t]]-Zeta[3]+t Zeta[2])-3t^2/2;
twice=j2/2+3t^2/4;
core=(1-t^e)/e;
checks=<|
 "normalizer_recurrence"->And@@Table[TrueQ[FullSimplify[d[m,e]-(1+e/m)d[m-1,e]]==0],{m,1,12}],
 "Gamma_pole_normalization"->And@@Table[TrueQ[FullSimplify[(-1)^m m! d[m,e] Gamma[-m-e]+1/e,Assumptions->0<e<1]==0],{m,0,8}],
 "core_lowering_endpoint"->TrueQ[FullSimplify[m core+t D[core,t]-(m+e)core+1,Assumptions->t>0&&e>0]==0],
 "dilog_jet_lowering"->TrueQ[FullSimplify[D[j1,t]-j0+1,Assumptions->t>0]==0],
 "trilog_jet_lowering"->TrueQ[FullSimplify[D[j2,t]-2j1+t,Assumptions->t>0]==0],
 "twice_primitive"->TrueQ[FullSimplify[D[twice,{t,2}]-j0,Assumptions->t>0]==0],
 "twice_primitive_zero_endpoint"->TrueQ[Limit[twice,t->0,Direction->"FromAbove"]==0],
 "twice_primitive_derivative_zero_endpoint"->TrueQ[Limit[D[twice,t],t->0,Direction->"FromAbove"]==0],
 "missing_polynomial_rejected"->TrueQ[FullSimplify[D[j2/2,{t,2}]-j0,Assumptions->t>0]==-3/2]
|>;
out=<|"all_pass"->And@@Values[checks],"checks"->checks,"engine"->$Version,
"scope"->"Exact finite Gamma recurrence, pole normalization, low-order lowering and anchored repeated-primitive identities. The all-index result is proved in the manuscript.","exact_symbolic_arithmetic"->True|>;
Export[FileNameJoin[{baseDirectory,"resonant-primitives-native.json"}],out,"RawJSON"];
Print[out];If[!TrueQ[out["all_pass"]],Exit[1]];
