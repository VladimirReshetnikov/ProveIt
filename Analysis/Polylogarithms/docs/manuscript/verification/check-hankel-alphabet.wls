baseDirectory=DirectoryName[$InputFileName];
l=-Log[1-z];
u=PolyLog[2,z]/(z(1-z))-1/(1-z);
v=(PolyLog[2,z]+l^2-2l)/(z(1-z))+1/(1-z);
n=(3z-2)PolyLog[2,z]+(1-z)(3l-l^2)-z;
g=n/(z(1-z)^2);
series=Normal[Series[g,{z,0,30}]];
wrong=(n+PolyLog[2,z])/(z(1-z)^2);
checks=<|
 "shifted_generating_identity"->TrueQ[FullSimplify[z D[u,z]-v-g,Assumptions->0<z<1]==0],
 "all_Taylor_coefficients_agree_through_thirty"->And@@Table[TrueQ[Coefficient[series,z,m]==m(HarmonicNumber[m+1,2]-1)-(HarmonicNumber[m+1]-1)^2],{m,0,30}],
 "numerator_derivative"->TrueQ[FullSimplify[D[n,z]-(3PolyLog[2,z]+l^2-2l+2-2l/z),Assumptions->0<z<1]==0],
 "lower_boundary"->TrueQ[Limit[n/z,z->0]==0],
 "upper_boundary"->TrueQ[Limit[n,z->1,Direction->"FromBelow"]==Zeta[2]-1],
 "combined_cancellation_primitive"->TrueQ[FullSimplify[D[l/z-l,z]-(1/z-l/z^2),Assumptions->0<z<1]==0],
 "combined_cancellation_lower_boundary"->TrueQ[Limit[l/z-l,z->0]==1],
 "combined_cancellation_upper_boundary"->TrueQ[Limit[l/z-l,z->1,Direction->"FromBelow"]==0],
 "wrong_dilog_coefficient_rejected"->TrueQ[Limit[wrong,z->0]==1],
 "empty_word_wrong_anchor_has_log_pole"->TrueQ[Residue[1/(z(1-z)),{z,0}]==1]&&TrueQ[Residue[(z/(1-z))/z,{z,0}]==0],
 "Euler_beta_weight"->TrueQ[FullSimplify[Beta[m,3]/2-1/(m(m+1)(m+2)),Assumptions->m>0]==0]
|>;
out=<|"all_pass"->And@@Values[checks],"checks"->checks,"engine"->$Version,"maximum_cutoff"->30,"Taylor_coefficient_checks"->31,"exact_symbolic_arithmetic"->True,"scope"->"Native exact generating identity, finite Taylor coefficients, endpoint cancellation derivatives/boundaries and controls. Ordinary endpoint values follow the manuscript's analytic integration proof; floating-point evidence is separate."|>;
Export[FileNameJoin[{baseDirectory,"hankel-alphabet-native.json"}],out,"RawJSON"];
Print[out];If[!TrueQ[out["all_pass"]],Exit[1]];
