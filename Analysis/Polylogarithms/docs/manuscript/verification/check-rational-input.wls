baseDirectory=DirectoryName[$InputFileName];
w=ArcSinh[z/2];
y=z/(2+Sqrt[4+z^2]);
l=Log[1-z];
normal2=2 w^2;
h1=-z-(1-z)l;
h2=-2 w^2+(1-z)l^2/2-z PolyLog[2,z]+2 z (PolyLog[2,y]-PolyLog[2,-y]);
sq=Sqrt[4+z^2];
formalH=-2 ww^2+(1-z)ll^2/2-z pp+2 z bb;
formalDH=D[formalH,z]+D[formalH,ww]/ss-D[formalH,ll]/(1-z)-D[formalH,pp]ll/z+D[formalH,bb]2 ww/(z ss);
n2[m_Integer]:=If[EvenQ[m],(-1)^(m/2-1)((m/2-1)!)^2,0];
normalSeries=Normal[Series[normal2,{z,0,30}]];
primitiveSeries=Normal[Series[h2,{z,0,30}]];
wrongDilog=-2 w^2+(1-z)l^2/2-z PolyLog[2,z]+2 z (PolyLog[2,y]+PolyLog[2,-y]);
asinhDerivative=ww^2-2 ww z/ss+2 t ww/(x ss);
logDerivative=ll^2+2(x-t)ll z/(x(1-z))-2 t ll/x;
checks=<|
 "normal_ODE"->TrueQ[FullSimplify[(z^2+4)D[normal2,{z,2}]+z D[normal2,z]-4]==0],
 "linear_primitive_ODE"->TrueQ[FullSimplify[h1-z D[h1,z]+l+z,Assumptions->0<z<1]==0],
 "local_log_ratio_algebra"->TrueQ[FullSimplify[(1+y)/(1-y)-(z+sq)/2]==0],
 "local_log_germ"->TrueQ[FullSimplify[Exp[w]-(z+sq)/2,Assumptions->0<z<1]==0]&&TrueQ[(w/.z->0)==0],
 "dilog_composition_derivative_factor"->TrueQ[FullSimplify[D[y,z]/y-2/(z sq)]==0],
 "quadratic_primitive_ODE_from_local_branches"->TrueQ[Expand[formalH-z formalDH-(ll^2/2-2 ww^2)]==0],
 "normalization"->TrueQ[Limit[h2/z,z->0]==0],
 "normal_coefficients"->And@@Table[TrueQ[FullSimplify[m! Coefficient[normalSeries,z,m]-n2[m]]==0],{m,2,30}],
 "primitive_coefficients"->And@@Table[TrueQ[FullSimplify[m! Coefficient[primitiveSeries,z,m]-(n2[m]/(m-1)-(m-2)!HarmonicNumber[m-1])]==0],{m,2,30}],
 "asinh_antiderivative_from_local_branches"->TrueQ[FullSimplify[(asinhDerivative-ww^2)/.z->t/x]==0],
 "log_antiderivative_from_local_branches"->TrueQ[FullSimplify[(logDerivative-ll^2)/.z->t/x]==0],
 "wrong_dilog_difference_rejected"->TrueQ[Coefficient[Normal[Series[wrongDilog,{z,0,2}]],z,2]==-1],
 "wrong_added_constant_rejected"->TrueQ[Limit[(h2+z)/z,z->0]==1],
 "wrong_square_root_germ_rejected"->TrueQ[Coefficient[Normal[Series[z/(2-sq),{z,0,1}]],z,-1]==-4]|>;
record=<|"all_pass"->And@@Values[checks],"checks"->checks,"engine"->$Version,"maximum_weight"->30,"exact_symbolic_arithmetic"->True,"scope"->"Exact native ODE, local logarithm-germ algebra and every quadratic Taylor coefficient through weight thirty. The composed dilogarithm derivative is justified by the verified local log ratio and zero germ; it is not an unqualified global branch substitution."|>;
Export[FileNameJoin[{baseDirectory,"rational-input-native.json"}],record,"RawJSON"];
Print[record];Exit[If[record["all_pass"],0,1]];
