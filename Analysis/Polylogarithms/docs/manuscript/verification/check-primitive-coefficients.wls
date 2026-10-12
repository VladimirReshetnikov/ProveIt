baseDirectory=DirectoryName[$InputFileName];
maximumWeight=16;
vars=Table[Symbol["pgcJet"<>ToString[j]],{j,0,maximumWeight}];
delta[p_]:=Expand[Sum[vars[[j+2]] D[p,vars[[j+1]]],{j,0,maximumWeight-1}]];
cp[r_Integer]:=((1+v)^(r+1)-(v-1)^(r+1))/(2^(r+1) (r+1)!);
exponents[partition_]:=Table[Count[partition,j+1],{j,0,maximumWeight}];
monomial[a_]:=Times@@MapThread[Power,{vars,a}];
normalCoefficient[a_,m_]:=Module[{d,l},
 If[m==0,Return[1]];
 d=Max[Select[Range[0,maximumWeight],a[[#+1]]>0&]];
 If[d==0,Return[1]];
 l=Sum[j a[[j+1]],{j,0,maximumWeight}];
 If[a[[d+1]]==1||OddQ[l],Return[0]];
 (-1)^d m!/(4^d d! (d+1)! Times@@(Factorial/@a))
 Integrate[Expand[(1-v^2)^d cp[d]^(a[[d+1]]-2) Product[cp[j]^a[[j+1]],{j,1,d-1}]],{v,0,1}]];
primitiveCoefficient[a_,m_]:=Module[{d,l},
 If[m<2,Return[0]];
 d=Max[Select[Range[0,maximumWeight],a[[#+1]]>0&]];
 If[d==0,Return[-m/2]];
 l=Sum[j a[[j+1]],{j,0,maximumWeight}];
 (-1)^(l+1) m!/(2^(d+2) (d+1)! Times@@(Factorial/@a))
 Integrate[Expand[(1+v)^(d+1) cp[d]^(a[[d+1]]-1) Product[cp[j]^a[[j+1]],{j,1,d-1}]],{v,-1,1}]];
raw=1;rows={};normals={};primitives={};
Do[
 If[m>0,raw=Expand[vars[[1]] raw-delta[raw]]];
 normal=Expand[Total[Map[Function[part,With[{a=exponents[part]},normalCoefficient[a,m] monomial[a]]],IntegerPartitions[m]]]];
 primitive=If[m<2,0,Expand[Total[Map[Function[part,With[{a=exponents[part]},primitiveCoefficient[a,m] monomial[a]]],IntegerPartitions[m-1]]]]];
 good=TrueQ[Expand[raw-normal-delta[primitive]]==0];
 AppendTo[rows,<|"weight"->m,"identity_passed"->good,"primitive_terms"->Length[CoefficientRules[primitive,vars]]|>];
 AppendTo[normals,normal];AppendTo[primitives,primitive];
 Print["Native primitive coefficient identity weight ",m,": ",good];
 If[!good,Exit[1]],{m,0,maximumWeight}];
linearChecks=Table[TrueQ[Coefficient[primitives[[r+3]],vars[[r+1]]]==(-1)^(r+1)],{r,1,maximumWeight-2}];
mixedChecks=Table[TrueQ[Coefficient[Coefficient[primitives[[r+5]],vars[[r+1]]],vars[[2]]]==(-1)^r (r+1)(r+4)/2],{r,2,maximumWeight-4}];
control=Expand[vars[[1]]^4-6 vars[[1]]^2 vars[[2]]+3 vars[[2]]^2+4 vars[[1]] vars[[3]]-vars[[4]]-normals[[5]]-delta[primitives[[5]]-vars[[3]]]];
checks=<|"all_raw_normal_primitive_identities"->And@@Lookup[rows,"identity_passed"],"weight_one_zero_constant"->TrueQ[primitives[[2]]==0],"all_linear_coefficients"->And@@linearChecks,"all_mixed_linear_coefficients"->And@@mixedChecks,"wrong_kernel_factor_rejected"->TrueQ[Expand[control-vars[[4]]]==0]&&UnsameQ[control,0]|>;
result=<|"engine"->$Version,"maximum_weight"->maximumWeight,"exact_symbolic_arithmetic"->True,"rows"->rows,"checks"->checks,"all_pass"->And@@Values[checks],"scope"->"Independent native symbolic Bell recurrence compared with the established normal Beta coefficients and new primitive polynomial-integral coefficients at every weight zero through sixteen. Exact differentiation, linear/mixed coefficient families and a coefficient corruption control are checked. This finite replay is separate from the manuscript all-weight and analytic proofs."|>;
Export[FileNameJoin[{baseDirectory,"primitive-coefficient-native.json"}],result,"RawJSON"];
Print["Native all-index primitive coefficient audit: ",result["all_pass"]];
Exit[If[result["all_pass"],0,1]];
