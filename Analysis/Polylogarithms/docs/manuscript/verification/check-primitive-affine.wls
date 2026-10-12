baseDirectory = DirectoryName[$InputFileName];
z = b t^2/2;
normalFactor = (Cosh[z] + Sinh[z]/z - z SinhIntegral[z])/2;
normalGenerator = Exp[t (a+b x)] normalFactor;
primitiveGenerator = t/2 + t Exp[t (a+b x)] (Exp[-z]-normalFactor)/(2 z);
rawGenerator = Exp[t (a+b x)-z];
h[j_Integer] := (-1)^(j+1)/(2^(j+1) (j+1)!) (1+If[OddQ[j],1/(j (j+2)),0]);
series = Normal[Series[primitiveGenerator /. x->0,{t,0,18}]];
coefficientChecks = Table[TrueQ[FullSimplify[m! Coefficient[series,t,m] - m! Sum[h[j] a^(m-2 j-1) b^j/(m-2 j-1)!,{j,0,Floor[(m-1)/2]}]]==0],{m,2,18}];
checks = <|
 "affine_translation_derivative" -> TrueQ[FullSimplify[D[primitiveGenerator,x]-(rawGenerator-normalGenerator),Assumptions->b!=0&&t!=0]==0],
 "weight_one_zero_constant_normalization" -> TrueQ[Coefficient[series,t,1]==0],
 "missing_t_over_two_rejected" -> TrueQ[Coefficient[series-t/2,t,1]==-1/2],
 "constant_input_removable_limit" -> TrueQ[FullSimplify[Limit[primitiveGenerator,b->0]-t(1-Exp[t a])/2]==0],
 "all_affine_coefficients_through_eighteen" -> And@@coefficientChecks|>;
result = <|"engine"->$Version,"checks"->checks,"all_pass"->And@@Values[checks],"coefficient_degrees"->{2,18},"exact_symbolic_arithmetic"->True,"scope"->"Independent native symbolic derivative, removable constant-input limit and every affine compensator coefficient through degree eighteen. The required t/2 term enforces zero-constant normalization. Exact finite symbolic checks are separate from the manuscript all-weight and analytic convergence proofs."|>;
Export[FileNameJoin[{baseDirectory,"primitive-affine-native.json"}],result,"RawJSON"];
Print["Native affine primitive audit: ",result["all_pass"]];
Exit[If[result["all_pass"],0,1]];
