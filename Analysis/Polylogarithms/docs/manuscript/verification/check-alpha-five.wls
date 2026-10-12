baseDirectory = DirectoryName[$InputFileName];
printedCoefficient = (EulerGamma^5-10 EulerGamma^3 Zeta[2]+20 EulerGamma^2 Zeta[3]+15 EulerGamma Zeta[2]^2-30 EulerGamma Zeta[4]-20 Zeta[2] Zeta[3]+24 Zeta[5])/120;
nativeCoefficient = Coefficient[Normal[Series[1/Gamma[1+u],{u,0,5}]],u,5];
checks = <|"native_Gamma_Taylor_coefficient_matches"->TrueQ[FullSimplify[nativeCoefficient-printedCoefficient]==0],"coefficient_degree"->TrueQ[Exponent[Normal[Series[1/Gamma[1+u],{u,0,5}]],u]==5]|>;
result = <|"engine"->$Version,"degree"->5,"checks"->checks,"all_pass"->And@@Values[checks],"exact_symbolic_arithmetic"->True,"scope"->"Independent native reciprocal-Gamma Taylor audit of the corrected fifth coefficient. This is an exact symbolic coefficient check, not a global manuscript proof or interval certificate."|>;
Export[FileNameJoin[{baseDirectory,"alpha-five-native.json"}],result,"RawJSON"];
Print["Native exact fifth Gamma coefficient: ",result["all_pass"]];
Exit[If[result["all_pass"],0,1]];
