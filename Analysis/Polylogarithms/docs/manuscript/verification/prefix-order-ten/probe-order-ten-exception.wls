baseDirectory = DirectoryName[$InputFileName];
expectedCertificate = Import[FileNameJoin[{baseDirectory,"order-ten-exception-probe.json"}],"RawJSON"];
orderA = 5; parameterB = 962;
Clear[safeInteger,safeRational,fallingProduct];
safeInteger[text_String] := Module[{negative=StringStartsQ[text,"-"],digits},
 If[!StringMatchQ[text,RegularExpression["-?[0-9]+"]],Print["Invalid integer input"];Exit[2]];
 digits=If[negative,StringDrop[text,1],text];If[negative,-1,1] FromDigits[digits]];
safeRational[text_String] := Module[{parts=StringSplit[text,"/"]},
 If[Length[parts]==1,Return[safeInteger[First[parts]]]];
 If[Length[parts]!=2,Exit[2]];safeInteger[parts[[1]]]/safeInteger[parts[[2]]]];
fallingProduct[value_,length_] := Product[value-offset,{offset,0,length-1}];
bernoulliValues=Table[2 BernoulliB[2 parameterB-2 index],{index,1,2 orderA-1}];
computedMatrix=Table[Module[{node=parameterB-orderA+row,upper,lower,coefficients,polynomial,firstPart,correction},
 polynomial=(2 node+2-variable) fallingProduct[4 node+2-variable,2 row];
 coefficients=Table[Sum[(-1)^(degree-position) Binomial[degree,position] (polynomial/.variable->position),{position,0,degree}]/degree!,{degree,0,2 row+1}];
 upper=2 parameterB-2 orderA+2+2 column;lower=2(node-column)+1;
 firstPart=fallingProduct[2 node,2 column] Product[2 node+3+offset,{offset,0,2 column-1}]/(2 column+1)!;
 correction=Sum[coefficients[[2 index+2]] fallingProduct[lower,2 index+1] bernoulliValues[[orderA-row+column+index]],{index,0,row}];
 2 firstPart+upper! correction/((2 node+1)(2 node+2)(2 column+2)! lower!)],{row,0,orderA-1},{column,0,orderA-1}];
expectedMatrix=Map[safeRational,expectedCertificate["matrix"],{2}];
expectedInverse=Map[safeRational,expectedCertificate["inverse"],{2}];
expectedBernoullis=Table[safeRational[expectedCertificate["bernoulli_coordinates"][ToString[index]]],{index,1,2 orderA-1}];
checks=<|"Bernoulli_values_match"->(bernoulliValues===expectedBernoullis),"matrix_matches"->(computedMatrix===expectedMatrix),
 "left_inverse_identity"->(computedMatrix.expectedInverse===IdentityMatrix[orderA]),
 "right_inverse_identity"->(expectedInverse.computedMatrix===IdentityMatrix[orderA]),
 "determinant_matches"->(Det[computedMatrix]===safeRational[expectedCertificate["determinant"]]),"determinant_nonzero"->(Det[computedMatrix]!=0)|>;
result=<|"engine"->$Version,"a"->orderA,"b"->parameterB,"checks"->checks,"all_pass"->And@@Values[checks],
 "exact_rational_arithmetic"->True,"scope"->"Independent native Bernoulli and finite-difference construction of the five-square exceptional matrix, comparison with every Python coefficient, both inverse products and the exact determinant. The full family additionally requires the audited infinite congruence and eventual-rank proofs; no arithmetic independence or Gaussian identity is asserted."|>;
Export[FileNameJoin[{baseDirectory,"order-ten-exception-native.json"}],result,"RawJSON"];
Print["Native exact exceptional case: ",result["all_pass"]];
Exit[If[result["all_pass"],0,1]];
