(* Run with: wolframscript -file test_HahnRational.wl
   The package may also be loaded in a notebook before evaluating this file. *)
If[!MemberQ[$Packages, "HahnRational`"],
  Get[FileNameJoin[{DirectoryName[$InputFileName], "HahnRational.wl"}]]];
Clear[u,t,s];
checks = {};
check[name_, test_] := AppendTo[checks, name -> TrueQ[test]];
h[e_] := HCreate[{u,t},e];
one = h[1]; zero = h[0];
check["normalization", HEqualQ[h[(1-t^2)/(1-t)],h[1+t]]];
check["rank-sensitive leading term", HValuation[h[u+t^100]] === {0,100}];
check["rank-sensitive inequality", HCompare[h[u],h[t^100]] === -1];
check["cancellation crosses a rank", HValuation[HAdd[h[1/(1-t)+u],h[-1/(1-t)]]] === {1,0}];
check["inversion", HEqualQ[HMul[h[t-u],HInv[h[t-u]]],one]];
check["inverse valuation", HValuation[HInv[h[t-u]]] === {0,-1}];
check["negative value", HSign[h[-t/(1-u)]] === -1];
check["nonreal ordering rejected", FailureQ[HSign[h[t+I u]]]];
check["nonreal pair ordering rejected", FailureQ[HCompare[h[I],h[1+I]]]];
check["zero", HZeroQ[HAdd[h[t],h[-t]]]];
check["zero valuation", HValuation[zero] === Infinity];
check["zero inverse rejected", FailureQ[HInv[zero]]];
check["zero negative power rejected", FailureQ[HPower[zero,-1]]];
check["coefficient domain rejected", FailureQ[h[Pi+t]]];
check["machine coefficients rejected", FailureQ[h[1.0+t]]];
check["nonrational expression rejected", FailureQ[h[Exp[t]]]];
check["fractional powers need parent extension", FailureQ[h[Sqrt[t]]]];
check["duplicate parent rejected", FailureQ[HCreate[{t,t},1]]];
check["different parents rejected", FailureQ[HAdd[h[t],HCreate[{t,u},t]]]];
check["finite standard part", HStandardPart[h[(2+3 I+t)/(1-u)]] === 2+3 I];
check["infinitesimal standard part", HStandardPart[h[u/t^20]] === 0];
check["infinite standard part rejected", FailureQ[HStandardPart[h[t/u]]]];
check["complex norm", HEqualQ[HNormSquared[h[t+I u]],h[t^2+u^2]]];
check["real part", HEqualQ[HRe[h[(t+I u)/(1-I t)]],h[(t-u t)/(1+t^2)]]];
check["imaginary part", HEqualQ[HIm[h[(t+I u)/(1-I t)]],h[(t^2+u)/(1+t^2)]]];
check["exact geometric tail", HEqualQ[
 HAdd[h[1/(1-t)],h[-Sum[t^j,{j,0,9}]]],h[t^10/(1-t)]]];
check["leading coefficient of quotient", HLeadingCoefficient[h[(3t+u)/(2t^2-u)]] === 3/2];
check["negative denominator normalization", HEqualQ[h[(t-u)/(u-1)],h[(u-t)/(1-u)]]];
SeedRandom[20260921];
Do[
  p = Sum[RandomInteger[{-5,5}] u^RandomInteger[{0,3}] t^RandomInteger[{0,4}],{5}];
  q = Sum[RandomInteger[{-5,5}] u^RandomInteger[{0,3}] t^RandomInteger[{0,4}],{5}];
  a = h[p/(1+t^2+u^2)]; b = h[q/(1+t^4+u^4)];
  check["distributive-"<>ToString[k], HEqualQ[HMul[HAdd[a,b],h[1+t]],
    HAdd[HMul[a,h[1+t]],HMul[b,h[1+t]]]]];
  check["conjugate-"<>ToString[k], HEqualQ[HConjugate[HConjugate[a]],a]];
  If[!HZeroQ[a],
    check["valuation-product-"<>ToString[k],
      HValuation[HMul[a,h[t-u]]] === HValuation[a]+{0,1}]];
, {k,20}];
report = <|"Kernel"->$Version,"Tests"->Length[checks],
 "Passed"->Count[Last /@ checks,True],
 "Failures"->Select[checks,!Last[#]&]|>;
Print[InputForm[report]];
If[Length[report["Failures"]] > 0, Exit[1]];
