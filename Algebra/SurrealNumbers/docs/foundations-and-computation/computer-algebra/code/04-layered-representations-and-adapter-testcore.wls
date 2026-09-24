(* Run with wolframscript -file TestCore.wls, from any working directory. *)
Get[FileNameJoin[{DirectoryName[$InputFileName], "SurrealCASCore.wl"}]];
checks = {};
check[name_, condition_] := AppendTo[checks, {name, TrueQ[condition]}];
one = HCreate[{{{0},1}},1];
t = HCreate[{{{1},1}},1];
zero = HCreate[{},1];
a = HAdd[one,HNegate[t]];
b = HAdd[one,t];
check["difference of squares", HMultiply[a,b] === HAdd[one,HNegate[HPower[t,2]]]];
check["cancellation", HAdd[t,HNegate[t]] === zero];
check["valuation zero", HValuation[zero] === Infinity];
check["fraction identity", REqual[RCreate[one,a],RCreate[b,HMultiply[a,b]]]];
check["zero denominator", MatchQ[RCreate[one,zero],_Failure]];
check["inverse zero", MatchQ[RInverse[RCreate[zero,one]],_Failure]];
check["bad coefficient", MatchQ[HCreate[{{{1},0.5}},1],_Failure]];
check["bad rank", MatchQ[HAdd[t,HCreate[{{{0,1},1}},2]],_Failure]];
check["bad exponent", MatchQ[HCreate[{{{Sqrt[2]},1}},1],_Failure]];
check["bad power", MatchQ[HPower[t,-1],_Failure]];
z = HCreate[{{{0},1+I},{{1/2},2-I}},1];
check["conjugation involution", HConjugate[HConjugate[z]] === z];
check["complex ordering rejected", MatchQ[HCompareReal[z,z],_Failure]];
check["order", HCompareReal[HAdd[one,t],one] === 1];
s = HCreate[{{{0,1},1}},2]; u = HCreate[{{{1,0},1}},2];
check["lex hierarchy", HCompareReal[HPower[s,100],u] === 1];
check["fraction valuation", RValuation[RCreate[t,HPower[t,3]]] === {-2}];
check["fraction addition", REqual[RAdd[RCreate[one,a],RCreate[one,b]],RCreate[HAdd[a,b],HMultiply[a,b]]]];
check["fraction multiplication", REqual[RMultiply[RCreate[a,b],RCreate[b,a]],RCreate[one,one]]];
check["fraction inverse", REqual[RInverse[RCreate[one,a]],RCreate[a,one]]];
check["zero product", HMultiply[zero,t] === zero];
check["duplicate exponents", HCreate[{{{1/2},2},{{1/2},3}},1] === HCreate[{{{1/2},5}},1]];
SeedRandom[20260921];
Do[
  aa=HCreate[Table[{{RandomInteger[{-4,6}]/2},RandomInteger[{-4,4}]+I RandomInteger[{-3,3}]},{4}],1];
  bb=HCreate[Table[{{RandomInteger[{-4,6}]/2},RandomInteger[{-4,4}]+I RandomInteger[{-3,3}]},{4}],1];
  cc=HCreate[Table[{{RandomInteger[{-4,6}]/2},RandomInteger[{-4,4}]+I RandomInteger[{-3,3}]},{4}],1];
  check["distributivity "<>ToString[k],HMultiply[aa,HAdd[bb,cc]] === HAdd[HMultiply[aa,bb],HMultiply[aa,cc]]];
  check["multiplication conjugation "<>ToString[k],HConjugate[HMultiply[aa,bb]] === HMultiply[HConjugate[aa],HConjugate[bb]]];
  If[HValuation[aa] =!= Infinity && HValuation[bb] =!= Infinity,
    check["multiplicative valuation "<>ToString[k],HValuation[HMultiply[aa,bb]] === HValuation[aa]+HValuation[bb]]],
  {k,30}];
report=<|"Kernel"->$Version,"Checks"->Length[checks],
  "Passed"->Count[checks,{_,True}],"Failures"->Select[checks,!Last[#]&]|>;
Print[InputForm[report]];
If[report["Failures"] =!= {},Exit[1]];
