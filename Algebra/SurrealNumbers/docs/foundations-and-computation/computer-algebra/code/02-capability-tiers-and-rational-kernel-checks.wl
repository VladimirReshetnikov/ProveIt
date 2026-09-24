(* Run after Get["RationalHahn.wl"]. All checks are exact, finite tests.
   They do not constitute a formal verification of surreal/Hahn theory. *)
Clear[t,s,z,u];
checks = {};
check[name_String, condition_] := AppendTo[checks, name -> TrueQ[condition]];
a=RHMake[1+t,t,{t,s}]; b=RHMake[t,1,{t,s}];
one=RHMake[1,1,{t,s}]; zero=RHMake[0,1,{t,s}];
check["cancellation", RHCompare[RHMake[(1+t)^2-1-2t,t^2,{t,s}],one]===0];
check["inverse product", RHCompare[RHMultiply[a,RHInverse[a]],one]===0];
check["addition subtraction", RHCompare[RHSubtract[RHAdd[a,b],b],a]===0];
check["negative denominator", RHSign[RHMake[1,-t,{t,s}]]===-1];
check["higher rank dominates", RHCompare[RHMake[s,1,{t,s}],RHMake[t^10000,1,{t,s}]]===-1];
check["infinite second scale", RHSign[RHMake[t^10000-s,1,{t,s}]]===1];
check["valuation rational", RHValuation[RHMake[s+t^2,t^3,{t,s}]]==={-1,0}];
check["valuation cancellation", RHValuation[RHMake[(1+t)s-s,1,{t,s}]]==={1,1}];
check["zero valuation marker", RHValuation[zero]===Infinity];
check["zero sign", RHSign[zero]===0];
check["zero standard part", RHStandardPart[zero]===0];
check["finite rational standard part", RHStandardPart[RHMake[3+2t,2-t,{t,s}]]===3/2];
check["small standard part", RHStandardPart[RHMake[s,t^10000,{t,s}]]===0];
check["infinite rejected by standard part", FailureQ[RHStandardPart[a]]];
check["zero inverse rejected", FailureQ[RHInverse[zero]]];
check["zero denominator rejected", FailureQ[RHMake[1,0,{t,s}]]];
check["inexact coefficient rejected", FailureQ[RHMake[1.0+t,1,{t,s}]]];
check["transcendental coefficient rejected", FailureQ[RHMake[Pi+t,1,{t,s}]]];
check["nonpolynomial rejected", FailureQ[RHMake[Sin[t],1,{t,s}]]];
check["domain mismatch rejected", FailureQ[RHAdd[a,RHMake[1,1,{t}]]]];
check["duplicate variables rejected", FailureQ[RHMake[1,1,{t,t}]]];
check["empty variables rejected", FailureQ[RHMake[1,1,{}]]];
check["geometric series", Normal[Series[t/(1+t),{t,0,6}]]===Sum[(-1)^(k-1)t^k,{k,1,6}]];
check["square root coefficients", Expand[Normal[Series[Sqrt[1+t^2],{t,0,6}]]-(1+t^2/2-t^4/8+t^6/16)]===0];
check["finite sine coefficients", Simplify[Normal[Series[Sin[Pi/6+t],{t,0,3}]]-(1/2+Sqrt[3]t/2-t^2/4-Sqrt[3]t^3/12)]===0];
(* At positive u, ArcCos[1-u^2] = 2 ArcSin[u/Sqrt[2]]. *)
check["inverse cosine endpoint", Simplify[Normal[Series[2 ArcSin[u/Sqrt[2]]/(Sqrt[2]u),{u,0,6}]]-(1+u^2/12+3u^4/160+5u^6/896)]===0];
check["inverse tangent coefficients", Expand[Normal[Series[ArcTan[t],{t,0,7}]]-(t-t^3/3+t^5/5-t^7/7)]===0];
check["ramified quadratic positive root", Expand[(1+u)^2-2(1+u)+1-u^2]===0];
check["ramified quadratic negative root", Expand[(1-u)^2-2(1-u)+1-u^2]===0];
check["Cayley unit circle", Together[((1-t^2)/(1+t^2))^2+(2t/(1+t^2))^2-1]===0];
check["residue cancellation coefficients", Expand[Normal[Series[Sinh[u]/u,{u,0,8}]]-Sum[u^(2k)/(2k+1)!,{k,0,4}]]===0];
check["implicit inverse sine", Normal[Series[Sin[t+t^3/6+3t^5/40+5t^7/112]-t,{t,0,8}]]===0];
check["formal derivative convention", D[t^3,t]===3t^2 && Expand[-t^2 D[t^3,t]+3t^4]===0];
check["trigonometric algebraization", Together[((u-1/u)/(2I))^2-t-(-u^4+(2-4t)u^2-1)/(4u^2)]===0];
<|"KernelVersion"->$Version,"Checks"->Length[checks],
  "Passed"->Count[Last /@ checks,True],"Failures"->Select[checks,!Last[#]&],
  "Details"->Association[checks]|>
