(* Executed through the connected Wolfram kernel, 8 October 2026.
   Exact reference calculation; no claim about Renegar-style complexity. *)
Clear[qm, A, B, t];
qm[p_, q_] := {
 p[[1]] q[[1]]-p[[2]] q[[2]]-p[[3]] q[[3]]-p[[4]] q[[4]],
 p[[1]] q[[2]]+p[[2]] q[[1]]+p[[3]] q[[4]]-p[[4]] q[[3]],
 p[[1]] q[[3]]-p[[2]] q[[4]]+p[[3]] q[[1]]+p[[4]] q[[2]],
 p[[1]] q[[4]]+p[[2]] q[[3]]-p[[3]] q[[2]]+p[[4]] q[[1]]};
A = {0, 1, 0, 0};
B = {0, (1-t^2)/(1+t^2), 2t/(1+t^2), 0};
tr = Numerator[Together[#]] & /@ (qm[qm[A,B],A]-qm[qm[B,A],B]);
cy = Numerator[Together[#]] & /@ (A-B);
wrong = Numerator[Together[#]] & /@ (qm[A,A]-qm[qm[B,B],B]);
Y = {1/2, 0, Sqrt[3]/2, 0};
<|"Version" -> $Version, "TrefoilResiduals" -> tr,
 "TrefoilGCD" -> PolynomialGCD@@DeleteCases[tr,0],
 "TrefoilPositiveSolutions" -> Reduce[t>0 && And@@Thread[tr==0],t,Reals],
 "CyclicFeasibility" -> Resolve[Exists[t,t>0 && And@@Thread[cy==0]],Reals],
 "NonmeridionalTracelessFeasibility" -> Resolve[Exists[t,t>0 && And@@Thread[wrong==0]],Reals],
 "ActualNonmeridionalWitnessRelation" -> Simplify[qm[A,A]-qm[qm[Y,Y],Y]],
 "ActualWitnessCommutatorDifference" -> Simplify[qm[A,Y]-qm[Y,A]]|>
