(* Optional independent exact check. Evaluated in the connected kernel. *)
Clear[t, d, u, k];
f1 = Expand[(1 + 2 t) (1 + 3 t) (1 + 4 t)];
g1 = 1 + 8 t + 19 t^2 + 11 t^3;
h1 = 1 + 7 t + 13 t^2;
f2 = Expand[(1 + 2 t) (1 + 3 t)^2];
g2 = 1 + 7 t + 15 t^2 + 8 t^3;
h2 = 1 + 6 t + 10 t^2;
u = d (d - 1); k = (d - 1)/(d - 2);
deltaCube = Factor[k u^2 - u^2 - u/3 - 1/27];
<|"Version" -> $Version,
  "CoefficientLists" -> (CoefficientList[#, t] & /@ {f1,g1,h1,f2,g2,h2}),
  "DecompositionIdentities" -> {Expand[f1-g1-t h1], Expand[f2-g2-t h2]},
  "Discriminants" -> (Discriminant[#, t] & /@ {f1,g1,h1,f2,g2,h2}),
  "RealRootCountsMain" -> (CountRoots[#, {t,-Infinity,Infinity}] & /@ {f1,g1,h1}),
  "DeltaCubeDifference" -> deltaCube,
  (* False means there is no real d>=3 violating strict positivity. *)
  "DeltaCubePositiveForRealDAtLeast3" ->
    Reduce[d >= 3 && deltaCube <= 0, d, Reals]|>
