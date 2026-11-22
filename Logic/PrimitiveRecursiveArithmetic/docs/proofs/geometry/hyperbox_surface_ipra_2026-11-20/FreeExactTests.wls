(* Run with wolframscript -file FreeExactTests.wls in this directory. *)
Get[FileNameJoin[{DirectoryName[$InputFileName],"FreeExact.wl"}]];
check[condition_, label_] := If[!TrueQ[condition], Print["FAILED ",label];Exit[1]];
check[hbVisibility[{0,0},{2,2},{}]===True, "empty word"];
check[hbVisibility[{0,0},{2,2},{{{1,1},{0,2}},{{1,2},{2,2}}}]===True,
      "ordered gate times"];
check[hbVisibility[{0,0},{2,2},{{{1,2},{2,2}},{{1,1},{0,2}}}]===False,
      "reversed gate times"];
check[hbVisibility[{0,0},{0,2},{{{0,0},{1,1}}}]===True,"collinear gate"];
check[hbVisibility[{0,0},{0,2},{{{1,1},{1,1}}}]===False,"parallel line misses"];
rect=HyperboxFreeExact[{1,2}];
check[rect["Diameter"]===3 && rect["StrictImprovement"]===False,"rectangle"];
cube=HyperboxFreeExact[{1,1,1,1}];
check[cube["DiameterSquared"]===6,"four-cube"];
rod=HyperboxFreeExact[{1,1,1,5}];
check[rod["VertexSquared"]===802/25 &&
      TrueQ[FullSimplify[rod["DiameterSquared"]==134-40 Sqrt[6]]],"long four-prism"];
plate=HyperboxFreeExact[{1,2,2,2}];
check[plate["DiameterSquared"]===17,"one short side"];
shortPrism=HyperboxFreeExact[{1,1,1,1,1,2}];
check[shortPrism["DiameterSquared"]===11 && shortPrism["StrictImprovement"]===False,
      "six-dimensional corner regime"];
(* Exercise optimization independently of the closed-form small cases. *)
rectchart=hbChartMax[{1,2},{1,0},{1,1}];
check[rectchart["Squared"]===9,"CAD rectangle chart"];
Print["Passed gate, rectangle, cube, and exact chart tests."];
