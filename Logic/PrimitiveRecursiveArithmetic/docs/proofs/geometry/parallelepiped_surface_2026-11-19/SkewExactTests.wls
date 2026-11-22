Get[FileNameJoin[{DirectoryName[$InputFileName], "SkewExact.wl"}]];
failures = 0;
check[label_, pred_] := If[TrueQ[pred], Print["PASS ", label],
  failures++; Print["FAIL ", label, "   ", InputForm[pred]]];
checkValue[label_, answer_, expected_] :=
  check[label, AssociationQ[answer] && RootReduce[answer["SquaredDistance"] - expected] === 0];
g = IdentityMatrix[3];
a = {0, 0, 0}; b = {1, 1, 1};
rh = (IdentityMatrix[3] + 31 ConstantArray[1, {3, 3}])/32;
checkValue["unit cube opposite vertices", SurfaceDistance[g, a, b], 5];
checkValue["skew rhombohedron opposite vertices", SurfaceDistance[rh, a, b], 71/8];
checkValue["distance on a shared face", SurfaceDistance[rh, a, {1/2, 1/2, 0}], 63/64];
checkValue["zero length on an edge", SurfaceDistance[rh, {1/2, 0, 0}, {1/2, 0, 0}], 0];
check["non-SPD input", SurfaceDistance[ConstantArray[1, {3, 3}], a, b] === $Failed];
Do[check["ten words on each opposite face, one on each incident face",
  Length[SkewExact`Private`vertexWords[vert, face]] ==
    If[MemberQ[SkewExact`Private`incident[vert], face], 1, 10]],
  {vert, {{0, 0, 0}, {1, 0, 1}}}, {face, 6}];
testGates[label_, r_, truth_] := (
  check[label <> " (interval)", SkewExact`Private`admissible[r, {}] === truth];
  check[label <> " (polynomial)", SkewExact`Private`visibility[r] === truth]);
testGates["collinear overlap", {1, {0, 0}, {1, 0},
  {{{3/4, 0}, {1/4, 0}}, {{1/2, -1}, {1/2, 1}}}}, True];
testGates["reversed timing", {1, {0, 0}, {1, 0},
  {{{3/4, -1}, {3/4, 1}}, {{1/4, 0}, {1/2, 0}}}}, False];
testGates["point on two consecutive seams", {0, {0, 0}, {0, 0},
  {{{0, 0}, {0, 1}}, {{-1, 0}, {1, 0}}}}, True];
If[MemberQ[$ScriptCommandLine, "--extrema"],
  checkValue["exact fixed-vertex optimum", VertexMaximum[rh], 71/8];
  checkValue["exact free optimum", SurfaceDiameter[rh], 71/8];
  box = DiagonalMatrix[{1, 1, 4}];
  checkValue["interior farthest point of box", VertexMaximum[box], 65/8];
  checkValue["free box diameter", SurfaceDiameter[box], 16 - 4 Sqrt[3]]];
Exit[Boole[failures > 0]];
