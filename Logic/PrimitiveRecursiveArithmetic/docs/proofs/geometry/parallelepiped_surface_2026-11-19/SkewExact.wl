(* Exact real-algebraic geometry for a parallelepiped, in unit coefficient
   coordinates. Public entry points: SkewExact`SurfaceDistance,
   SkewExact`VertexMaximum, SkewExact`SurfaceDiameter. *)
BeginPackage["SkewExact`"];
SurfaceDistance::usage = "SurfaceDistance[g,p,q] gives the shortest surface distance for an exact positive-definite 3 by 3 real algebraic Gram matrix g and boundary points p,q expressed in edge coordinates in [0,1]^3.";
VertexMaximum::usage = "VertexMaximum[g,v] gives the eccentricity of the specified vertex v (default {0,0,0}), with exact coordinates of a farthest point.";
SurfaceDiameter::usage = "SurfaceDiameter[g] gives the intrinsic diameter and the exact edge coordinates of a centrally opposite pair attaining it.";
Begin["`Private`"];

cross[p_, q_] := p[[1]] q[[2]] - p[[2]] q[[1]];
algebraicQ[x_] := Precision[x] === Infinity &&
  TrueQ[Element[x, Algebraics] && Element[x, Reals]];
gramQ[g_] := MatrixQ[g, algebraicQ] && Dimensions[g] === {3, 3} &&
  TrueQ[g == Transpose[g]] &&
  And @@ Table[TrueQ[Det[g[[1 ;; k, 1 ;; k]]] > 0], {k, 3}];
unitQ[x_] := TrueQ[0 <= x <= 1];
boundaryQ[p_] := ListQ[p] && Length[p] === 3 && AllTrue[p, algebraicQ] &&
  AllTrue[p, unitQ] && AnyTrue[p, TrueQ[# == 0 || # == 1] &];
vertexQ[p_] := boundaryQ[p] && AllTrue[p, TrueQ[# == 0 || # == 1] &];

axis[i_] := Ceiling[i/2];
side[i_] := Mod[i - 1, 2];
free[i_] := DeleteCases[Range[3], axis[i]];
chart[i_, vars_] := Insert[vars, side[i], axis[i]];
incident[p_] := Select[Range[6], TrueQ[p[[axis[#]]] == side[#]] &];
opposite[i_] := If[OddQ[i], i + 1, i - 1];

paths[i_, j_] := grow[{i}, j];
grow[path_, j_] := If[Last[path] === j, {path},
  Join @@ (grow[Append[path, #], j] & /@
    Select[Complement[Range[6], path], axis[#] =!= axis[Last[path]] &])];

(* After the last face incident with v, a shortest word visits only faces
   opposite v. Its prefix in that last incident face is a straight chord. *)
vertexWords[v_, face_] := Module[{neg, pos, i, j, suffixes},
  neg = incident[v];
  If[MemberQ[neg, face], Return[{{face}}]];
  pos = Complement[Range[6], neg, {face}]; {i, j} = pos;
  suffixes = {{face}, {i, face}, {j, face}, {i, j, face}, {j, i, face}};
  Flatten[Table[Prepend[suffix, n], {suffix, suffixes},
    {n, Select[neg, axis[#] =!= axis[First[suffix]] &]}], 1]
];

(* A face layout is {origin, three planar axis vectors}; the vector of
   its fixed coordinate is zero. Each hinge is a closed segment. *)
initial[g_, i_] := Module[{m, n, dirs = ConstantArray[0, {3, 2}]},
  {m, n} = free[i];
  dirs[[m]] = {Sqrt[g[[m, m]]], 0};
  dirs[[n]] = {g[[m, n]]/Sqrt[g[[m, m]]],
    Sqrt[g[[m, m]] g[[n, n]] - g[[m, n]]^2]/Sqrt[g[[m, m]]]};
  {{0, 0}, Map[RootReduce, dirs, {2}]}
];
advance[g_, i_, j_, frame_] := Module[
  {a = axis[i], b = axis[j], k, e, normal, incoming, outSign, relative,
   newDir, dirs = ConstantArray[0, {3, 2}], hinge},
  k = First[Complement[Range[3], {a, b}]];
  e = frame[[2, k]]; normal = {-e[[2]], e[[1]]};
  incoming = (1 - 2 side[j]) frame[[2, b]];
  outSign = -(1 - 2 side[i]) Sign[RootReduce[cross[e, incoming]]];
  relative = Sqrt[g[[k, k]] g[[a, a]] - g[[k, a]]^2];
  newDir = RootReduce /@ ((g[[k, a]] e + outSign relative normal)/g[[k, k]]);
  dirs[[k]] = e; dirs[[a]] = newDir;
  hinge = RootReduce /@ (frame[[1]] + side[j] frame[[2, b]]);
  {{RootReduce /@ (hinge - side[i] newDir), dirs}, {hinge, hinge + e}}
];
position[frame_, p_] := frame[[1]] + p.frame[[2]];
route[g_, path_, p_, q_, vars_] := Module[
  {frame, start, offset, gates = {}, step, raw, cost},
  frame = initial[g, First[path]]; start = position[frame, p];
  Do[step = advance[g, path[[m]], path[[m + 1]], frame];
    frame = First[step]; AppendTo[gates, Last[step]], {m, Length[path] - 1}];
  offset = Expand /@ (position[frame, q] - start);
  raw = Expand[offset.offset];
  cost = If[vars === {}, RootReduce[raw], Collect[raw, vars, RootReduce]];
  {cost, start, offset, gates}
];
routes[g_, fs_, gs_, p_, q_, vars_] :=
  Flatten[Table[route[g, chain, p, q, vars],
    {i, fs}, {j, gs}, {chain, paths[i, j]}], 2];

(* Greedy interval selection gives a monotone sequence of gate times if
   one exists. Handles collinear overlap, endpoint contact and zero length. *)
admissible[r_, rules_] := Module[
  {p, d, dd, last = 0, a, b, e, det, t, s, t0, t1, lo, hi},
  p = RootReduce /@ (r[[2]] /. rules);
  d = RootReduce /@ (r[[3]] /. rules); dd = RootReduce[d.d];
  Do[{a, b} = gate; e = b - a;
    det = RootReduce[cross[d, e]];
    If[det != 0,
      t = RootReduce[cross[a - p, e]/det];
      s = RootReduce[cross[a - p, d]/det];
      If[!TrueQ[0 <= s <= 1 && last <= t <= 1], Return[False, Module]];
      last = t,
      If[RootReduce[cross[e, p - a]] != 0, Return[False, Module]];
      If[dd == 0,
        If[!TrueQ[0 <= (p - a).e <= e.e], Return[False, Module]],
        t0 = RootReduce[(a - p).d/dd]; t1 = RootReduce[(b - p).d/dd];
        lo = Max[0, Min[t0, t1]]; hi = Min[1, Max[t0, t1]];
        last = Max[last, lo]; If[!TrueQ[last <= hi], Return[False, Module]]
      ]
    ], {gate, r[[4]]}];
  True
];
shortest[rs_, rules_] := Module[{ranked, item},
  ranked = Sort[Table[{RootReduce[rs[[i, 1]] /. rules], i},
    {i, Length[rs]}], TrueQ[First[#1] < First[#2]] &];
  item = SelectFirst[ranked, admissible[rs[[Last[#]]], rules] &, $Failed];
  If[item === $Failed, $Failed, First[item]]
];
result[z_, p_, q_] := <|"Point" -> p, "OtherPoint" -> q,
  "SquaredDistance" -> z, "Distance" -> RootReduce[Sqrt[z]]|>;

SurfaceDistance[g_, p_, q_] := Module[{rs, z, fs, gs, chains},
  If[!gramQ[g] || !boundaryQ[p] || !boundaryQ[q], Return[$Failed]];
  fs = incident[p]; gs = incident[q];
  If[Intersection[fs, gs] =!= {},
    z = RootReduce[(q - p).g.(q - p)]; Return[result[z, p, q]]];
  Which[vertexQ[p],
      chains = Join @@ (vertexWords[p, #] & /@ gs);
      rs = route[g, #, p, q, {}] & /@ chains,
    vertexQ[q],
      chains = Join @@ (vertexWords[q, #] & /@ fs);
      rs = route[g, #, q, p, {}] & /@ chains,
    True, rs = routes[g, fs, gs, p, q, {}]];
  z = shortest[rs, {}]; If[z === $Failed, $Failed, result[z, p, q]]
];

(* Candidate generation. For fixed v, pair differences are bisector
   lines; the triple systems give circumcenters. For opposite pairs the
   differences are quadratic. Drop duplicate polynomials for generating
   points only. Every original route stays in the distance/visibility test. *)
zeroQ[f_] := Module[{vars = Cases[Variables[f], _Symbol]},
  If[vars === {}, Return[TrueQ[RootReduce[f] == 0]]];
  AllTrue[Last /@ CoefficientRules[Expand[f], vars], TrueQ[RootReduce[#] == 0] &]
];
rootsInSquare[eqs_, vars_] := Module[{sol, points},
  If[AnyTrue[eqs, zeroQ], Return[{}]];
  sol = Quiet[Solve[And @@ (# == 0 & /@ eqs), vars, Reals]];
  If[!ListQ[sol], Throw[$Failed, candidateFailure]];
  points = (vars /. #) & /@ sol;
  If[!AllTrue[points, AllTrue[#, algebraicQ] &], Throw[$Failed, candidateFailure]];
  Select[points, AllTrue[#, unitQ] &]
];
candidatePoints[rs_, vars_] := Module[
  {ps, u, v, pair, triple, poly, at, sub, eq1, eq2, jac, harvested},
  {u, v} = vars;
  ps = DeleteDuplicates[rs[[All, 1]], zeroQ[#1 - #2] &];
  harvested = Reap[
    Scan[Sow, Tuples[{0, 1}, 2]];
    Do[poly = Expand[pair[[1]] - pair[[2]]];
      Do[at = vars[[i]] -> s; sub = {vars[[3 - i]]};
        Scan[(Sow[vars /. at /. Thread[sub -> #]]) &,
          rootsInSquare[{poly /. at}, sub]],
        {i, 2}, {s, 0, 1}], {pair, Subsets[ps, {2}]}];
    Do[eq1 = Expand[triple[[1]] - triple[[2]]];
      eq2 = Expand[triple[[1]] - triple[[3]]];
      jac = Expand[D[eq1, u] D[eq2, v] - D[eq1, v] D[eq2, u]];
      If[!zeroQ[jac], Scan[Sow, rootsInSquare[{eq1, eq2}, vars]]],
      {triple, Subsets[ps, {3}]}]
  ][[2, 1]];
  DeleteDuplicates[harvested, TrueQ[#1 == #2] &]
];

(* A separate exact global check also handles exceptional algebraic inputs
   where a candidate intersection has positive dimension. The optional cross-check keeps
   all gates and the order of intersections, without genericity assumptions. *)
gateBounds[p_, d_, gate_] := Module[{e, w, n0, n1, l0, l1},
  e = gate[[2]] - gate[[1]]; w = p - gate[[1]];
  n0 = Expand[cross[e, w]]; n1 = Expand[cross[e, d]];
  l0 = Expand[w.e]; l1 = Expand[d.e];
  (* Each pair {A,B} encodes A+B t >= 0. *)
  {{n0, n1}, {-n0, -n1}, {l0, l1}, {Expand[e.e - l0], -l1}}
];
visibility[r_] := Module[{gates = r[[4]], blocks, flat, constantTests, bounds},
  If[gates === {}, Return[True]];
  blocks = gateBounds[r[[2]], r[[3]], #] & /@ gates;
  blocks[[1]] = Append[blocks[[1]], {0, 1}];
  blocks[[-1]] = Append[blocks[[-1]], {1, -1}];
  flat = Flatten[blocks, 1];
  constantTests = ((#[[2]] != 0 || #[[1]] >= 0) & /@ flat);
  (* A lower bound at gate i must not exceed an upper bound at j >= i.
     Clearing denominators under the indicated signs avoids division,
     including on coincident seams and when p and q develop to one point. *)
  bounds = Flatten[Table[
    Implies[low[[2]] > 0 && high[[2]] < 0,
      Expand[high[[1]] low[[2]] - low[[1]] high[[2]]] >= 0],
    {i, Length[blocks]}, {j, i, Length[blocks]},
    {low, blocks[[i]]}, {high, blocks[[j]]}]];
  And @@ Join[constantTests, bounds]
];
bestFace[g_, face_, vertex_, mode_, vars_, checkGlobal_] := Module[
  {p, q, rs, candidates, scores, winner, z, domain, vis, bigger,
   test, hyp, opt, pair, actual, pars, verify = checkGlobal, zv = Unique["sq"]},
  pars = vars;
  If[mode === "vertex",
    p = vertex; q = chart[face, vars];
    rs = route[g, #, p, q, vars] & /@ vertexWords[vertex, face],
    p = chart[face, vars]; q = 1 - p;
    rs = routes[g, {face}, {opposite[face]}, p, q, vars]];
  candidates = If[Length[rs] == 1, Tuples[{0, 1}, 2],
    Catch[candidatePoints[rs, vars], candidateFailure]];
  If[candidates === $Failed, candidates = Tuples[{0, 1}, 2]; verify = True];
  scores = Table[shortest[rs, Thread[vars -> xy]], {xy, candidates}];
  If[MemberQ[scores, $Failed], Return[$Failed]];
  winner = Fold[If[TrueQ[scores[[#2]] > scores[[#1]]], #2, #1] &,
    1, Range[2, Length[scores]]];
  z = scores[[winner]]; pair = candidates[[winner]];
  If[!TrueQ[verify] || Length[rs] == 1,
    Return[result[z, p /. Thread[vars -> pair], q /. Thread[vars -> pair]]]];
  domain = And @@ (0 <= # <= 1 & /@ vars);
  vis = visibility /@ rs;
  bigger = domain && And @@ MapThread[(!#1 || #2 > z) &, {vis, rs[[All, 1]]}];
  test = With[{xx = pars, cond = bigger}, Resolve[Exists[xx, cond], Reals]];
  If[!TrueQ[test === False],
    hyp = domain && zv >= 0 &&
      And @@ MapThread[(!#1 || zv <= #2) &, {vis, rs[[All, 1]]}];
    opt = Maximize[{zv, hyp}, Join[{zv}, vars], Reals];
    If[!MatchQ[opt, {_, {___Rule}}], Return[$Failed]];
    z = First[opt]; pair = vars /. Last[opt];
    If[!algebraicQ[z] || !AllTrue[pair, algebraicQ], Return[$Failed]];
    actual = shortest[rs, Thread[vars -> pair]];
    If[!TrueQ[actual == z], Return[$Failed]]
  ];
  result[z, p /. Thread[vars -> pair], q /. Thread[vars -> pair]]
];
global[g_, v_, mode_, verify_] := Module[{faces, answers, pars = {Unique["u"], Unique["v"]}},
  faces = If[mode === "vertex", Range[6], {1, 3, 5}];
  answers = bestFace[g, #, v, mode, pars, verify] & /@ faces;
  If[MemberQ[answers, $Failed], $Failed,
    Fold[If[TrueQ[#2["SquaredDistance"] > #1["SquaredDistance"]], #2, #1] &,
      First[answers], Rest[answers]]]
];
VertexMaximum[g_, v_ : {0, 0, 0}, verify_ : False] :=
  If[gramQ[g] && vertexQ[v] && MemberQ[{True, False}, verify],
    global[g, v, "vertex", verify], $Failed];
SurfaceDiameter[g_, verify_ : False] :=
  If[gramQ[g] && MemberQ[{True, False}, verify],
    global[g, {}, "diameter", verify], $Failed];

End[];
EndPackage[];
