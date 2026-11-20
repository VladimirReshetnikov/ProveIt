(* Exact free-endpoint and fixed-vertex maxima on the boundary of a box.
   Load with Get["FreeExact.wl"], then evaluate HyperboxFreeExact[{1,1,2}].
   Uses only built-in Wolfram Language functions. All sides must be exact
   positive real algebraic numbers. CAD size increases rapidly with dimension.
*)

ClearAll[hbFaceBox, hbVisibility, hbWordRecords, hbChartMax, hbBest, hbFamilyAnswers,
  HyperboxFreeExact];

(* Each row {a,b} denotes a t+b >= 0. A gate has its own time.
   Feasible nondecreasing gate times exist iff zero rows are consistent
   and every lower bound is <= every later (or same gate) upper bound. *)
hbVisibility[z_, site_, gates_] := Module[
  {direction = site-z, rows, tests, oldRows = {}, current},
  rows = Table[
    Join[{{1,0},{-1,1}},
      Flatten[Table[
        {{direction[[j]], z[[j]]-gate[[j,1]]},
         {-direction[[j]], gate[[j,2]]-z[[j]]}},
        {j, Length[z]}], 1]],
    {gate, gates}];
  tests = Reap[
    Do[
      current = DeleteDuplicates[rr];
      Do[Sow[Or[row[[1]] != 0, row[[2]] >= 0]], {row, current}];
      oldRows = Union[oldRows, current];
      Do[
        Sow[Or[low[[1]] <= 0, high[[1]] >= 0,
          Expand[low[[1]] high[[2]]-low[[2]] high[[1]]] >= 0]],
        {low, oldRows}, {high, current}],
      {rr, rows}]
  ][[2]];
  If[tests === {}, True, And @@ DeleteDuplicates[First[tests]]]
];

(* A frame slot {j,sign,offset} has unfolded coordinate offset+sign*x_j. *)
hbFaceBox[a_, frame_] := Map[
  Function[slot, With[{l=slot[[3]], r=slot[[3]] + slot[[2]] a[[slot[[1]]]]},
    {Min[l,r],Max[l,r]}]],
  frame];

hbWordRecords[a_, p_, q_, start_, sourceFaces_] := Module[
  {m=Length[a]-1, z, startFrame, walk, records},
  z = Delete[q, start[[1]]];
  startFrame = ({#,1,0}&) /@ Delete[Range[Length[a]], start[[1]]];
  walk[face_, frame_, used_, gates_] := Module[
    {site, axis, sign, offset, nxt, bound, gate, orient, newFrame},
    If[MemberQ[sourceFaces, face],
      site = (#[[3]] + #[[2]] p[[#[[1]]]]&) /@ frame;
      Sow[{Expand[Total[(z-site)^2]], hbVisibility[z,site,gates]}];
      Return[Null]
    ];
    Do[
      {axis,sign,offset}=frame[[k]];
      nxt={axis,side};
      If[!MemberQ[used,nxt],
        bound = offset+sign side a[[axis]];
        gate = ReplacePart[hbFaceBox[a,frame], k->{bound,bound}];
        orient = sign (2 side-1) (1-2 face[[2]]);
        newFrame = ReplacePart[frame,
          k->{face[[1]],orient,bound-orient face[[2]] a[[face[[1]]]]}];
        walk[nxt,newFrame,Append[used,nxt],Append[gates,gate]]
      ], {k,m},{side,0,1}]
  ];
  records=Reap[walk[start,startFrame,{start},{}]][[2]];
  If[records === {}, {}, DeleteDuplicates[First[records]]]
];

(* With f=None the source is the origin. Otherwise f and g specify an
   endpoint chart, including its full boundary. *)
hbChartMax[a_, f_, g_] := Module[
  {n=Length[a], p, q, ux, uy, s=Unique["sq"], sourceFaces, vars,
   ranges, records, distanceConstraints, conclusion, witness},
  uy=Table[Unique["y"], {n-1}];
  q=Insert[uy,g[[2]] a[[g[[1]]]],g[[1]]];
  If[f === None,
    ux={}; p=ConstantArray[0,n];
    sourceFaces=({#,0}&) /@ Range[n],
    ux=Table[Unique["x"],{n-1}];
    p=Insert[ux,f[[2]] a[[f[[1]]]],f[[1]]];
    sourceFaces={f}
  ];
  vars=Join[{s},ux,uy];
  ranges=And @@ Join[MapThread[0<=#1<=#2&, {p,a}],
                     MapThread[0<=#1<=#2&, {q,a}]];
  records=hbWordRecords[a,p,q,g,sourceFaces];
  If[records === {}, Return[$Failed]];
  distanceConstraints=And @@ Map[
    Function[group,
      Or[s<=group[[1,1]], Not[Or @@ group[[All,2]]]]],
    GatherBy[records,First]];
  conclusion=Maximize[{s, s>=0 && ranges && distanceConstraints},vars,Reals];
  If[!MatchQ[conclusion,{_,{___Rule}}], Return[$Failed]];
  witness=Last[conclusion];
  If[!FreeQ[Join[p,q]/.witness, Alternatives @@ vars], Return[$Failed]];
  <|"Squared"->First[conclusion],"P"->(p/.witness),"Q"->(q/.witness)|>
];

hbBest[records_] := Fold[Function[{best,r},
  If[TrueQ[FullSimplify[r["Squared"]>best["Squared"]]],r,best]],
  First[records],Rest[records]];

(* Closed forms proved in the article. A two-element result contains
   the fixed and free records; an empty list requests the CAD fallback. *)
hbFamilyAnswers[a_] := Module[
  {n=Length[a], d=Length[a]-1, lo=Min[a], hi=Max[a],
   lowAxes, highAxes, corner, t, delta, tRatio, longAxis,
   fixed, free, pair, ov},
  ov=Total[a^2]+2 Min[Times @@@ Subsets[a,{2}]];
  corner=<|"Squared"->ov,"P"->ConstantArray[0,n],"Q"->a|>;
  lowAxes=Select[Range[n],Function[i,TrueQ[FullSimplify[a[[i]]==lo]]]];
  highAxes=Select[Range[n],Function[i,TrueQ[FullSimplify[a[[i]]==hi]]]];
  If[n==2 || Length[highAxes]>=n-1, Return[{corner,corner}]];
  If[Length[lowAxes]!=d, Return[{}]];
  longAxis=First[highAxes]; tRatio=hi/lo;
  If[d<5 && !TrueQ[FullSimplify[tRatio>=d]],Return[{}]];
  t=(tRatio+1)/(2 tRatio);
  delta=1/(2 (tRatio+Sqrt[tRatio^2-1]));
  fixed=<|"Squared"->FullSimplify[lo^2 (tRatio^2+2 tRatio t+d t^2)],
    "P"->ConstantArray[0,n],"Q"->ReplacePart[ConstantArray[lo t,n],longAxis->hi]|>;
  pair=ReplacePart[ConstantArray[lo (1/2-# delta),n],
                   longAxis->If[#==1,0,hi]]& /@ {1,-1};
  free=<|"Squared"->FullSimplify[lo^2 ((tRatio+1)^2+4(d-1)delta^2)],
    "P"->First[pair],"Q"->Last[pair]|>;
  {hbBest[{corner,fixed}],hbBest[{corner,free}]}
];

HyperboxFreeExact[a_List] := Module[
  {n=Length[a], known, fixed, free, pairs, fixedAxes, freeAnswers,
   fixedAnswers, pairKey, sideCompare},
  If[n<2 || !(And @@ (TrueQ[FullSimplify[Element[#,Algebraics] && #>0]]& /@ a))
      || !FreeQ[a,_Real], Return[$Failed]];
  known=hbFamilyAnswers[a];
  If[known =!= {},
    {fixed,free}=known,
    fixedAxes=DeleteDuplicatesBy[Range[n], Function[i,a[[i]]]];
    fixedAnswers=Table[hbChartMax[a,None,{i,1}],{i,fixedAxes}];
    (* Each pair of distinct axes can be oriented to two lower facets.
       Opposite parallel facets can be oriented lower-to-upper. *)
    pairs=Join[Table[{{i,0},{i,1}},{i,n}],
      Flatten[Table[{{i,0},{j,0}},{i,n},{j,i+1,n}],1]];
    pairKey[pair_] := {pair[[1,1]]===pair[[2,1]],
       Sort[{a[[pair[[1,1]]]],a[[pair[[2,1]]]]}]};
    pairs=DeleteDuplicatesBy[pairs,pairKey];
    freeAnswers=(hbChartMax[a,#[[1]],#[[2]]]&)/@pairs;
    If[MemberQ[Join[fixedAnswers,freeAnswers],$Failed],Return[$Failed]];
    fixed=hbBest[fixedAnswers]; free=hbBest[freeAnswers]
  ];
  sideCompare=FullSimplify[free["Squared"]>fixed["Squared"]];
  <|"VertexSquared"->fixed["Squared"],"VertexDistance"->Sqrt[fixed["Squared"]],
    "FarthestFromOrigin"->fixed["Q"],"DiameterSquared"->free["Squared"],
    "Diameter"->Sqrt[free["Squared"]],"P"->free["P"],"Q"->free["Q"],
    "StrictImprovement"->sideCompare|>
];
