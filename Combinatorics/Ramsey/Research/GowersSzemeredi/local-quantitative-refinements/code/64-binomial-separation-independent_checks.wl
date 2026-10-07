(* Independent exact checks; Wolfram Language, no external packages. *)
d = {0, 1, 4, 13};
images = Mod[Tuples[d, 3].{1, 5, 10}, 80];
slice[weights_] := With[
  {ww = Join[weights, weights], h = Length[weights]},
  Total[Table[
    (-1)^Length[s] Max[Total[weights] - Total[s], 0]^(2 h - 1),
    {s, Subsets[Join[weights, weights]]}
  ]]/((2 h - 1)! Times @@ weights^2)
];
{Length[DeleteDuplicates[images]], slice[{1, 3}], slice[{1, 5, 10}],
 N[{Log[80]/Log[4], 5 + 9 Log[4]/Log[80]}, 35]}
