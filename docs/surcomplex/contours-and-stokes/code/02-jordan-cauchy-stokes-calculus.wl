(* Independent exact cross-check for the radius-free contour example.
   Evaluate in a Wolfram Language kernel. No external packages are needed.
   The displayed evaluation was run through the Wolfram connector. *)

coefficients = With[{nmax = 8},
  Table[{m, Sum[n^(2 (m - n) + 1), {n, 1, m}]}, {m, 1, nmax}]
];
expected = {{1, 1}, {2, 3}, {3, 12}, {4, 64}, {5, 441},
  {6, 3855}, {7, 41464}, {8, 533736}};
Print[coefficients];
If[coefficients =!= expected,
  Print["FAILED: radius-free coefficient mismatch"]; Abort[]];
Print["PASS: all eight radius-free contour coefficients."];

(* Recorded connector output for the With expression:
   {{1, 1}, {2, 3}, {3, 12}, {4, 64}, {5, 441},
    {6, 3855}, {7, 41464}, {8, 533736}}
   These are coefficients of t^m, not numerical approximations to t.
*)
