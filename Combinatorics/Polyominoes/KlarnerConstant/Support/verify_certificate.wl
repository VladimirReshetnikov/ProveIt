(* Exact Wolfram Language audit of the Klarner-constant certificate. *)

zeta = 2000/9047;
names = {"c", "d", "e", "f", "g", "h", "p", "q", "r", "s", "t",
   "u", "v", "w", "x", "y", "z"};
values = {
   3482045, 4310668, 5751028, 16014774, 9499305, 7394875,
   6515468, 3748277, 2390936, 3084206, 2902315, 5050537,
   1238300, 1015088, 1664015, 1375847, 1132149
   }/10000000;

{c, d, e, f, g, h, p, q, r, s, t, u, v, w, x, y, z} = values;
phi = {
   zeta + zeta e,
   zeta + zeta g,
   zeta + zeta f,
   g + p,
   e + q,
   d + s,
   e h + q d + x r + v y + u y z,
   zeta g + zeta g e + zeta^2 (u + t g + r u),
   y + w,
   zeta g + zeta e^2 + zeta^2 t + zeta^2 x g + zeta^2 y u,
   x + v,
   d h + s d + y r + w y + u z^2,
   zeta s + zeta^2 (g^2 + t e + r t),
   zeta s + zeta^2 (e g + x e + y t),
   zeta d + zeta^2 (g + u),
   zeta c + zeta^2 (g + t),
   zeta c + zeta^2 (e + x)
   };
residuals = Together[values - phi];

If[! And @@ Thread[values >= 0], Print["negative coordinate"]; Exit[1]];
If[! And @@ Thread[residuals >= 0], Print["failed inequality"]; Exit[1]];
If[! TrueQ[g < 1], Print["g is not below one"]; Exit[1]];
If[! TrueQ[1/zeta == 9047/2000], Print["wrong reciprocal"]; Exit[1]];

Print["zeta = ", zeta, "; reciprocal = ", 1/zeta];
Print["g = ", g, " < 1"];
Print[Column[MapThread[Row[{#1, ": ", #2}] &, {names, residuals}]]];
