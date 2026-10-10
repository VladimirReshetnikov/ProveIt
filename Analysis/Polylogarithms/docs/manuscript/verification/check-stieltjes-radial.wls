ClearAll[xx, yy, cc, hh, uu, vv, rr, pp, dd, dec];
dd[t_] := 1 - 2 cc t + t^2;
pp = Expand[(xx dd[yy]^2 + yy dd[xx]^2 - (xx - yy)^2 (xx dd[yy] + yy dd[xx]))/2];
dec = (1 - xx) (1 - yy) ((xx - yy)^2 + xx (1 - yy)^2 + yy (1 - xx)^2)/2 + 4 xx yy (1 - xx) (1 - yy) (1 - cc) + 2 xx yy (xx + yy) (1 - cc)^2;
nom = ComplexExpand[Im[(cc + I hh) uu (1 - rr uu (cc - I hh))^2 (1 - rr vv (cc + I hh)) (1 - 2 rr cc vv + rr^2 vv^2)]];
reduced = PolynomialRemainder[Expand[nom], hh^2 + cc^2 - 1, hh];
symmetric = (reduced + (reduced /. {uu -> vv, vv -> uu}))/2;
checks = <|
 "positiveDecomposition" -> TrueQ[Expand[pp - dec] === 0],
 "symmetrizedDerivative" -> TrueQ[Expand[symmetric - hh/rr (pp /. {xx -> rr uu, yy -> rr vv})] === 0],
 "singleAtomNormalization" -> TrueQ[Expand[(pp /. yy -> xx) - xx dd[xx]^2] === 0],
 "corruptedPolynomialRejected" -> Not[TrueQ[Expand[pp - dec + 1/100] === 0]]
|>;
record = <|"all_pass" -> And @@ Values[checks], "engine" -> $Version, "checks" -> checks, "scope" -> "Native exact polynomial identities and a corruption control; measure positivity and continuum quantifiers are proved in the manuscript."|>;
Export[FileNameJoin[{DirectoryName[$InputFileName], "stieltjes-radial-native.json"}], record, "RawJSON"];
Print[ExportString[record,"RawJSON"]];
Exit[If[TrueQ[record["all_pass"]],0,1]];
