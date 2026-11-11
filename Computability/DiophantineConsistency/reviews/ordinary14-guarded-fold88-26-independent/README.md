# Independent review: quotient-guarded 88/26 equivalence

**PASS, external mathematics and finite graph review.** With integer fixed
ports `beta>0` and `0<=K0<(beta+1)²`, the 14-positive-input quotient-guarded
88-gate graph has a positive zero iff the 13-positive 88/30 parent has one.
All 88 gates and 14 inputs are live; its actual compact44 polynomial has exact
degree 26. This is not a new Lean/iPRA theorem, PDF/file-semantics binding,
paired endpoint replay or global-minimality claim.

For a parent zero, the independently reviewed 89/26 guarded construction
provides a signed-fold zero with positive sigma and positive Bt. Its first
norm gives b|Bt; taking t=Bt/b>0 and sigma'=sigma+t makes the new first
expression equal to the old one, and makes the quotient guard zero. Other
residuals are unchanged. Thus a positive parent zero supplies a positive
quotient-guarded zero.

Conversely, every positive quotient-guarded zero makes each of the five
squares zero, so `Bt=b*t>0`. Its first norm implies `M|Z` and `q³|Y`;
write `Y=q³s`, `M=q³b`, `m=XY²`, `ell=mk` and `tau=|Z|/M`. Its first and
main norm equations give `k>2` and then `k>=8m+4` by the separately reviewed
consecutive-square and first-Pell descent argument. Since

```
(ell+k/2)²−tau² = k²/4−1 > 0,
```

`tau<ell+k/2`. With C=q−F−alpha<=b−1, K0<q² and Y>=q³,

```
0<t<=Bt < b*(X+K0*q) < q*X+q^4 < 2*X*q^6 < k/4.
```

The first expression is now `Z=M*(ell+k−sigma')+Yb`, so its two root
branches give `sigma'=ell+k+s±tau>k/2+s>t`. Thus
`sigma=sigma'−t>0`; it produces the same Z in the signed-fold graph, whose
other residuals remain zero and whose Bt is positive. The independently
reviewed positive-Bt repair then produces a positive parent root. No claim is
made that the candidate's first-root branch directly gives a positive parent
coordinate.

The checker matches all source rows to the signed graph minus two rows plus
four guard rows, checks all-gate reachability, independently authenticates
the P72/P115 port bytes and hypotheses, reruns the author's finite receipt,
and evaluates a nonuniform whole-graph modular ray. With the reviewed degree
upper bound of 26 and a guard square of degree at most four, its nonzero
coefficient **6848080 modulo 1000000007** at degree 26 proves exact
specialized integer degree 26. The checker also exercises finite sign and
norm-bound controls; they supplement the unbounded proof above.
