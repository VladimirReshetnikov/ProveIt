# Verifying the weight-5 depth-2 multiple polylogarithms with Wolfram 15

- Status: Report (machine verification of previously PSLQ-only results)
- Created (UTC): 2026-06-18T01:16:41Z
- Repository HEAD: aecae7c8aa0553f6cd64921d14e592e81d83138a
- Requested by Vladimir: *"there were some cases where multiple zeta values
  appeared in our computations, but we were not able to verify them with
  Mathematica. Now it's time to do that."*

## Summary

The one place in this repository where genuine **depth-two** multiple
polylogarithm values appeared — the weight-5 single direction of the
Hypergeometric "Catalan ladder", stored in
[`identities/discovered-level4-weight5-eulersum.wl`](../../identities/discovered-level4-weight5-eulersum.wl)
and presented as the depth-two theorem of
[`src/Hypergeometric/docs/article/pfq-derivative-ladders.tex`](../../../Hypergeometric/docs/article/pfq-derivative-ladders.tex) —
was originally pinned **only** by PSLQ at 700 digits plus accelerated `NSum`,
because the Mathematica version available at the time had no
multiple-polylogarithm primitive. Wolfram **15.0** adds `MultiplePolyLog`,
`MultipleZeta`, `GeneralizedPolyLog`, `HarmonicPolyLog` and
`MultipleHarmonicNumber`, so every one of these values now goes through the
genuine special function — numerically **and** symbolically.

All of the following was run on the local paid Wolfram 15.0 kernel
(`$Version` → `15.0.0`). Reproducible scripts:
[`tools/scratch/mzv-v15/`](../../tools/scratch/mzv-v15/) (`convention.wl`,
`verify.wl`, `nielsen.wl`).

## 1. Pinning the `MultiplePolyLog` convention

With the store's definition `Li_{a,b}(z₁,z₂) = Σ_{m>n≥1} z₁ᵐ z₂ⁿ / (mᵃ nᵇ)`,
the four weight-5 generators are `gₐᵦ = Im Li_{a,b}(i,1)`, `a+b=5`. The V15
reference docs are ambiguous about which argument of `MultiplePolyLog` holds
the exponents, so the convention was fixed empirically against the known value
`g41 = −0.01592246492806263367…`. Of the six plausible argument arrangements,
exactly one matched (the rest returned `ComplexInfinity`):

```
Im MultiplePolyLog[{4,1}, {I,1}] = g41   (residual ~10⁻⁴¹)
```

So **the first list is the exponents, the second the z-values**:
`Im Li_{a,b}(i,1) = Im MultiplePolyLog[{a,b}, {I,1}]`. This matches the
documentation's `MultipleZeta[{6,4,2,8}] == MultiplePolyLog[{6,4,2,8},{1,1,1,1}]`.

## 2. The four generators verify, and reduce to standard functions

Each generator evaluated through `MultiplePolyLog` matches the store's
accelerated-`NSum` value to the precision floor (40–50 digits), and
`FullSimplify` reduces it to a standard harmonic/Nielsen polylogarithm — the
imaginary parts checked **exactly** equal:

| generator | `= Im Li_{a,b}(i,1)` | V15 `FullSimplify` reduction |
|---|---|---|
| `g41` | `Im MultiplePolyLog[{4,1},{I,1}]` | `Im PolyLog[3,2,I]`  (Nielsen `S₃,₂(i)`) |
| `g32` | `Im MultiplePolyLog[{3,2},{I,1}]` | `Im HarmonicPolyLog[{3,2},I]` |
| `g23` | `Im MultiplePolyLog[{2,3},{I,1}]` | `Im HarmonicPolyLog[{2,3},I]` |
| `g14` | `Im MultiplePolyLog[{1,4},{I,1}]` | `Im HarmonicPolyLog[{1,4},I]` |

The `b=1` generator collapses to a **Nielsen polylogarithm** `PolyLog[3,2,I]`
(`PolyLog[n,p,z]` is Wolfram's `Sₙ,ₚ(z)`); the others land in the
Remiddi–Vermaseren harmonic-polylog basis (condensed-index notation, where a
positive integer `m` denotes `m−1` leading zeros). This is exactly the
"multiple-zeta / multiple-polylogarithm structure of the cyclotomic field" the
article anticipated — now made concrete by the CAS.

## 3. The headline theorem, now through the special function

The weight-5 depth-2 closed form (article Theorem "Weight-five depth-two
closed form"),

```
S = Σ_{n≥0} (−1)ⁿ Hₙ/(2n+1)⁴
  = (4 g41 − 3 g32 − 9 g23)/7 + π⁵/224 − (27/224) G·ζ(3) − 2 β(4) log 2,
```

re-verifies to 50 digits with `g41,g32,g23` evaluated by `MultiplePolyLog`
(`S_lhs − S_rhs = 0` at working precision). Independently, V15 now returns a
**closed form for the bare Euler sum** that the old kernel left unevaluated:

```
Sum[(-1)^n HarmonicNumber[n]/(2n+1)^4, {n,0,Infinity}]
  = (I/2)( −HarmonicPolyLog[{-4,1},I] + HarmonicPolyLog[{4,-1},I]
            + PolyLog[3,2,-I] − PolyLog[3,2,I] ).
```

This V15-derived form agrees with the project's PSLQ closed form to 52 digits —
two independent derivations (one experimental, one from Wolfram's analytic
machinery) of the same constant.

## 4. Bonus: the depth-1 MZV frame now auto-reduces

The ordinary multiple zeta values that frame the depth-one layer are evaluated
symbolically by `MultipleZeta` (all classical Euler/MZV reductions, confirmed):

| input | `MultipleZeta` output |
|---|---|
| `{2,1}` | `Zeta[3]` |
| `{3,1}` | `π⁴/360` |
| `{4,1}` | `2 Zeta[5] − π² Zeta[3]/6` |
| `{2,2}` | `π⁴/120` |
| `{3,2}` | `π² Zeta[3]/2 − 11 Zeta[5]/2` |
| `{5,1}` | `π⁶/1260 − Zeta[3]²/2` |

## Conclusion

Every multiple-zeta / multiple-polylogarithm value that this repository could
previously certify only by PSLQ + numerics is now confirmed by Wolfram 15's
native special functions, and the four "irreducible depth-two generators" have
explicit closed forms in Wolfram's harmonic/Nielsen polylogarithm basis. The
store and the article have been annotated accordingly. Nothing in the original
results changed — the PSLQ closed form was correct; it is now also
machine-derivable.
