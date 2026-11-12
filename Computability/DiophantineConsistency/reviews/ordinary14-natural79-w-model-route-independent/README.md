# Independent source review: natural-79 forced-w model route

The [source route](../../research/ordinary14-natural79-w-model-route/README.md) identifies the necessary zero-specific unit and signed divisibility obligations and gives mathematically valid conditional commutative-ring identities. Neither its graph-to-model route nor its two Lean proof scripts have been elaborated; no iPRA endpoint, provider closure or physical binding follows.

If `H | U*(d-a*c)`, write `U*(d-a*c)=H*z`. Under `d²=1+(a²+H)c²`, the displayed witness `z*(d+a*c)-U*c²` satisfies

```
H*(z*(d+a*c)-U*c²) = U.
```

Likewise `H=4Y+3`, `U=Y*q²`, and `U=H*z` give `3q²=H*(q²-4z)`. Both identities hold over arbitrary commutative rings; this review checks their formal polynomial rearrangements. They do not themselves provide the required model norm, signed quotient, graph zero equations or natural order contradiction.

The inspected source signatures state, for arbitrary `IΣ₁` arithmetic models, the positive-divisor square-root divisibility lemma, a scaled quotient, a natural magnitude representing either sign in the difference ring, and reflection of divisibility of embedded natural values. These are appropriate candidates to avoid importing standard-integer factorization into nonstandard models, but their composition, casts, proof axioms and coherent providers have not been checked here. In particular, the existing 74 own-zero extractor explicitly requires positive slot 6, so it cannot be invoked directly at the critical `w=0` valuation. A separate 79 graph unit extraction and literal residue patterns remain necessary.

The receipt pins the relevant source declarations and selected 79 graph rows, and checks the ring identities as formal sparse polynomials. It does not run Lean or verify the full graph-to-factor, model-to-iPRA or physical-file chain.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-w-model-route-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-w-model-route-independent/result.json
```
