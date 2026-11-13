# Independent review of the modulo-223 strong-witness obstruction

The [author packet](../../research/p64-qcube75-q2-strong-choice-obstruction/README.md)
excludes an auxiliary-unit solution for one **specific symbolic strong Pell
witness** associated with a q²-scale partial tuple. This review confirms that
scope; it does not exclude other strong witnesses or establish nonexistence
of a full graph zero.

The analytic descent is valid for integer `I≥2` and a positive auxiliary
solution of `x²−(I²−1)y²=1`, taking `x=I*|V|`. The inequalities
`(I−1)y<x≤Iy` give `0≤Iy−x<y`, and
`I*x−(I²−1)y>0`; the norm is preserved. Descent therefore reaches `(1,0)`
and recovers a power of `I+sqrt(I²−1)`. Modulo `I`, the real coefficients
at even exponents are `±1`, so `I|x` forces an odd exponent. This reasoning
covers either sign of the original `V` via its absolute value.

The [independent checker](check.py) uses norm-one bitwise doubling for the
4686-bit main Pell coefficient and the symbolic strong witness modulo 223.
It then enumerates *Pell pairs and parity*, rather than the author's scalar
recurrence, confirming a 32-state cycle and the same signed residue set
`{1,47,86,101,122,137,176,222}`. The required residue `−c=204` is absent.
It also checks the descent map on 52 bounded genuine positive Pell solutions.
Those finite sanity cases do not replace the preceding general descent
argument. The main coefficient, strong witness residues, both author packet
hashes, and the q² partial packet hashes are pinned in the script.

This is an external mathematical and finite-residue review, not a Lean proof,
a claim about arbitrary `f,i`, a compact44-port statement, or a counterexample
to existential equivalence. No Lean was run. The independent
[result](result.json) and checker are reproducible with:

```sh
nice -n 19 ionice -c 3 timeout 60s python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube75-q2-strong-choice-independent/check.py
```

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `b8b88ec2c94ca53d48765babe7797f648e8faab791f6261e4266412a36eefac9` |
| `result.json` | `1416ea72656b40e18fce103d8dbedb89b6c08aed162beefaecf8c0d39ada001b` |
