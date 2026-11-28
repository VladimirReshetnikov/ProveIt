# Formal source status

`OrbitCharacterSum.lean` is a proposed standalone Mathlib proof file. **It is uncompiled.** There was no Lean or lake executable available for this review.

The file contains proposed proofs, without `sorry`, `admit`, or new axioms, of four elementary statements:

1. A character sum over a finite group is zero or the group cardinality.
2. A weighted sum over an explicitly presented torsor is zero or the stabilizer cardinality times one character value.
3. Dividing by that cardinality gives zero or the single value.
4. If that value has finite multiplicative order, the normalized value is zero or has finite order.

The domain group is not assumed commutative. The torsor statement requires an explicit equivalence and a weight-factorization proof; it does not conceal the source-specific transporter construction.

The following remain to be formalized and integrated: the effective observed gauge group, character descent, its action on the reduced edge tuple, the anchored-chain stabilizer, the compatible quotient/CRT comparison, the first-datum replacement, and its downstream consumer updates. The report gives mathematical proofs and an implementation sequence for these tasks.

In a suitable existing Mathlib checkout, a developer can copy this file there and attempt:

```bash
lake env lean OrbitCharacterSum.lean
```

This command has not been run here; API or elaboration repairs may be required. No new lake project or unverified dependency lockfile is supplied.
