# Integration notes

## Suggested destination

Preserve the package intact under a continuation directory such as:

```text
Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/order-ten-stieltjes-generators/
```

The ZIP can also remain in `docs/incoming` until the normal intake process is run.

## Recommended manuscript edits

1. Insert the complete order-ten theorem after the complete order-eight result and the effective eventual-rank theorem.
2. Replace the research item asking to check `6 <= b < 1920` with a completed-status note and move the next fixed-order target to `p=12`.
3. In the order-ten congruence discussion, state that the old class `b congruent 962 mod 2048` is fully resolved by the finite certificate together with eventual rank.
4. Add the ordinary reconstruction theorem after the harmonic-tail rank discussion. It converts formal coordinates into ordinary convergent polygamma-product identities.
5. Place the two-tail multiple-polylogarithm generator near the harmonic-tail generating-function material.
6. Place the Stieltjes correlation kernel in the shifted-Stieltjes chapter or a nearby analytic-generator section; it is logically independent of the determinant certificate.

## Nonnegotiable proof-status details

- The certificate's residues have two meanings: direct determinants for `b=6..9`, retained determinants for `b=10..1919`.
- The exact determinant multiplier is inherited; the modular computation certifies the remaining finite determinants.
- The SHA-256 digest is an integrity check, not the proof object by itself.
- High-precision numerical scripts are diagnostics only.
- The theorem is about formal rational rank, not arithmetic independence of even zeta values.
- The broad all-order conjecture remains open.

## Label policy

The supplied `manuscript_fragment.tex` uses the prefix `otc:`. Preserve that prefix, or systematically rename it during integration, to avoid collisions with existing labels.

## Generated-file policy

Keep the JSON certificate and both replay programs together. Do not copy only the theorem statement or only the digest. The exact coefficient table in the article is generated from `verification/explicit_10_16_zeta2.json`; regenerate rather than editing large integers manually.
