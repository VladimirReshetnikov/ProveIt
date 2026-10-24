# Auxiliary growth after Pell fusion

This packet supplies six explicit integer polynomials in ten **strictly
positive** unknowns. The cheapest evaluator uses 89 binary arithmetic
operations and has exact total degree 288. Its four fixed coefficients
are reconstructed by a finite portable recipe and also supplied as
compressed integer payloads.

| Circuit | Operations | Exact degree |
|---|---:|---:|
| `equations/uncentered.json` | 89 | 288 |
| `equations/upper.json` | 91 | 283 |
| `equations/sharp.json` | 92 | 278 |
| `equations/direct_uncentered.json` | 94 | 262 |
| `equations/direct_upper.json` | 96 | 258 |
| `equations/direct_sharp.json` | 97 | 254 |

The new argument uses an auxiliary Pell coordinate already present in the
equation to bound the fused radical. Its fifth-index gap proves `b>8Q`
before any transport sign or denominator cancellation. This licenses
`W=1+h*b` and allows the cheapest equations to omit the product center.
The four centered alternatives save one or two operations against the
corresponding saturated incoming parents without changing their degrees.

`PROOF.md` prints the complete equation, both directions of its ordinary
arithmetic equivalence, the logical dependency order, and explicit
nonzero highest homogeneous forms. The earlier source and saturation
proofs are retained under `provenance/`; `SOURCE_PINS.json` records exact
archive and dependency hashes. The complete compact44 BFS tuple is used
as a whole. The differently calibrated original44 tuple is not substituted.

The resulting theorem is that ZFC proves the absence of positive zeros
equivalent to syntactic Con(ZFC), by composition with the inherited
native/controller/refutation calibration. No global minimality, assertion
of consistency, or new end-to-end proof-assistant certificate is claimed.
The variables in these six equations do not range over all integers.

## Reproduce

Only Python's standard library is needed. From this directory:

```sh
python3 -B build.py --check
python3 -B verify.py
python3 -B -O verify.py
```

The verifier checks complete row maps, exact full-formula evaluations,
universal polynomial identities, coefficient reconstruction, exact
specialized polynomial degrees over Z, and deliberate corruptions.
Global degrees and semantic equivalence are proved in `PROOF.md`; finite
checks are not substitutes for those proofs.

AI assistance was used in the derivation and preparation of this packet.
Retained upstream licenses and notices apply to their respective sources.
