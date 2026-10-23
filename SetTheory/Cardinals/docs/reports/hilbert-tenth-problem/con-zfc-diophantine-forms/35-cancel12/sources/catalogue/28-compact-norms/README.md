# Smaller norms for Diophantine ZFC consistency

Prepared for Vladimir Reshetnikov and incorporation into ProveIt, 23 October 2026.

**Two improvements over the inspected ProveIt packages 16–23:**

| Construction | Unknown domain | Equations | Exact degree / maximum degree | Binary operations |
|---|---|---:|---:|---:|
| Compact norm product | 12 strictly positive integers | 1 | 1081 | 116 |
| Compact norm system | 12 strictly positive integers | 3 | 1072 | 112 |
| Compact norm sum of squares | 12 strictly positive integers | 1 | 2144 | 119 |
| Structured signed Jones finalizer | 9 nonnegative integers | 1 | `93264*5^33+288` | 20,547 |

For each construction, ZFC proves that the stated system has a solution if
and only if there is a finite ZFC refutation. Negating gives the requested
equivalence between unsolvability and `Con(ZFC)`. This is an ordinary
mathematical proof composed with explicitly identified inherited compiler,
Pell, Jones-reduction and K215-calibration theorems. It does not prove
consistency and is not a new end-to-end Lean or Rocq certificate.

## Read first

`report.pdf` and its complete source `report.tex` / `sections/*.tex` give the
formulas, proofs, comparison, exact-degree certificates, verification scope,
and further research questions. `INSTANCE.json` fixes the actual coefficient
binding and domains. All formula abbreviations are substituted polynomial
expressions, not additional unknowns.

The twelve-variable product improves degree 1145 / 123 operations from
package 20 to **1081 / 116**, and improves degree 1353 at the same 116
operations from package 21. It dominates the inspected twelve-positive-variable
products on these two measures. The nine-variable degree is exactly
**10,857,358,574,867,248,535,156,250,288**, a reduction of approximately
42.374138% from package 18, at a cost of sixteen operations.

These are improvements in a tradeoff landscape, with no global minimality
claim. The older 67-operation equation, low-degree systems and constructions
over unrestricted integers retain their respective advantages. In particular,
the new twelve-variable proof uses `h > 0`; it must not be silently reused
over all integers or inserted into the older signed-h lift.

## What changed mathematically

The twelve-variable norm uses the sharper uniform conjugate bound
`|y'| < (T^2 + X*I^2)*sqrt(G)` and the smaller root coefficient `4*H*W`.
Two automorphism arguments recover the eliminated integer roots. Rational
Pell saturation recovers the last auxiliary root. A residue modulo four
excludes the negative unit in the final product.

The nine-variable construction keeps the exact package-18 quartic and Jones
packing expressions. Structured bounds for the actual radicals reduce the
weight degrees. A signed-divisor lemma keeps `u = J*F` signed and uses a
polynomial upper bound for `abs(v/u)`, avoiding the old squared divisor and
dividend. The proof includes negative packed `R`, zero `C`, zero `H`, and
the zero-sum radical case.

## Fixed coefficients

The authoritative source revision is
`ae3007ca4467011e0e051c84acb4a1dd13971b0e`:

<https://github.com/VladimirReshetnikov/ProveIt/tree/ae3007ca4467011e0e051c84acb4a1dd13971b0e/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms>.

Both constructions use the **entire published compact Wang943 tuple** from
package 19. Its base is `B = 2^(5^10)`. The four raw integers occupy
5,312,269 bytes, or 20,260 bytes in the included deterministic gzip files.
The coefficient named `MF` in the polynomial is the **shifted**
`MF_source`, not the native mask. All four raw SHA-256 hashes are recorded
in `INSTANCE.json` and `compiler/COMPACT_PAYLOAD_MANIFEST.json`.

The nine-variable DAG has 348 nonliteral fixed leaves. Its much larger Jones
indices and weighted quartic coefficients are specified by bounded, explicit
recipes in `circuits/nine/constants.json` and `index_bound_s.json`; those
index integers are not expanded. No fixed coefficient depends on whether
ZFC is consistent. There is no unbounded search hidden in a coefficient.

The immutable quartic source retains historical metadata. The current whole
tuple in `INSTANCE.json` and `vendor/jones18/NINE_BINDING.json` is authoritative
for this release. Its row 16 uses the old transport quotient `z`; the article
records its relation to the shifted convention in some inherited proof notes.

## Reproduce

Python 3.10 or later, standard library only:

```bash
python3 reproduce.py
```

This regenerates both constructions in a temporary directory, compares exact
JSON bytes, runs the independent checks using the actual compressed
coefficients, and writes `verification/REPRODUCED.json`. It requires neither
network access nor a full repository checkout.

To rebuild the tiles, coefficient geometry and all four raw integer payloads,
including an independent byte-for-byte audit:

```bash
python3 reproduce.py --rebuild-coefficients
```

The extra raw data occupy about 5.3 MB temporarily. The enormous Jones indices
are evaluated from their finite recipes modulo primes, never expanded.

To rebuild the article:

```bash
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The supplied PDF was compiled and visually reviewed. Python reproduction does
not require TeX.

## Contents and evidence

- `circuits/compact12_*.json`: complete division-free twelve-variable circuits.
- `circuits/nine/`: nine-variable DAG, shifted quartic, exact fixed-index
  recipes, and verification receipt.
- `code/`: two builders and two verifiers. The twelve-variable independent
  verifier does not import either emitter.
- `compiler/`, `audit/`: attributed upstream Wang943 construction, table,
  proofs, materializer, independent auditors, bindings and compressed integers.
- `proofs/`, `verification/`: new proof notes and independent review records.
- `vendor/`: immutable inherited sources and proof interfaces needed to review
  the composition. They are source excerpts, not a separately buildable copy of
  the complete Lean/Rocq development.
- `SOURCE_MANIFEST.json`: pinned origins and hashes for the retained sources.
- `MANIFEST.sha256`: hashes of the release files.
- `NOTICE.md`, `licenses/`: attribution, contribution boundaries and terms.

The twelve-variable verifier checks a 295-monomial generic norm identity and
a 1,649-monomial symbolic leading-form certificate, with all four fixed ports
symbolic. The nine-variable verifier authenticates the quartic source,
regenerates 346 weighted coefficient records, handles the leading cancellation,
and checks twelve actual-coefficient output evaluations plus 312 named
intermediates modulo three primes. It also checks 6,912 majorant assignments,
134,400 bounded finalizer evaluations and 468 constructed witnesses.

These finite audits detect circuit and transcription errors. The quantified
claims rest on the mathematical proofs and the named inherited theorems; a
hash or finite check is not a proof of an unbounded semantic equivalence.

## Suggested placement

Add this directory as a new numbered package under
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/`.
Retain the earlier packages: they remain sources and comparison points.
No existing GitHub file was changed in preparing this archive.

The report ends with seven concrete research directions, including the newly
exposed degree bottleneck, a justified signed-domain transfer, general use
of the signed-divisor lemma, a smaller quartic parent, and formalization of
the new algebraic interfaces.
