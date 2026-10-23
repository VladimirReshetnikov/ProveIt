# Support-aware digit coding and sharper Pell norms for Con(ZFC)

Research package prepared for Vladimir Reshetnikov's ProveIt repository,
23 October 2026. Start with **report.pdf**; its complete LaTeX source is
**report.tex** plus **sections/**.

Source snapshot: [`124c07c0b77a9e20e84676514d8b1ff78536ea3f`](https://github.com/VladimirReshetnikov/ProveIt/tree/124c07c0b77a9e20e84676514d8b1ff78536ea3f/Computability/DiophantineConsistency).
This includes the wave-6 packages 38–45. Comparison against wave 5 alone
would overstate the improvements.

## Exact results

For every listed polynomial, using its stated witness domain and the
complete fixed coefficient tuple, the ordinary mathematical proof gives

> ZFC proves: “this polynomial has no zero in its stated domain” if and
> only if Con(ZFC), for the repository's fixed syntactic proof calculus.

This uses the identified inherited K215 calibration, native compiler and
arithmetic lemmas. No proof of Con(ZFC), global minimality theorem, new
variable-count record, or new end-to-end Lean/Rocq certificate is claimed.

| Domain | Exact total degree | Live operations | Canonical polynomial |
|---|---:|---:|---|
| 9 strictly positive integers | **32,568,568** | **652** | `nine/generated/multitarget_nine_positive.json` |
| 9 nonnegative integers | **32,568,568** | **655** | `nine/generated/multitarget_nine_natural.json` |
| 10 unrestricted integers | **59,564,744** | **653** | `data/polynomial.json` |
| 11 strictly positive integers | **990** | **117** | `eleven/generated/eleven_full_product.json` |
| 11 strictly positive integers | **994** | **115** | `eleven/generated/eleven_short_product.json` |
| 15 strictly positive integers | **44** | **76** | `short/offset44.json` |

The nine-variable route uses the Jones numerical ratio contracts; it does
not depend on Sun's ten-integer reduction. The ten-integer companion does
use the explicitly cited Sun 2026 preprint bridge, as parameterized in
package 40. Positive and natural domains must not be silently replaced
by unrestricted integers.

## Main contribution: isolate supported pairs only

The source system uses 71 padded quadratic monomials among all 528 pairs
of its 32 positions, including the constant position. Every active pair
must have a unique sum **among all pairs**. Inactive pairs may collide.
The article proves this weaker sufficient condition and the off-target
coefficient bound needed for carry coding.

The certified labels, in the precise parent order in the article, are

```text
0;
200,199,193,166,11,57,125,37,93,113,153,16,158,192,120,64,
139,198,144,23,15,43,18,165,179,112,10,44,117,71,119
```

The maximum label is 200, versus the earlier full-Sidon maximum 799.
All 71 active sums are isolated, despite 130 collided unused sum
positions. The 528 pairs occupy 285 distinct sums. Target digits are
`400 + 401*(j-1)` for `j=1,...,22`.

| Matching source baseline | Source degree / operations | This package |
|---|---:|---:|
| Package 45, 9 positive | 129,875,980 / 788 | 32,568,568 / 652 |
| Package 40, 10 integer | 237,520,456 / 782 | 59,564,744 / 653 |
| Package 38, 11 positive | 1,154 / 123 | 990 / 117 or 994 / 115 |
| Historical wave-2 gap SOS, 15 positive | 44 / 78 | 44 / 76 |

The packed degrees fall by about 74.92%. This is an explicit instance
improvement, with no assertion that 200 is an optimal maximum label or
that the support-sensitive idea has global literature priority.

## Two additional constructions

**Eleven positive variables.** A new relative-error estimate compares
`I*sqrt(G) - c*sqrt(D)` directly with `(b+c*sqrt(D))/(Q-1)`. It permits
the smaller outer separator `K=I*T+1` before the absorbed index quotient
has been recovered. Thus package 38's quotient absorption and package
44's removal of an inner separator can be combined. The full carrier
gives degree 990/117 operations; the short carrier gives 994/115.

**Fifteen positive variables.** The degree-44/76 evaluator combines
historical root gaps with a shorter pairing of norm/index/transport
residuals. Degree 44 and the gap substitutions already occur in wave 2;
the contribution here is the two-operation saving. The historical
67-operation equation remains shorter if operations alone are optimized.

## Exact coefficients

All four ports are bound together to the package-31 tuple
`wang943-mixed-121x8801`, with the already shifted `MF_source` port.
Their bit lengths are 1,064,921; 1,070,004; 1,064,921; and 1,064,922.
The four raw payloads total 533,099 bytes (10,485 bytes gzip).

`coefficients/` contains the finite recipe, literal 943-tile table,
compressed integer payloads, manifest, provenance and inherited licenses.
`audits/verify_coefficients.py` independently reconstructs them without
importing the original builder. `fixed/` materializes all 17 nine-variable
and 16 ten-variable nonliteral fixed leaves. Their encodings and hashes
are part of the specification. A fully expanded polynomial coefficient
list is not the representation being claimed.

## Reproduce

Python 3 and NumPy are required for the combined finite checks. NumPy is
used only by the eleven-variable polynomial-ray audit; the other auditors
use the standard library. No network access or external checkout is needed.

```sh
python3 verify_all.py
```

This runs the five audits both normally and with `python3 -O`, compares
the nine supplied eleven/offset objects exactly with their builders, and
checks inherited source-copy hashes. The aggregate receipt is
`audits/ALL_CHECKS.json`; per-run logs are in `audits/logs/`.

The checks include all 44 exact symbolic digit-extraction identities,
all 528 pair sums, actual coefficient reconstruction, all 33 fixed leaf
reconstructions, circuit liveness and paid operation counts, exact
algebraic norm identities, and degree certificates. Modular and finite
Pell examples are supplementary diagnostics, not substitutes for the
unbounded mathematical proofs.

Compile with a standard TeX Live installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

`make verify`, `make pdf` and `make rebuild` provide convenient targets.
Rebuilding uses only the attached fixed data. `SHA256SUMS` records the
distributed file bytes; rerunning an audit can update its receipt.

## Proof and integration map

- `report.tex`, `report.pdf`, `sections/`: main mathematical article.
- `SPARSE_PACKING_PROOF.md`: detailed support and nine-variable proof.
- `audits/eleven_combination_review.md`: detailed independent derivation
  of the combined eleven-variable argument.
- `short/PROOF.md`: degree-44 regrouping, completeness and history.
- `INTEGRATION.md`: proposed adoption paths and formalization boundaries.
- `SOURCES.json`, `upstream/ADDITIONAL_SOURCE_PINS.json`,
  `coefficients/SOURCE_PINS.json`, `short/historical/SOURCES.json`:
  immutable source references and file hashes.
- `upstream/`: inherited proofs and comparison sources, retaining their
  original numerical claims. They are provenance, not active definitions.
- `NOTICE.md`, `LICENSE`, `coefficients/licenses/`: attribution and licenses.

This is AI-assisted mathematical research prepared for review and
incorporation. Independent agent checks are not external human review.
The archive does not claim a new proof-assistant build or a checked
derivation inside the object-language ZFC calculus. It preserves the
distinction between an ordinary mathematical proof formalizable in ZFC,
finite computational certificates, and the repository's separate formal
development. No remote repository changes have been made.
