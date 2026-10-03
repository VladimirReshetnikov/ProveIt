# Exact polynomial constructor correction

Date: 3 October 2026. Scope: the low-level `Poly` constructor in
`replay/core/sparse_mass.py`, regression tests, and packaging provenance.
No theorem, witness budget, polynomial formula, or valid mathematical input has
changed. This is executable boundary hardening, not formal verification.

## Reproduced defect

Original archive SHA-256:
`90c9dadeccad7c70c777b141b0c65029b992048fd69448f0f8e035ec522cdc68`.
Original producer SHA-256:
`1c35e0104730dfe99c9be4c350b49d66646d8e0dd7c7580b262367f1070d02c8`.

On that exact original producer:

```python
from sparse_mass import Poly, Builder
witness = 2**60 + 1
p = Poly((((), float(2**60)), ((0,), -1.0)))
b = Builder()
b.new("x", witness)
b.constrain("residual minus one", p)
print(p.evaluate([witness]), b.validate_witness(), b.score())
# 0.0 True 0.0
print(2**60 - witness)
# -1
```

Floating-point multiplication loses the final unit. The intended integer
residual is -1, whose squared score is 1. The frozen dataclass also did not
freeze supplied nested containers:

```python
terms = [[(0,), 1]]
p = Poly(terms)
print(p.evaluate([3]))  # 3
terms[0][1] = 2
print(p.evaluate([3]))  # 6
```

The original constructor accepted these noncanonical forms:

```python
Poly((((1, 0), 1),))              # unsorted variable indices
Poly((((0,), 1), ((0,), 2)))      # duplicate monomials
Poly((((1,), 1), ((0,), 1)))      # unsorted terms
Poly((((0,), 0),))               # explicit zero coefficient
```

The corrected direct constructor rejects all the above with `ValueError`.
It requires exact tuples throughout; exact Python `int` coefficients and
indices (not bool, float, or numeric subclasses); nonzero coefficients; sorted
indices; and distinct, sorted monomials. `Poly.make(...)` remains the
canonicalizing interface, combining equal monomials, removing zeros, sorting
terms and copying mutable inputs. Repeated indices remain valid powers, and
negative indices remain valid free parameter references. Zero and constant
polynomials remain accepted.

The JSON decoder and bound-export verifier already enforce exact integer
coefficients. Original and corrected code reject an otherwise valid shipped
certificate with a coefficient replaced by its numerically equal float.
This defect was not an accepted false bound-export certificate.

## Reproduction and evidence

Requirements: Python 3.10+, standard library, POSIX shell. From this directory:

```sh
python3 replay/verify_manifest.py
./run-replay.sh --regenerate-source
```

Use `sh run-replay.sh --regenerate-source` if extraction loses executable
modes. The archive preserves mode 0755 for both shell scripts. The corrected
runner includes the new exactness suite by default. Standalone:

```sh
python3 replay/core/test_poly_exactness.py
```

It checks 24 malformed constructor categories, the float false-zero case,
immutable/canonical construction, signed parameter indices, repeated-variable
powers, and 2,700 independent exact-expression comparisons across 300
seeded polynomial pairs. Exact residual -1 and score 1 are verified. Factories
and the existing bound-export boundary are tested too. The optional
`--baseline-module PATH` mode additionally reproduces the defect and compares
all 2,700 valid expression coefficient lists with the original producer;
that mode was run against the untouched extracted delivered file.

The original full replay passed all 18 stages, including fresh construction
of both source certificates (n=0, T=7 and n=2, T=41). The corrected full replay
passes those same stages plus the exactness stage. Fresh outputs are under
`.replay`. Packaged summaries are `receipts/release-verification.json` and
`receipts/poly-exactness.json`.

## Changed-code / unchanged-mathematics ledger

- Changed behavior: `Poly.__post_init__` rejects inputs outside the declared
  exact, immutable, canonical representation
- Changed runner: executes and compares the new standalone exactness receipt
- New test and receipt: `replay/core/test_poly_exactness.py` and
  `receipts/poly-exactness.json`
- Refreshed provenance: README, this note, SOURCE-PROVENANCE, SHA256SUMS,
  coefficient-crosscheck receipt (producer hash only), and release-verification
  receipt (new stage and producer hash)
- Byte-identical mathematics: all six `paper/*.tex` files, the PDF, all six
  shipped coefficient fixtures, and both complete source-table CSVs
- Stable core, independent dynamics, coefficientwise compilation, source-rule,
  paid-loader/observer, mass-two, and semilinearity results are unchanged.
  Regenerated gzip fixtures match after decompression; header timestamps are
  not mathematical data
- No optional optimization, source-construction change, theorem strengthening,
  improved universal constant, or public publication is included

Reference reviewed read-only:
https://github.com/VladimirReshetnikov/ProveIt/commit/9975af7e1354b83422dc9a2dc13abce4992d0c26.
External code was not executed or applied. The guard and tests were written
independently against the delivered code.
