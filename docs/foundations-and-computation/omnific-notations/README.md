# Notations for Omnific Integers
## Exact holonomic towers and the complexity of equality

Prepared for Vladimir Reshetnikov, 23 September 2026.

## Read the article

`omnific_notations.pdf` is the typeset article. `omnific_notations.tex` is its
standalone LaTeX source, including its bibliography. No external graphics,
font files, or bibliography database are needed.

The principal results are:

- **Theorems 6.2, 7.2, 7.4, and 9.2:** effective holonomic fraction towers;
  their triangular omnific-integer parts; exact floor and truncation; and a
  decidable ordinal-labelled union with ordinal trace exactly the ordinals
  below epsilon-zero.
- **Theorems 11.2 and 11.4:** co-c.e.-complete equality for raw
  primitive-recursive positive-block names, even on a one-monomial family;
  no uniform translation of those raw names into an equality-decidable
  representation, although all their values already have rational names.
- **Theorem 12.2:** positivity in d raw dominance blocks is many-one complete
  for the d-c.e. sets. The hardness uses at most d nonzero monomials.
- **Theorem 13.3:** semantic support validity is Pi^1_1-complete even with
  coefficient one and exponents in one fixed computable dyadic subset of
  (1,2). Checked equality and equality under a validity promise differ.

These are proved as mathematical theorems under the explicit representation
contracts in the article. Their standard ingredients, repository precedents,
and proposed original combined formulations are separated in Section 15.
No claim of exhaustive priority verification, peer review, or Lean
formalization is made.

## Build the PDF

A standard TeX Live installation containing the packages named in the source
is sufficient. Run:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error omnific_notations.tex
```

Alternatively, run `pdflatex` three times so cross-references and the table of
contents stabilize. The delivered PDF was compiled with pdfTeX from TeX Live
and visually inspected. Bibliographic URLs are clickable.

## Run the finite prototype

Use Python 3.10 or later. The recorded run used the Python and SymPy versions
listed in `data/verification.json`.

```sh
python -m pip install -r requirements.txt
python code/verify.py
```

The verification program writes `data/verification.json` and exits with an
error if a check fails. The delivered run passes **41 test groups**, including
521 finite change-event schedules, 780 arbitrary-sign block assignments,
and a 121-node dyadic midpoint embedding with all 14,520 distinct ordered
pairs checked.

The source modules are:

| File | Implemented scope |
| --- | --- |
| `code/holonomic.py` | Rational Euler certificates, finite compatible jets, exact coefficient extraction, derivative-system annihilators for sum and product, fraction field, guarded omnific ring `Z + U*HF[U]`. |
| `code/ordinals.py` | Hereditary finite Cantor-normal-form trees below epsilon-zero, comparison, natural addition/multiplication, ordinary ordinal addition, omega exponentiation. |
| `code/verify.py` | Exact-algebra tests and finite combinatorial checks; creates the verification report. |
| `code/demo.py` | A short executable example of the public prototype interface. |

### What the prototype does not implement

It is not a general surreal computer algebra system. It does not implement
arbitrary exact real coefficient backends, operators over higher-rank
coefficient fields, the entire R_2 ring, the general tower floor or
recognition procedures, or all finite-label field embeddings. These are
mathematical algorithms in the article, not software capabilities claimed
for the delivered code.

Tests of infinite-series identities use generated differential certificates
and the proven finite-jet rule, not merely matching a fixed number of terms.
Nevertheless, the code is not formally verified. Finite test cases do not
prove the mathematical impossibility or completeness results.

The Python constructors accept trusted Python/SymPy objects and are not a
hardened parser for untrusted serialized input. They reject malformed
mathematical data in the documented interface, but callers can still mutate
Python objects; this package is not a security boundary.

## Files and provenance

`PROVENANCE.md` records the inspected repository snapshot and the boundaries
of the source review. The mathematical article cites primary literature,
including the 2026 D-algebraic transseries zero-test. No third-party source
manuscript, downloaded paper, or font file is redistributed.
