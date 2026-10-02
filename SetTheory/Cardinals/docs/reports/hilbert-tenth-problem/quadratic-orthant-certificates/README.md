# Quadratic Certificates for Maximal Parallelism

**Exact witnesses, sharp growth bounds, and a convexity obstruction**  
Research manuscript prepared for Vladimir Reshetnikov with ChatGPT, 2 October 2026.

## Read first

`article.pdf` is the article; `article.tex` is its self-contained LaTeX source.
The main results are conventional mathematical proofs, not proof-assistant
formalizations. Global priority and peer review are not claimed. The work does
not establish a fixed-arity finite-fold or single-fold theorem for unbounded
halting. The source audit distinguishes inherited facts from the constructions
and quantitative deductions developed in the manuscript.

## Main results

For a fixed consumption/production pair with d species, m rules and H distinct
positive (species, consumption-threshold) pairs:

* One maximal round has a quadratic nonnegative on the entire real orthant,
  with exactly d + 2m + 4H natural auxiliaries when endpoints are supplied.
  For a specified extent vector, the other auxiliaries are unique.
* T-round extent histories use T(2d + 2m + 4H) witnesses. Exact first-halting
  histories use T(2d + 2m + 4H + 1) + 4H + m witnesses.
* A resource cover meets the reactant support of every rule. If rho(A) is the
  minimum rational rank of the corresponding row submatrices, the number of
  maximal extents is O((1 + |x|_1)^(m-rho(A))). For every A, a suitable integral
  input ray attains this exponent. Fixed-horizon affine-ray counts are eventually
  quasipolynomial of degree at most T(m-rho(A)).
* No convex quadratic with any fixed finite number of natural auxiliaries
  represents the deadlock relation x=0 or y=0 for A+B -> C, although xy does.
* Numerical stoichiometry supplied as input on a fixed support admits a quartic;
  degree four is necessary in the globally orthant-nonnegative class.

The sharp counting exponent is for unguarded ordinary maximality. Flat and guarded
semantics are covered by separate certificate theorems. Rule labels distinguish
choices; permutations of individual identical firings are not counted.

## Contents

- `article.tex`, `article.pdf`: complete manuscript and references.
- `code/parallel_certificates.py`: compiler, exact evaluator, canonical witnesses,
  extent enumerator, rank and resource-cover routines, trace counting.
- `code/verify.py`: deterministic exact validation.
- `data/example_certificate.json`: structured and fully expanded example quadratic
  for A+B -> C and A -> B, with one exact witness.
- `data/verification.txt`, `data/verification_counts.json`: actual validation results.
- `PROOF_AUDIT.md`: assumptions, uniqueness, counting and degree audit.
- `SOURCE_AUDIT.md`: consulted sources and repository identifiers.
- `SHA256SUMS.txt`: integrity checksums for the package files (excluding itself).

## Run the exact checks

Python 3.10 or later; no third-party Python packages are needed.

```sh
python code/verify.py
python code/parallel_certificates.py > data/example_certificate.json
```

The verification script prints its results and updates the JSON counts file.
To refresh the text transcript explicitly:

```sh
python code/verify.py > data/verification.txt
```

The included run used Python 3.13.5 and passed all checks. These include 160,524
threshold assignments, 32,805 full-polynomial assignments in a tiny complete
root search, 64 consumption matrices, 38,496 rejected witness mutations, 328
history/first-halting checks, and all 75 labelled simple graphs on 1--4 vertices.
Finite tests support implementation correctness; they are not general proofs.

## Quick start

Matrices in the Python API are stored **as rule columns**, not as rows.

```python
import sys
sys.path.insert(0, "code")
from parallel_certificates import Network, RoundCertificate, HistoryCertificate

# Species order A, B, C. Rules A+B -> C and A -> B.
net = Network(
    consume=((1, 1, 0), (1, 0, 0)),
    produce=((0, 0, 1), (0, 1, 0)),
)
compiler = RoundCertificate(net)
witness = compiler.canonical_assignment((2, 1, 0), (1, 1), (0, 1, 1))
assert witness is not None
assert compiler.polynomial.evaluate(witness) == 0
assert len(compiler.auxiliary_names) == 15

# An arbitrary feasible extent need not be maximal.
assert compiler.canonical_assignment((2, 1, 0), (1, 0)) is None

# One rule A -> nothing; first halting occurs after one round at every n>0.
consume_all = Network(((1,),), ((0,),))
history = HistoryCertificate(consume_all, 1, first_halt=True)
assert history.canonical_assignment((7,), ((7,),)) is not None
```

`RoundCertificate` supports `flat=True`, a tuple of zero/one retention flags,
and conjunctions of `Atom(species, threshold, present)` guards on each rule.
`HistoryCertificate` implements only unguarded, ordinary, retaining histories.
The program-uniform quartic and general Presburger guard compilation are proved
mathematically, not implemented here. The resource-cover search is exponential
in species count. The package is not a Diophantine root-solving program.

## Compile the article

A TeX Live installation with newtx, amsmath/amsthm, microtype, tcolorbox, xurl,
hyperref and the usual LaTeX packages suffices. The bibliography is embedded.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The supplied PDF was rendered and visually reviewed. No font files are included.
