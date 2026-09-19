# The minimal e-monotone infinitary ordinal sum

**An unrefereed proposed solution to Paolo Lipparini's Problem 6.2.**
Research note prepared with ChatGPT, 19 September 2026.

## Read first

`article/explicit_ordinal_sum.pdf` is the complete article. The editable source
is `article/explicit_ordinal_sum.tex`. The note proposes an explicit formula
for the least operation satisfying the weak monotonicity and e-special
strict monotonicity axioms in arXiv:2505.00424v2 (30 April 2026).

The proof consists of an arithmetic admissibility upper bound and a
rank-theoretic minimality lower bound. The one imported theorem about
infinitary operations is Lipparini's explicit formula and minimality theorem
for the weaker operation S (Definition 3.1 and Theorem 3.4). That dependency is
stated precisely in Proposition 6.1 of the article. The other arguments are
provided, including an explicit countable-multiset profile order, its rank,
finite-product ranks, the absorption lemma, correction rules, bounded-poset
heights, and finite-cap ranks.

This work has **not** been independently refereed, checked in a proof
assistant, submitted to the author, or published as an accepted solution.
The April 2026 source still poses the question; the priority search was not
exhaustive. Successful tests do not prove the transfinite result.

## Contents

- `article/explicit_ordinal_sum.pdf`: compiled research article.
- `article/explicit_ordinal_sum.tex`: LaTeX source, with inline bibliography.
- `code/ordinals.py`: exact finite hereditary Cantor-normal-form arithmetic.
- `code/verify.py`: deterministic symbolic stress tests and independent finite
  poset rank computations.
- `code/demo.py`: executable examples.
- `checks/results.json`: structured results of the supplied default run.
- `checks/run.txt`: the same run's console report.
- `checks/demo.txt`: recorded demonstration output.
- `REVIEW_NOTES.md`: theorem dependencies, proof-sensitive conventions, and
  validation limitations.
- `build.sh`: rebuild the PDF using pdfLaTeX.

## Run the implementation

Python 3.10 or later is sufficient; no external packages are required.
From the root of this directory:

```sh
python3 code/demo.py
python3 code/verify.py --output checks/results.json
```

The default run uses seed `20260919`, 10,000 randomized cases, a 223-ordinal
basis, and an exhaustive 1,000-profile family. It reports 734,869 counted
checks, all passing. Some counted cases contain several assertions. Runtime
is machine-dependent (about 22 seconds in the supplied environment).

The finite rank calculation independently computes 912 ranks across the
finite domains 1 <= M <= 5 and 0 <= H <= 4, then compares them to the
finite-cap formula. These truncated ranks are not the transfinite ranks of
the full profile poset; the article explains why their supremum need not
recover the full rank.

## A small example

```python
# Run from code/, or add code/ to Python's module search path.
from ordinals import OMEGA, ONE, Profile

p = Profile(OMEGA, (OMEGA,))  # cut omega, one exceptional omega
print(p.value())             # w^2 + 1
print(Profile(OMEGA + ONE).value())  # constant omega: w^2 + w
```

The constructor accepts a **positive cut** and a finite multiset of heads,
all at or above that cut. Their order is immaterial; multiplicity is retained.
For a constant tail with value t, the cut is t+1, not t.

The engine represents ordinals **below epsilon_0**, not arbitrary ordinals.
The theorem is stated for arbitrary ordinal entries, but the tests exercise
only the engine's finite-notation domain. The evaluator accepts a profile;
it does not infer a tail cut from an arbitrary infinite sequence or program.
There can be no such uniform algorithm, even for all computable binary
sequences, by the halting-problem reduction in the article.

## Rebuild the article

A TeX Live-style installation with newpx, amsmath/amsthm, mathtools,
tcolorbox, hyperref, cleveref, listings, and the other packages named in the
preamble is sufficient:

```sh
sh build.sh
```

No bibliography engine is needed. Font binaries and downloaded copies of
Lipparini's paper are not included. Build logs and auxiliary TeX files are
not part of this distribution; rebuilding creates them locally.

## Sources

Paolo Lipparini, *Monotone infinitary operations on ordinals (extended
version)*, arXiv:2505.00424v2, 30 April 2026.
https://arxiv.org/abs/2505.00424v2

Published counterpart: *A Monotone Infinitary Operation on Ordinals*,
Mathematical Logic Quarterly 72(2), e70019 (2026).
https://doi.org/10.1002/malq.70019
