# An explicit formula for Lipparini's minimal infinitary ordinal operation

Research manuscript and reproducible exact checks — September 19, 2026.

## Result and status

The selected target is Problem 6.2 of Paolo Lipparini, *Monotone infinitary
operations on ordinals (extended version)*, arXiv:2505.00424v2, April 30, 2026.
It asks for an explicit definition and study of the least weakly monotone,
e-special strictly increasing operation on countable sequences of ordinals.

The manuscript supplies a proposed complete solution: a three-case finite
ordinal-arithmetic formula and a proof of its admissibility and pointwise
minimality. Relative to Lipparini's already evaluated operation S, the correction
is either zero, a finite increment, or one natural summand omega. Ordinary
addition of omega is NOT a substitute for natural addition of omega.

This is an unrefereed AI-generated research draft. Neither correctness nor
priority has been independently verified. The proof imports the published
characterization of S (Theorem 3.4), stated explicitly in the article. The new
arguments are supplied in full. No proof-assistant formalization is claimed.
The latest arXiv revision consulted still poses the question; the source search
was not an exhaustive priority review. See sources.md.

## Files

- `article.pdf`: the complete typeset article.
- `article.tex`: editable LaTeX source, including bibliography.
- `code/ordinals.py`: exact hereditary finite Cantor-normal-form arithmetic,
  and three formula-evaluation paths.
- `code/verify.py`: reproducible comparisons, hand-checked examples, and
  independently computed ranks of finite multiset posets.
- `results/verification.json`: actual deterministic verification output.
- `results/verification.txt`: human-readable copy of the same output.
- `proof_audit.md`: dependencies, delicate proof steps, and limitations.
- `sources.md`: the primary references, version information, and source audit.
- `results/quality_report.txt`: compilation and PDF checks.
- `build.sh`: runs the checks and rebuilds the PDF.

No external reference PDFs or standalone font files are included.

## Mathematical scope

The theorem is stated for all omega-indexed sequences of arbitrary ordinals.
The Python implementation is narrower: it represents ordinals below epsilon_0
using hereditary finite Cantor normal forms. It needs a **certified positive
threshold** and a finite exceptional-coordinate list, with multiplicity. It
cannot infer an arbitrary infinite sequence's threshold from finite samples.

A threshold is the least ordinal e for which only finitely many sequence
entries are >= e. Every such exceptional entry must be present in the list.
Subthreshold entries may also be supplied and are ignored. The unspecified
infinite background must actually have the stated threshold.

The exact tests are supporting checks, not a proof of the transfinite theorem.
The finite-poset ranks are computed from the order relation, not from the rank
formula being checked. Suprema of bounded finite models do not by themselves
recover the unrestricted transfinite ranks; the article explains the failure.

## Reproduce the checks

Requirements: Python 3.10 or newer; standard library only.

Run from this directory, without Python's `-O` option (tests use assertions):

```sh
python3 code/verify.py --seed 20260919 --trials 20000 \
    --output results/verification.json > results/verification.txt
```

The supplied run passed 20,000 comparable-profile tests, 40,000 randomized
formula-agreement checks, 24,916 corrected-block cross-checks, 40,000
permutation/zero-invariance checks, 648 exhaustive small-profile formula checks,
6,084 natural-commutativity checks, and 3,081 ordinal-difference checks. It also
computed ranks for 994 states in three finite posets, checking 122,738 strict
comparisons, and evaluated 15 specified examples.

These counts refer to overlapping audit categories, not disjoint independent
mathematical proofs. All three formula paths use the same ordinal-arithmetic
backend. The fixed seed and all outputs are included for reproducibility.

## Use the evaluator

```python
import sys
sys.path.insert(0, 'code')
from ordinals import ONE, OMEGA, finite, omega_power, evaluate_n

# One exceptional omega^2 + 5, with all other entries equal to omega.
epsilon = OMEGA + ONE
exception = omega_power(finite(2)) + finite(5)
print(evaluate_n(epsilon, [exception]))
# w^(2)*2 + w + 5
```

`Ord.__add__` is ordinary ordinal addition. The `.natural()` method is natural
addition. String output uses `w` for omega and `*k` for a finite coefficient.

## Build the article

Requirements: a standard TeX Live installation with the packages used in
`article.tex`, including `newtx`, `tcolorbox`, and the AMS packages.
The source uses pdflatex; no shell escape is needed.

```sh
bash build.sh
```

The build script first runs the deterministic audit and then runs pdflatex
three times to stabilize the table of contents and cross-references. Intermediate
TeX build files are created locally but are not part of the distributed archive.
