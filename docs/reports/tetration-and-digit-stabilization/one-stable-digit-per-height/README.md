# Exactly One Digit per Height

## Result

This package develops a self-contained resolution, as written, of the three
conjectural comments in OEIS A324017. They were still labelled conjectures in
the entry retrieved on 19 September 2026. The first two are proved; the third
is disproved for every nontrivial base in its stated domain.

Let q >= 4 be even, a = q - 1, T_0 = 1, and T_(h+1) = a^(T_h).
For every h >= 0 and r >= 1 the central theorem is

    T_(h+r) - T_h == -2*q^h  (mod q^(h+1)).

Thus each added height contributes exactly one new stable radix-q digit.
The article also gives exact prime-adic distances, unique fixed points,
a factorization-free digit-lifting algorithm, an extension to higher Knuth
arrow ranks, and a sign-sensitive local p-adic Lambert W formula.

The smallest counterexample to the third conjecture is

    3 ↑↑ 2 = 27       (mod 64),
    3 ↑↑ 3 = 59       (mod 64).

These are mathematical proofs, supplemented by finite computations. They
have not received independent peer review. The literature search does not
establish worldwide priority. General modular-tetration stabilization,
lifting-the-exponent arguments, and the p-adic Lambert W function are
established background, not claimed discoveries here. No claim is made to
resolve general analytic tetration, arbitrary Conway chains, or unrestricted
fast-growing hierarchies. Nothing has been submitted to OEIS on your behalf.

## Contents

- `article.pdf`: the 16-page article, including proofs, algorithms and references.
- `article.tex`: complete, self-contained LaTeX source; bibliography is embedded.
- `code/tower_digits.py`: exact modular tetration and higher-arrow evaluator.
- `code/verify.py`: independent modular oracle and reproducible verification.
- `data/verification.json`: passing test report and per-family counts.
- `data/counterexample.json`: exact counterexample certificate.
- `data/residues.csv`: stable residues and preceding-height residues.
- `data/local_lambert.csv`: exact local Lambert-series checks.
- `PROOF_AUDIT.md`: proof dependencies and potential failure modes checked.
- `SOURCES.md`: primary-source record and limits of the status check.
- `Makefile`: optional test and PDF-build targets.

No third-party Python packages are needed. No font files or third-party
papers are included.

## Run

Use Python 3.9 or later. Run from this directory:

```sh
python code/verify.py
python code/tower_digits.py 4 3 --height 2
python code/tower_digits.py 4 3 --height 3
python code/tower_digits.py 10 60 --rank 1000000 --argument 2
```

The finite-height examples return `27` and `59`. The last command computes
9 with one million Knuth arrows and right argument 2, modulo 10^60. It returns

```text
864868894914047889985007525482726503475610748087597392745289
```

The full enormous integer is never constructed. The default command without
`--height` or `--rank` returns the stable residue:

```sh
python code/tower_digits.py 10 20
```

Here q is always the **radix**, and the tower base is **q - 1**. Precision is
measured in radix-q digits, not binary bits and not digits in the tower base.
The special function `local_lambert_residue(q, p, K)` instead uses p-adic
precision K; its docstring states this distinction.

### Python API

```python
import sys
sys.path.insert(0, "code")
from tower_digits import (
    stable_residue, tetration_mod, knuth_mod,
    difference_residue, predicted_prime_distance,
    local_lambert_residue,
)

assert tetration_mod(4, 2, 3) == 27
assert tetration_mod(4, 3, 3) == 59
assert stable_residue(4, 3) == 59
assert difference_residue(4, 2, 1) == 2
assert predicted_prime_distance(4, 2, 2) == 5
assert knuth_mod(10, 10**100, 2, 20) == stable_residue(10, 20)
assert local_lambert_residue(6, 2, 9) == stable_residue(6, 9) % 512
```

The modular evaluators validate their parameters. Their proved domain is
even q >= 4; the excluded q = 2 corresponds to the trivial constant base-1
tower. `capped_hyper` has the separate domain a >= 3. Factorization is used
only by diagnostic/verification helpers, not by the production tetration or
higher-arrow evaluators.

## Verification

The recorded suite passes **62,649 exact assertions**. In addition, the
exhaustive fixed-point checks examine **51,414 candidate residue classes**.
Those candidates are not added to the assertion total.

The main grid covers every even q from 4 to 200, heights 0 through 10, gaps
1 through 3, and precisions through 10, in the combinations explicit in the
source and JSON report. Separate checks cover higher-arrow operations,
large ranks and the local Lambert formula. Every arithmetic comparison is
exact; elapsed-time measurement alone uses floating point.

The independent oracle uses Euler-totient recursion and a justified
large-exponent lift. It does not reuse the specialized fixed-modulus
iteration to generate its expected answers. The oracle is itself checked
against literal integer towers at manageable sizes. Finite tests validate
software and provide supporting evidence; they do not replace the proofs.

Running the verifier regenerates the four files in `data/`. Mathematical
outputs and assertion counts are deterministic; elapsed time is not.
The examples here and in the article were also run separately.

## Build the article

A TeX installation with pdfLaTeX, `latexmk`, the AMS packages, `newpx`,
`geometry`, `microtype`, `booktabs`, `enumitem`, `fancyhdr`, `tcolorbox`,
`listings`, `hyperref`, and `cleveref` is sufficient. These are common TeX Live
or MiKTeX packages. No external images or bibliography database are required.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `pdflatex article.tex` twice to resolve the table of
contents and references. The optional Makefile provides `make test`,
`make pdf` and `make clean`.
