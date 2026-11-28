# Symplectic blocks at every congruence precision

`symplectic_precision.pdf` and its source `symplectic_precision.tex` prove that the first residue digit gives
an optimal test, with equal priors, for a Haar symplectic block against independent
Haar entries. This holds for every number of source pairs when the target's
orthogonal complement can contain the source. The paper gives an exact finite
formula for total variation and proves that higher digits can improve tests
with unequal priors.

The result is unconditional and uses the classical local-density formula of
Wakatsuki (2005), with precise normalization and citations in the paper.
No Lean formalization is claimed.

## Reproduce

From this directory:

```sh
python3 code/verify.py
pdflatex -interaction=nonstopmode -halt-on-error symplectic_precision.tex
pdflatex -interaction=nonstopmode -halt-on-error symplectic_precision.tex
```

The verification script requires Python 3 and NumPy. All mathematical comparisons
and probabilities are exact rational numbers; NumPy only enumerates integer arrays.
The script writes `results/verification.json` and checks 13 Gram parameter sets and
11 compression parameter sets, enumerating 1,863,252 Fourier characters and
407,106 observed blocks. These checks support the proof; they are not the proof.

The inspected repository commit is
`2e714ce3d8e33aa8160391cf5dd95f3af3c34045`.
