# Nondegenerate symplectic blocks

Research prepared for Vladimir Reshetnikov, 27 November 2026.

The complete human-readable proof is `paper.pdf`, with source `paper.tex`.

## Main result

Let n be even. Take the n by n block along a nondegenerate half of a uniform
symplectic transformation of a 2n-dimensional space over F_q. Its entire rank
distribution approaches the independent-entry matrix rank distribution, with
sharp total variation `(c_infinity/(q-1)) q^(-n) + O_q(q^(-2n))`.
The full matrix distributions remain separated by
`Delta_q = o_infinity (1-e_infinity) > 0`. The exactly optimal distinguishing
test in every dimension is whether `J-M^T J M` is nonsingular.

Here `c_infinity=product(1-q^(-j))`, `e_infinity=product(1-q^(-2j))`, and
`o_infinity=product(1-q^(-(2j-1)))`. The paper gives the complete likelihood,
sharp signed rank-law expansion, and a companion sharp universality theorem
for the nullity of the quadratic alternating defect of an iid matrix.

This is an unconditional finite-method extension motivated by the supplied
GRH proof and ProveIt article. It does not require RH or GRH as an assumption.
The critical asymptotics, likelihood-sign theorem, and optimal statistical
test are the substantive extension; classical subspace counts and the earlier
general compression law are credited. Worldwide publication priority is
provisional. No new Lean formalization or upstream kernel replay is claimed.

## Contents

- `paper.tex`, `paper.pdf`: complete research note and proof.
- `code/exact_laws.py`: exact rational finite laws and numerical constants.
- `code/verify_exhaustive.py`: independent exhaustive finite-field checker.
- `code/check_cross_validation.py`: compare those two independent calculations.
- `code/make_figure.py`: reproduce the plot from exact calculations.
- `code/build_pdf.py`: offline PDF build, including a fallback for an installed
  TeX tree whose format and filename database are missing.
- `results/`: exact check reports, rational distributions, and numerical tables.
- `figures/`: vector PDF and PNG version of the scientific figure.
- `provenance/`: pinned source audits, literature comparison, and review scope.
- `formalization_plan.md`: proposed Lean dependency structure; not compiled.
- `MANIFEST.sha256`: checksums for all substantive archive files.

## Reproduce

From this directory:

```sh
python3 code/verify_exhaustive.py --output results/exhaustive.json
python3 code/exact_laws.py --max-n 24
python3 code/check_cross_validation.py
python3 code/make_figure.py
python3 code/build_pdf.py
```

The first three programs use only the Python standard library. The figure
requires Matplotlib; the PDF requires an installed TeX distribution with the
standard packages named in the source. The build script performs no network
requests. Ordinary `pdflatex paper.tex` run twice also works on a configured
TeX installation.

The exhaustive checker covers `(q,n)=(2,2),(2,4),(3,2),(4,2),(5,2)` and really
enumerates matrices. F_4 arithmetic uses F_2[x]/(x^2+x+1). The formula checks
cover 48 cases, all even n from 2 through 24 and q in {2,3,4,5}. Mathematical
proofs, not numerical experiments, establish the general results.
