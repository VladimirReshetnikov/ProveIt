# Exact residue transport for sparse p-adic roots

Research supplement prepared for ProveIt, 27 November 2026.

## Contents

- `paper.tex` — complete LaTeX research manuscript, with proofs and references.
- `paper.pdf` — compiled 11-page manuscript.
- `verify.py` — exact-arithmetic fixed-support optimizer, exhaustive universal optimizer, and witness generator/checker.
- `certificates.json` — all computed examples, including integer polynomial coefficients (encoded as decimal strings), rational depths, and root-count certificates.
- `verification.log` — successful run of the verifier.
- `PROVENANCE.md` — repository source identifiers and scope of review.
- `requirements.txt` — dependency for the squarefreeness checks.
- `SHA256SUMS` — archive-file checksums.

## Reproduce

Use a standard TeX Live distribution with AMS packages, Latin Modern, microtype, and hyperref:

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

With Python 3.10 or newer:

```sh
python -m pip install -r requirements.txt
python verify.py --output reproduced.json
```

The default run exhaustively checks 15 parameter pairs, generates and checks 21 squarefree witnesses, and performs 72 residue-invariance comparisons. All arithmetic is exact. Example single computations:

```sh
python verify.py --universal 2 9
python verify.py --support 3 0 1 3 4 6 9 12
python verify.py --support 3 0 1 3 4 6 9 12 --depth 51/100
sha256sum -c SHA256SUMS
```

The full theorem proofs do not depend on computation. These checks are not a Lean formalization. The algorithms take a prime p and distinct nonnegative integer exponents as inputs; prime validity is a precondition. Exhaustive residue-multiset enumeration can be expensive.

## Scope

The paper solves finite sharp determination in the sense of the repository's `smd:q:roots` question for arbitrary support sizes and deeper disks, and establishes the sharp formula for `p+2 <= t <= 2p+1`. It does not claim closed formulas in all larger ranges, priority worldwide, or a resolution of nonabelian GRH or Artin holomorphy. The new theorems are unconditional.
