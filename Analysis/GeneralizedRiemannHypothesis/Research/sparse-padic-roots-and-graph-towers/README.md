# Sparse p-adic polynomials and four-step graph towers

Two independent research papers extending the ProveIt GRH project at commit
`6d284fcf75bc3a91bb2e79ba7636f94724bff62c` (27 November 2026).

## Sparse polynomials

Open `fewnomial/paper.pdf` for the sharp maximum number of roots, counted
geometrically with multiplicity, in the open p-adic exponential disk. For a
fixed exponent support of at most p terms, the answer is computed from its
residue multiplicities. For a term budget through p+1 it has a triangular-number
formula. At the next term, p+2, the maximum is exactly p squared. Integer
polynomials attain the extrema with simple roots.

At p=11 the successive maxima for 12 and 13 terms are 33 and 121. For the
larger value a specific squarefree witness is

    (X^11-1)^11 - 11^11*(X^11-1-11*(X-1)) + 11^14.

The verification program checks its open-disk Newton polygon and certifies
simplicity by reduction modulo an auxiliary prime.

## Graph towers

Open `graph/paper.pdf` for a coefficient formula counting every rank-two
row space with each spanning-tree valuation in a four-step Cayley tower,
for every prime p>8 and all tower levels. The only non-elementary counting
inputs are the Frobenius traces of two explicit elliptic curves. The paper
gives their rational quotient maps, a congruence modulo 192, the
Sato–Tate fluctuation law for the middle isotropic class, and first and
second moments for all ranks from one to four.

## Reproduction

Each directory contains the complete LaTeX source, its compiled six-page PDF,
a Python standard-library checker, and the checker's saved output. In either
directory, run the following commands with Python 3.9 or newer and a standard
TeX Live installation.

    python3 verify.py
    pdflatex paper.tex
    pdflatex paper.tex

The graph checker includes a direct enumeration of 136,366 row spaces and
direct point counts at every prime from 5 through 199. The sparse-polynomial
checker includes 3,934 multiplicity partitions, 1,274 residue-jet rank
comparisons and 85 witness polynomials. Both outputs can be reproduced
without network access.

## Provenance and scope

The local root-count papers and the graph-tower section cited in the papers
are the mathematical starting points. The repository's vendored Dirichlet
GRH development is pinned separately at `72fead102f663d5c7a407964a13dc0cf9d977207`.
Neither paper needs RH or GRH as a hypothesis. Both contain mathematical
proofs and finite verification code. The package supplies no Lean
formalization. The papers document the closest work identified and leave
global publication priority open.

[ProveIt project snapshot](https://github.com/VladimirReshetnikov/ProveIt/tree/6d284fcf75bc3a91bb2e79ba7636f94724bff62c/Analysis/GeneralizedRiemannHypothesis)
