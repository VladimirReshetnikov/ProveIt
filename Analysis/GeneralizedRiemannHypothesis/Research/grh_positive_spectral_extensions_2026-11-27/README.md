# Positive prime signals and optimal zero cancellation

Research package prepared for Vladimir Reshetnikov, 27 November 2026.

Start with `report.pdf`. Its complete editable source is `report.tex`,
`papers/*.tex`, and `references.bib`.

## Main mathematical results

1. **One real positive arithmetic weight determines every labelled Dirichlet zero spectrum.**
   Assuming the proved Dirichlet GRH input from the pinned upstream development,
   a computable weight W on positive integers, independent of zero data and as
   close to 1 as desired, makes one real autocorrelation determine every
   primitive character's nontrivial zero multiset, including the signs of
   ordinates and every multiplicity. A stated correction permits using actual
   primes alone. This answers the supplied Article's explicit real-weight
   question. It concerns exact limiting data, not finite-noise reconstruction.

2. **Optimal two-frequency cancellation and an asymmetric resonance law.**
   The paper gives a complete proof over all compactly supported probability
   measures, unique optimal weights, a sharp transport-stability exponent,
   and an exact first-order shortening coefficient. At every odd integer n>=3,
   the minimum width at r=n+epsilon is

   `pi + 4*(3*pi/(2*n*(n*n-1)))**(1/3)*epsilon**(1/3) + O(epsilon)`.

   The increase from the other side is linear. The positive two-mode
   optimization and its three/four-impulse patterns have classical engineering
   antecedents; they are credited. The resonance and shortening asymptotics
   are the proposed new refinement, not a claim to have invented input shaping.

## Sources and novelty

- `lsernau/grh-lean`: commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
- `VladimirReshetnikov/ProveIt`: commit `22e5c8b7dda558fd9a50b61465483cb4c0433694`,
  `Analysis/GeneralizedRiemannHypothesis/Article`.
- The positive code is credited to that Article. Irrational reflection has
  phase-retrieval antecedents in Liehr (2024) and Wellershoff (2024).
- Two-mode input-shaping antecedents include Crain, Singhose and Seering (1996)
  and Singhose, Crain and Seering (1997).

The packet contains complete human-readable proofs and a targeted literature
comparison. No worldwide-priority claim is certified by the search. No new
Lean proof is claimed. Separate review passes in this AI-assisted session
checked the arguments; this is not external peer review.

## Reproduce

Python 3.10+ is sufficient for the exact arithmetic check:

```bash
python3 scripts/real_weight_checks.py --output results/real_weight_checks.json
```

For numerical illustrations, install the packages in `requirements.txt`, then:

```bash
python3 scripts/filter_checks.py
```

This generates the JSON/CSV tables and the PDF/PNG figure. The first two zeta
zeros are numerical illustrations, not interval-certified enclosures.

Rebuild the paper with a standard TeX installation:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

Alternatively run `pdflatex report`, `bibtex report`, and `pdflatex report`
twice. A Makefile provides `make pdf`, `make checks`, and `make clean`.

## Contents

- `report.pdf`, `report.tex`, `papers/`, `references.bib`: full paper and sources.
- `scripts/`: reproducible exact and numerical checks.
- `results/`: recorded outputs, including 65 exact transport identities,
  13 recovered multiplicities, 364 lattice queries, 19 moment examples,
  10 paired linear programs and 28 resonance cases.
- `figures/`: generated phase diagram and convergence illustration.
- `verification/`: pinned source hashes and detailed proof-review notes.
- `SHA256SUMS`: integrity hashes for all other delivered files.

The original upstream repositories and complete third-party research papers
are not redistributed. The archive is self-contained for rebuilding the new
report and reproducing its examples.
