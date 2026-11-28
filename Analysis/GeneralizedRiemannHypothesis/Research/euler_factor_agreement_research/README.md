# Euler-factor agreement: a conjecture counterexample and sharp cubic theorems

Prepared for Vladimir Reshetnikov, 27 November 2026.

## Read first

1. **rajan_counterexample.pdf / rajan_counterexample.tex** — a counterexample to Conjecture 3 in C. S. Rajan, *Proceedings of the American Mathematical Society* 128 (2000), 691–700, p. 698. It includes an infinite family and a sharp replacement in degree three, with a classification of all equality cases for arbitrary Hecke quasi-character triples over number fields.
2. **cubic_euler_agreement.pdf / cubic_euler_agreement.tex** — the exact 25/27 maximum for complete-factor agreement of inequivalent three-dimensional representations of a compact group, all equality cases, the sharp reducibility gap, quantitative stability, error/erasure bounds, an explicit Heisenberg Galois extension, and a sharp tempered cuspidal GL(3) theorem.

The two papers are self-contained apart from clearly cited standard results in representation theory, prime distribution, and automorphic forms. Neither relies on the truth of RH or GRH.

## Principal conclusions

- The independent cubic packets `{1, chi, chi^2}` and `{psi, psi chi, psi chi^2}` agree in their **complete** local factors at prime density **7/9**, above Rajan's proposed degree-three ceiling **3/4**. Explicit cubic characters modulo 7 and 13 work; the first distinguishing unramified prime is 29.
- An exact mixed cubic/quadratic family gives counterexamples in every degree `3*2^k <= n < 4*2^k`, for each nonnegative integer k.
- For distinct triples of arbitrary Hecke quasi-characters over a number field, **7/9 is the exact maximum agreement**. Equality occurs precisely for a common quasi-character twist of the independent cubic packets. The analogous compact-group theorem permits characters of arbitrary order.
- For any inequivalent continuous three-dimensional complex representations of a compact group, complete-factor disagreement has measure at least **2/27**. Equality forces irreducibility, equal determinants, and a common scalar kernel of index nine, with quotient `C3 x C3`.
- If at least one cubic representation is reducible, disagreement is at least **1/8**, and this bound is attained. For sums of three one-dimensional characters, the stronger bound is **2/9**.
- The bound **2/27** also holds for the lower Dirichlet density of full-factor disagreement between inequivalent unitary cuspidal GL(3) representations assumed tempered at all but finitely many unramified finite places. The bound is attained by cyclic automorphic induction of the explicit Heisenberg example.

## Source and novelty boundaries

The ProveIt source was pinned to commit `8528159d15e864e603ba4ded6ebb694c48cf160b` in `Analysis/GeneralizedRiemannHypothesis/`. The audit was targeted, not a review of every report or a fresh Lean build. The exact basic cubic packet already occurs in the repository's `Article/sections/rec.tex`, especially `rec:sec:omatch` and `rec:cor:ocubicmin`; it is credited there and in both papers.

The connection to Rajan's printed conjecture, the mixed-order family, the unrestricted cubic replacement and equality theorem, and the nonabelian complete-factor theorem are the contributions emphasized in this package. Targeted literature searches found no earlier statement of these exact results, but priority is **not certified**. The independent mathematical reviews included here are additional model-assisted checks, not external peer review or proof-assistant verification.

The counterexample resolves a named specialist conjecture as stated. It does not settle the general cuspidal refined strong-multiplicity-one conjecture, remove temperedness in the automorphic theorem, prove generalized Ramanujan, or independently certify the repository's RH/Dirichlet-GRH proofs.

## Exact verification

Run from any working directory:

```sh
python3 code/reproduce.py --checks-only
```

Python 3's standard library is sufficient. Three programs verify complementary finite assertions:

| Program | Exact verification |
| --- | --- |
| `code/verify_exact.py` | Both order-27 representations, all 1,458 representation-law products, full characteristic polynomials, character norms and orthogonality, trace/full-factor distinction, sharp error/erasure data, the reducible order-16 example, and the cubic modulo-91 packet. |
| `code/verify_field.py` | Radical identities over `Q(omega)`, 27 distinct automorphisms preserving all defining relations, commutator and order relations, and valuation residue data. The field-degree proof is written in the paper. |
| `code/verify_rajan_family.py` | Complete sixth-root multiplicity vectors for all 567 elements across k=0,...,5; all 72 reduced residue classes modulo 91; exact agreement counts and the smallest distinguishing prime. |

The general theorems and the infinite family are proved in the papers; finite verification is supplementary. JSON outputs are in `results/`.

## Rebuild the PDFs

```sh
python3 code/reproduce.py
```

This reruns all three checks and builds both papers with two pdfLaTeX passes. Required TeX packages are listed in their preambles: a standard LaTeX installation with AMS packages, Latin Modern, microtype, geometry, booktabs, tabularx, enumitem, fancyhdr, xcolor, graphicx, and hyperref suffices. The figure PDF is already included. To regenerate it, install NumPy and Matplotlib and run:

```sh
python3 code/reproduce.py --regenerate-figure
```

No network calls are made by the verification or build scripts. Compiled outputs can differ by TeX/font versions; the mathematical checks use exact integer or rational arithmetic.

## Archive contents

- Two manuscripts, with both `.tex` and `.pdf` files.
- Exact verification and reproduction scripts in `code/`.
- The trace-triangle mathematical figure in `figures/`.
- Machine-readable verification outputs and build reports in `results/`.
- Mathematical reviews, source audit, and a source manifest in `notes/`.
- `SHA256SUMS.txt` for the archived files. This manifest excludes itself and changes if you rebuild files.

The archive does not redistribute the source repository or the journal articles; pinned links and identifiers are supplied for independent inspection.
