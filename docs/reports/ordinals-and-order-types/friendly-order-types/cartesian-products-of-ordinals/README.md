# Friendly Order Types of Finite Posets and Ordinal Products

Research report prepared for Vladimir Reshetnikov, 19 September 2026.

## Main results

Write f(P) for Vialard's friendly order type: the rank of the bad-sequence
subtree in which every selected point has an incomparable friend in the
current residual.

1. For every finite poset P, f(P) = |P| - c(P), where c(P) counts connected
   components of its incomparability graph, including isolated vertices.
2. A Cartesian product with at least two non-singleton factors has exactly
   one non-endpoint incomparability component; existing least and greatest
   points are the only other components.
3. No function of the four invariants (o,h,w,f) of each factor determines
   f(A x B) for general wpos. Explicit four-point factors D and E both
   have tuple (4,3,2,1), but f(D x 2) = 5 and f(E x 2) = 6.
4. Let P = alpha_1 x ... x alpha_r x B, with r >= 1, each alpha_i infinite,
   B finite nonempty, and r >= 2 or |B| >= 2. Its friendly order type is
   Theta = alpha_1 natural-product ... natural-product alpha_r
   natural-product |B|, except that it is the right predecessor of Theta
   when every alpha_i is a successor and B has a greatest element.
5. This gives a complete classification for finite Cartesian products of
   ordinals, including empty factors, singleton factors, and finite boxes.

## Status

The broad compositional computation of friendly order type is identified as
an open research direction in Vialard's MFCS 2023 paper and 2024 thesis.
The exact restricted questions in this report are our formulations within
that direction. The both-limit product case and binary ordinal-sum formula
were already known and are not claimed as new.

Conventional proofs are supplied. The transfinite theorem explicitly uses
published maximal-linearization/natural-product results and Vialard's
limit-saturation corollary. The exact new-to-this-report formulas were not
located in the checked sources, but publication priority has not been
certified. This is not a peer-reviewed paper or a Lean formalization.
It does not solve the unrestricted general compositional program.

## Contents

- `friendly_order_types.pdf`: compiled article.
- `friendly_order_types.tex`: self-contained LaTeX source with bibliography.
- `build.sh`: PDF build helper.
- `code/finite_posets.py`: validated finite-poset representation, direct
  residual-tree rank, graph formula, constructive certificates, products,
  height, width, and exhaustive naturally labelled enumeration.
- `code/ordinal_cnf.py`: exact hereditary Cantor normal forms below epsilon_0;
  ordinary addition, natural sum/product, predecessor, formula evaluators.
- `code/verify.py`: reproducible tests; Python standard library only.
- `data/verification_results.json`: scope and counts of completed checks.
- `data/counterexample_certificate.json`: exact relations, covers, invariants,
  incomparability components, moves, friends, and residuals.
- `data/ordinal_examples.json`: exact symbolic ordinal-box examples.
- `PROOF_DEPENDENCIES.md`: dependency map.
- `RESEARCH_STATUS.md`: literature, scope, and verification boundaries.

## Reproduce computations

Python 3.10+ is required. From this directory:

```sh
python3 code/verify.py
```

The command rewrites the three data files. It needs no network access,
Wolfram kernel, SageMath, or external Python packages. Explicit checks are
not disabled by Python's `-O` option.

Completed checks:

- 5,231 nonempty naturally labelled posets of sizes 1 through 6, and the
  empty poset separately; direct rank equals the component formula.
- 5,231 independently constructed optimal legal-sequence certificates.
- 2,401 ordered products of naturally labelled factors of sizes 2 to 4.
- The four-point-factor counterexample, including equal ordinary product
  invariants (8,4,3) and different friendly types 5 and 6.
- 387 finite-surrogate corner-strategy cases, including two no-move cases.
- 7,200 sampled ordinal-algebra identities and six worked box examples,
  plus finite arithmetic, predecessor, and degeneracy checks.

Naturally labelled enumeration is not enumeration of every relabelling
and is not an isomorphism quotient. Every isomorphism class through the
stated size has a representative in this enumeration.

## What the computations do not establish

The direct finite rank algorithm is independent of the component formula,
but testing finitely many inputs is not the general proof. Corner simulations
replace limit cutoffs by 2 and test only legal moves, witnesses, move counts,
and residuals. They do not verify transfinite rank. The ordinal evaluator
implements the proved formula; it is not an independent infinite-tree rank
oracle. Its notation system excludes epsilon_0 and omega_1, even though
the mathematical theorem permits arbitrary set-sized ordinals.

## Build the PDF

A standard TeX installation providing the packages in the preamble is
required, including New PX, amsmath, amsthm, mathtools, microtype, TikZ,
tcolorbox, listings, hyperref, and booktabs.

```sh
sh build.sh
```

Temporary LaTeX files are put in `.latex-build/`. The resulting PDF is
copied into this directory. No font files are included in the archive.
