# Three results from the Dirichlet GRH development

26 November 2026

Start with **jet_period.pdf** for a solution to the branch-period problem posed in ProveIt. Start with **zero_census.pdf** for the result about the zeros of the Riemann xi-function itself.

## Papers

| Manuscript | Result | Relation to earlier work |
| --- | --- | --- |
| `jet_period.pdf` | The least precision period for contact depth one is an explicit power of the residue characteristic. The largest correction occurs precisely at multiples of that period. At arbitrary depth a bounded finite calculation gives the least eventual period. Two mixed profiles have periods 32 and 64. | ProveIt already determines sharp jet cutoffs, proves eventual periodicity and gives a fixed-ring recurrence. Its question about the least period motivates the exact formula. |
| `prime_sampling.pdf` | The squared relative mesh gap characterizes universal one-sided interpolation at a prescribed admissible error rate. Every failing mesh admits a binary counterexample of any specified density between zero and one. | Fourth-power sampling and the reciprocal chord estimate are antecedents. The converse for arbitrary meshes with bounded unit masses and fixed density is the extension. |
| `zero_census.pdf` | From the Taylor coefficients of a logarithmic derivative at one center, signed eigenvalue counts recover the real zeros and conjugate pairs inside a disk. A one-coefficient modification additionally recovers the locations and multiplicities of all boundary zeros. | The proof uses classical logarithmic-derivative moments and finite-set Hermite inertia. The high-order shift and dimension growth distinguish interior and boundary contributions without computing contour moments on the boundary of the disk in question. |

The local algebra and spectral theorems hold independently of GRH. The sampling paper uses the identified one-sided zero criterion in the Lean development for its Dirichlet application. The manuscripts give mathematical proofs. The Python runs check examples, including exact arithmetic and an explicitly identified floating-point illustration. The new theorems have no Lean formalizations in this packet. Historical priority beyond the comparisons cited in the papers remains undetermined.

## Source map

1. The [readable Sernau edition](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh) states RH and GRH for Dirichlet L-functions. Its [reading guide](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/GUIDE.md) identifies the comparison of upper and lower bounds for lattice covolumes and the ensuing one-sided prime remainder. [Andrew Sutherland's checks](https://math.mit.edu/~drew/shortgrh/) cover both released editions. We inspected sources and used the published checks of that development.
2. The [ProveIt inventory](https://github.com/VladimirReshetnikov/ProveIt/blob/b9a7c196e4aed3d93d4f222efef677a50efe912b/Analysis/GeneralizedRiemannHypothesis/README.md) lists 61 archived packets and describes their review status. The particular [open period question](https://github.com/VladimirReshetnikov/ProveIt/blob/b9a7c196e4aed3d93d4f222efef677a50efe912b/Analysis/GeneralizedRiemannHypothesis/Research/grh_transfers_lubin_tate_and_graph_towers/discussion.tex), [finite-ring recurrence](https://github.com/VladimirReshetnikov/ProveIt/blob/b9a7c196e4aed3d93d4f222efef677a50efe912b/Analysis/GeneralizedRiemannHypothesis/Research/grh_prime_patterns_and_branch_precision/periodicity.tex) and [prior sparse sampling theorem](https://github.com/VladimirReshetnikov/ProveIt/blob/b9a7c196e4aed3d93d4f222efef677a50efe912b/Analysis/GeneralizedRiemannHypothesis/Research/grh_method_transfers_2026-11-25/report/sparse_sampling.tex) give the closest comparisons.
3. The [Riemann hypothesis article](https://en.wikipedia.org/wiki/Riemann_hypothesis) gives the critical-line formulation, the account of Alpöge's proof, and context on zero locations. The spectral paper applies its local theorem to the critical-line coordinate of the completed function. The closest technical comparisons are [Kytmanov and Khodos](https://doi.org/10.1007/s11785-016-0606-8) and [Deng, Yang and Lü](https://arxiv.org/abs/2608.11520).

## Reproduction

In a standard TeX Live installation with Latin Modern and the usual AMS and LaTeX extra packages, run from this directory:

```sh
latexmk -pdf jet_period.tex
latexmk -pdf prime_sampling.tex
latexmk -pdf zero_census.tex
```

Keep `mixed_period.tex` beside `jet_period.tex`. The former is a section included in the latter.

```sh
python3 checks/jet_period.py
python3 checks/mixed_period.py
python3 checks/prime_sampling.py
python3 checks/zero_census.py
python3 checks/xi_example.py
```

The first four scripts use the Python standard library. The last uses mpmath 1.3.0. Recorded outputs have the same stems with the extension `.txt`. The Xi example takes no zero ordinates as input. It estimates coefficients by two trapezoidal Cauchy quadratures on the circle of radius 10 and tests disks of radii 12, 18 and 24. It illustrates the asymptotic theorem in finite precision. The polynomial example verifies its finite threshold counts by exact rational arithmetic.

Run `sha256sum -c SHA256SUMS` to verify the contents of the extracted directory.
