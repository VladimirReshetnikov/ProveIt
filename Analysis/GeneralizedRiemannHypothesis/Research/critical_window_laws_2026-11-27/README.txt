CRITICAL-WINDOW LAWS FOR QUADRATIC RELATIONS, CODE PRODUCTS,
AND HIDDEN SYMPLECTIC FORMS
27 November 2026

START HERE

Read critical_window_laws.pdf. The complete proof source is
critical_window_laws.tex, with its five section files under sections/.

MAIN RESULTS

1. A Fourier criterion makes the entire relation subspace of structured
   random constraints approach the kernel of a fully random matrix in
   total variation, at D+u samples for every fixed integer u.

2. The criterion applies to any space of homogeneous quadratics in n
   variables whose dimension D satisfies D/(n log D) -> infinity, over
   every fixed finite field, including characteristic two.

3. For random code factors of dimensions k and l with prescribed
   intersection dimension i, put D = kl - i(i-1)/2 and N = D+u.
   If D/((k+l-i)log D) -> infinity, then J = D-dim(C*C') has limiting law

       P(J=j) = g_infinity q^(-j(j+u)) / (g_j g_(j+u)),
       g_j = product_(r=1)^j (1-q^(-r)),  j >= max(0,-u).

   This provides the full bounded-offset asymptotic law in a stated
   regime of Randriambololona's published Problem 21. It includes
   prescribed overlaps uniformly, squares, systematic square generators,
   and the original random-generator formulation.

4. The entire corank pattern at any fixed set of distinct projective
   directions in a random space of alternating forms becomes independent.
   It yields the exact binomial-mixture law, full testing distance, and
   optimal recovery probability for the repository's hidden-form experiment.

STATUS

All theorem proofs in this note are unconditional; they do not use RH or
Dirichlet GRH. No new statement is asserted to have been Lean-formalized.
The paper does not claim to settle the full finite-parameter code-product
problem or a prominent general conjecture. The targeted literature check
supports proposed novelty of the precise refinements, not an exhaustive
worldwide-priority claim. The related recent unrestricted-matrix MRD result
is explicitly credited.

SOURCE SNAPSHOT

ProveIt commit b2c37bf49dd792be3258a0925c01725390b2b62f.
See PROVENANCE.json for exact source paths, Git blob hashes, and the scope
of the review. No repository files were modified by this task.

REPRODUCTION

Run from this directory:

  python3 code/verify_exact.py
  python3 code/compute_profiles.py
  python3 code/simulate_binary.py --trials 1500
  python3 code/make_figure.py
  latexmk -pdf -interaction=nonstopmode -halt-on-error critical_window_laws.tex

The first and third programs use only Python's standard library.
compute_profiles.py requires mpmath; make_figure.py requires matplotlib.
The numerical outputs and figure are included, so rebuilding the paper
requires only standard LaTeX packages, BibTeX, and latexmk.

WHAT THE CHECKS MEAN

results/exact_checks.json records 9,453 exact finite identity cases,
plus the indicated subsidiary checks. These checks passed, including
exhaustive alternating forms on four-dimensional spaces over F2, F3, F4.

results/profiles.json and profiles.csv contain 44 limiting inference
profiles for q=2,3,4,5 and offsets -5 through 5. Each saved decimal has
a certified absolute evaluation error at most 1e-45, using interval
arithmetic and explicit bounds on the infinite tails. This is an error
bound for the limiting formula, not a finite-size convergence rate.

results/binary_simulations.json contains 27,000 finite-model samples,
seed 20261127, with standard errors. They illustrate convergence and
do not prove the asymptotic theorems.

FORMALIZATION_NOTES.txt is a future formalization roadmap, not a proof
assistant output. SHA256SUMS.txt records all delivered file digests.

Suggested repository placement:
Analysis/GeneralizedRiemannHypothesis/Research/critical_window_laws_2026-11-27/
