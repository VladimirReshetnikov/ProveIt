# Uniform rank and joint-defect laws for rectangular symplectic blocks

**Research note, 27 November 2026.** The complete mathematical deliverable is
in **paper.pdf**; its editable source is **paper.tex** and **sections/**.

## Result and scope

Let q be a prime power, and let a ≥ b ≥ 2 be even. Let A be the a-by-b
off-diagonal block of a uniform symplectic transformation on complementary
nondegenerate spaces of dimensions a and b. Compare it with a uniform
independent-entry a-by-b matrix U.

The paper proves signed rank, translated-Gram-nullity, and centered joint-law
expansions with errors O_q(q^(-a-b)), uniformly over the gap d = a-b. In
particular,

    TV(rank A, rank U)
      = gamma_infinity / ((q-1) gamma_d) * q^(-a) + O_q(q^(-a-b)).

For K = nullity(U) and L = nullity(J_b - U^T J_a U), the distance between
their joint law and the product of their actual finite marginals is

    TV(Law(K,L), Law(K) x Law(L))
      = 2 q theta_infinity gamma_infinity / ((q-1) gamma_d)
        * q^(-a) + O_q(q^(-a-b)).

The paper gives the complete signed correction, not only these distances.
The event that exactly one of U and its translated Gram form is full rank
captures the entire leading dependence.

Meanwhile the full matrix laws stay apart:
TV(A,U) tends to theta_infinity (1 - eta_infinity) as both dimensions grow.
All notation and hypotheses are defined in the paper.

This resolves the fixed-positive-gap case for complementary nondegenerate
frames asked in the pinned ProveIt article. The main extension is the uniform
signed-law and joint analysis. The exact residual likelihood and optimal test
are inherited from the repository. A published classical complement count
already yields the scalar full-distance formula. See source_comparison.md
for the precise distinction.

The proofs are unconditional: they transfer the finite-field counting ideas
developed alongside GRH, and do not assume RH or GRH. They are mathematical
proofs, not a Lean formalization. A bounded literature review did not locate
these new uniform signed and joint expansions; worldwide priority has not
been certified.

## Contents

- paper.tex, sections/*.tex, paper.pdf: self-contained paper and full proofs.
- figures/: scientific figure in PDF and PNG.
- code/exact_laws.py: exact marginal laws and finite total variation distances.
- code/joint_laws.py: exact joint law and distance from independence.
- code/independent_enumeration.py: independent brute-force matrix enumeration.
- code/verify_independent.py: exact comparison of both approaches.
- code/make_figure.py: regenerates the figure from exact finite formulas.
- results/: rational certificates, numerical tables, and verification summaries.
- source_comparison.md: repository results versus the present extension.
- formalization_plan.md: verification boundary and suggested Lean stages.
- provenance.json: pinned source identities and public references.
- verification.md: checks performed and what they establish.
- SHA256SUMS: hashes of the included files, excluding itself.
- Makefile and requirements-plot.txt: reproducibility instructions.

## Reproduce the computations

Python 3.10 or later is sufficient for all exact computations. The four
verification programs use only the standard library. From this directory:

    python3 code/exact_laws.py
    python3 code/joint_laws.py
    python3 code/independent_enumeration.py
    python3 code/verify_independent.py

Or run:

    make verify

These commands regenerate results/. They use exact fractions and complete
small-case enumeration, with no random sampling. The supplied results are:

- 116 marginal parameter triples: all stated structural checks passed.
- 46 joint parameter triples: nonnegative mass, normalization and both marginals passed.
- Six independent matrix enumerations: all 98 marginal/distance and 76 joint
  equality checks passed.

Enumeration tests fields of orders 2 and 3. Formula evaluations also include
q = 4 and 5. They do not implement extension-field matrix arithmetic for q = 4;
the mathematical proof covers every prime power.

The exact rational checks verify finite examples and the implementation.
The all-dimensions theorem follows from the proof in the paper.

## Rebuild the PDF and figure

A conventional TeX Live installation with latexmk and the packages listed
in the preamble is sufficient. Run:

    latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex

The figure is already included, so rebuilding the PDF requires no Python
plotting package.

To regenerate the figure, install matplotlib (the supplied version is
recorded in requirements-plot.txt), then run:

    python3 code/make_figure.py

The exact computations are converted to floating point only when plotting.
The numerical tables contain decimal renderings of exact finite fractions.
Infinite-product constants have rational tail enclosures in
results/constant_enclosures.json.

## Source snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 497c1844e71393df41914f5b783d5dc9a618eb61
Directory: Analysis/GeneralizedRiemannHypothesis/

The principal comparison is Article/sections/spn.tex, especially the open
question spn:q:symplectic and the existing balanced, square-block,
nondeg-blind, and defect-universality results. Subsequent repository changes
are outside this comparison. The archive does not redistribute the complete
repository or its upstream Lean development.
