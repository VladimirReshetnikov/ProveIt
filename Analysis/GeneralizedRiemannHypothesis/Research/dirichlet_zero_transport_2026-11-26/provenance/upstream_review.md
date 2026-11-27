# Source audit: lsernau/grh-lean

Audit date in user timezone: 2026-11-26.

## Pinned source and scope

Repository: https://github.com/lsernau/grh-lean

Pinned commit: 72fead102f663d5c7a407964a13dc0cf9d977207, authored 2026-11-25T20:38:07Z; commit message "Lean proof of GRH". The returned commit has no parents. Git tree: 5eb1240f03e791edd3fc7aa84a3a7d8dc3997b7f. Recursive tree was not truncated: 1950 entries. Compact edition contains 794 source Lean files (573 Lib, 219 New, Statements, Main); readable edition has 803 source Lean files.

Canonical source prefix:
https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/

The scope is **RH and GRH for Dirichlet L-functions**, all positive moduli and all Dirichlet characters, including imprimitive characters. It is not a statement of GRH for arbitrary automorphic, Artin, or number-field L-functions. This is explicit in grh-compact/src/Statements.lean and grh-compact/src/Main.lean.

The four named statement definitions in Statements import only Mathlib:
- RiemannZetaZerosOnLine: excludes the negative even integers and the pole s=1.
- DirichletLNonvanishingRightOfHalf: Re(s)>1/2, with the principal-character pole excluded.
- DirichletLZerosOnLine: all zeros in 0<Re(s)<1 have Re(s)=1/2.
- PrimitiveDirichletLZerosOnLine: the primitive special case.
Main additionally proves Mathlib's RiemannHypothesis.

## Verification evidence and its limits

README reports:
- All source files compile under Lean 4.35.0 and Mathlib commit 56a005855ea17e0b0958f73ec801ae140b0a1679.
- Each of the five main theorems depends only on propext, Classical.choice, Quot.sound.
- Kernel replay and Comparator v4.35.0 accepted the proofs.
- No mathematician has read the proof through; no accompanying paper.
- Build needs roughly one to two hours on 12 cores and 24 GB RAM; Comparator about 64 GB and several hours.

I inspected the pinned source and the declared checks. I did **not** replay this complete build, inspect all 794 compact source files, or run Comparator. Consequently, report these as repository-provided verification evidence, not a fresh independent machine certification.

The tree has no .github workflow files or obvious committed audit/build logs. scripts/PrintAxioms.lean prints the five axiom dependencies. comparator.json permits exactly the three axioms above and sets enable_nanoda=true.

Challenge.lean contains five intentional sorry placeholders. README and Lake configuration explain that it is the independent statement challenge for Comparator, not imported into the proof and not a default build target. Finding those placeholders alone is not a defect in the main proofs.

## Mathematical mechanism

The source is not a newly constructed self-adjoint spectral operator for zeta. Its decisive argument is a comparison of **the same arithmetic covolume** from above and below, combining theta lifts, integrality, heights, and the product formula.

Notation in New/Main:
- D = dimension of the target row space.
- m ≈ sqrt(x), number of successive theta lifts.
- H = mainHeight = m*k*dirCost.
- R = remainder, a weighted prime-counting error.
- B = budget = f*a*(log b)^3.
- L = (log b)*B = f*a*(log b)^4.

Three input theorems:
1. **Short forms**, Endgame/ShortAndEnough.lean, lines 134–168: a rational normalization gives forms whose squared lifted norm is at most exp(H-mR+L), with controlled integral index.
2. **Enough forms**, same file, lines 170–178: a bounded number of translates span dimension n≥(1-4/b²)D. The number of translates times the source dimension is at most 5D log(1+b²).
3. **Integral forms are long**, Endgame/LongForms.lean, lines 60–71: if such a family has squared covolume ≤exp(V) at every complex embedding and logarithmic index ≤δ, then D(H-3L)≤V+2δ. Twisted ratios of volumes have height bounds whose product is 1; nonnegativity for the height of 1 is the product-formula step.

Endgame/LongForms.lean, lines 75–92, packages A and B:
n≥(1-4/b²)D,
δ≤5D log(1+b²)B,
V=n(H-mR+L).

New/Main.lean, lines 117–145, bounds the loss from missing dimensions and cancels H:
mR ≤ 4L + 4x^99 + 10 log(1+b²)B ≤ (log b)^2 B.

This explicitly quantifies where approximate spanning and index losses enter. The factor 1/m is the source of the square-root scale.

## Prime error and analytic bridge

Endgame/PrimeError.lean defines
λ_(d,M)(ν)=1_{ν≡1 mod M} Λ(ν)(1-(ν/d)),
and
R_(d,M)(x)=Σ_(ν≤x) λ_(d,M)(ν)(1/ν-1/x)
           - log(x)/φ(M) - Re(logDerivMean_(d,M)(1)).

The function is a smoothed weighted count of prime powers not split in Q(sqrt(-d)). PrimeError.lean proves the exact finite-sum rewrite used by divisibility and size estimates.

For d≡7 mod8 and gcd(d,M)=1, E(v)=R_(d,M)(exp v) satisfies IsPolar. IsPolar means measurability, E(v)=O(exp v), and a meromorphic continuation of
Φ(s)=∫_0^∞ E(v)exp((1-s)v)dv,
with no pole at Re(s)≥1 and specified simple-pole residues in Re(s)>0. The residues are differences of zero multiplicities of Dirichlet L-functions and their quadratic twists, divided by φ(M)s(1-s).

OneSidedCriterion.lean, lines 26–37:
A one-sided eventual bound R_(d,M)(x)≤x^(β-1), β>1/2, over a suitable prime family d gives a zero-free half-plane Re(s)>β. The proof uses a quadratic twist nonvanishing result and Landau's theorem.

OneSidedCriterion.lean, lines 69–99:
For polar E,E', for all sufficiently large t and every X∈[0,exp(t)], there is u∈[t,t²] with
E(u)-X E'(u)≤exp(-t).
This chooses the second scale in the arithmetic inequality. Its proof uses high gamma moments v^k exp(-3v), k≈t²/9, and the continuation-induced bound
|∫v^k exp(-3v)E(v)dv|≤k! t/R^k
for some R>3.

New/Main.lean, lines 147–190:
The arithmetic inequality and this good-window lemma give
R_(d,M)(x)≤x^(-1/2+8ε)
eventually, for every small ε>0. The one-sided criterion excludes zeros in Re(s)>1/2. The functional equation gives the critical-line statement, lines 192–204.

## Reusable ideas and possible extensions

Most reusable, with the fewest prerequisites:
- Defect-sensitive covolume sandwich: keep independent upper error, lower error, index loss, and missing-dimension loss rather than package them as a single slack monomial.
- Gamma-moment localization: analytic continuation past the Laplace abscissa gives a positive smoothing measure with exponentially small signed average.
- Simultaneous convex balancing: replace a scalar pair E-XE' by a fixed finite vector E_1,...,E_d. A positive truncated gamma average can make every coordinate exponentially small; Carathéodory gives at most d+1 shared scales.
- The source's [t,t²] window should improve to [t,Ct], with C depending explicitly on the continuation radius and the desired accuracy exponent. Choose moment degree k≈κt rather than t²/9, κ large enough to beat the transform and left-tail errors, and C large enough to beat the right-tail error. In original x variables this replaces [X, exp((log X)²)] by [X,X^C].

The last two directions appear substantively distinct from a spectral repackaging, but novelty must be compared with the user's existing ProveIt reports and literature on Landau oscillation / effective convex quadrature before any priority claim.

## Source archive

This directory contains verbatim pinned snapshots of the central files above, the root LICENSE and compact NOTICE. LICENSE and NOTICE should accompany any redistribution. These snapshots are a review subset, not a buildable copy of the repository. tree.json and head.json preserve retrieval metadata.

