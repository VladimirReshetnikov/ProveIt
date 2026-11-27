# Static source audit: the vendored GRH development

## Pinned material and verification boundary

- ProveIt commit inspected: `3d8689ceae76501a5c50f67da37e85369aac4fb6`.
- Vendored directory: `Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh`.
- The vendor README identifies the upstream snapshot as `lsernau/grh-lean`, commit `72fead102f663d5c7a407964a13dc0cf9d977207`, 25 November 2026.
- The Git tree contains 818 blobs totaling 30,396,423 bytes. The README says the import is byte-identical to that upstream tree; this audit independently read the tree but did not compare all 818 blobs against upstream.
- This audit inspected exact text of the theorem interfaces, main reduction, principal inequality, one-sided criterion, Landau argument, build configuration, and the finite positive-type and spanning interfaces. It did not execute Lean, replay exported proof terms, or inspect every transitive dependency.
- No Lean or Lake executable is installed in this workspace. Do not describe this as a new kernel verification.
- The vendor README explicitly says ProveIt's root Lake build does not include this separate package and that the import itself was neither built nor checked.
- The package pins Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Exact exported scope

`src/Statements.lean` imports only Mathlib and defines four propositions with Mathlib's zeta and Dirichlet L-functions. `src/Main.lean` exports:

1. `riemannHypothesis : RiemannHypothesis`.
2. `riemannZeta_eq_zero_re : RiemannZetaZerosOnLine`: a zero other than the negative even integers and the total-function point 1 has real part 1/2.
3. `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`: for every positive modulus, every Dirichlet character (including imprimitive), and Re(s)>1/2, the Dirichlet L-function is nonzero, excluding s=1 for the principal character.
4. `LFunction_eq_zero_re : DirichletLZerosOnLine`: zeros in 0<Re(s)<1 have real part 1/2, for all characters.
5. `LFunction_eq_zero_re_of_isPrimitive`: the primitive special case of item 4.

The names and the mathematical scope agree at the visible interface. In particular, the user-facing conclusions are not stated with internally redefined substitutes for Mathlib's L-functions.

The scope is Dirichlet GRH over Q. The declarations do not assert the general Hecke, Artin, nonabelian Dedekind, or automorphic versions of GRH. Nor do they assert simple zeros or nonvanishing at the central point. Additional Euler-factor zeros of imprimitive characters on Re(s)=0 lie outside the strip assertion.

## Axioms and holes: what was actually observed

The README reports that all five exports depend only on `propext`, `Classical.choice`, and `Quot.sound`, and reports independent exported-proof checking by nanoda, con-leche, and con-ron. `scripts/PrintAxioms.lean` imports `Main` and contains the five corresponding `#print axioms` commands. These reports were read, not reproduced.

The file `Challenge.lean` contains five intentional `sorry` placeholders. Its stated purpose is Comparator's target interface; it imports `Statements`, and nothing in the inspected proof path imports it. `lakefile.toml` has default targets `Lib`, `New`, and `Main`, not `Challenge`. Therefore the mere presence of these five placeholders is not evidence of a hole in the exported proof.

No axioms or proof placeholders occur in the inspected theorem-bearing files. This is a scoped static observation, not a statement about every dependency. Absence of text tokens alone would not substitute for printing axioms and replaying proof terms in any event.

## Proof architecture actually present in the sources

Let

`lambda_{d,q}(n) = Lambda(n) 1_{n=1 mod q} (1-chi_d(n))`,

and let `R_{d,q}(x)` be the ramp-smoothed sum of these nonnegative coefficients minus its logarithmic main term and normalizing constant. The arithmetic argument constructs admissible data depending on scales x, x1, b, with m in [sqrt(x),2 sqrt(x)].

`New.Reduction.MainInequality.star_inequality` compares a squared covolume plus twice an arithmetic index from two sides. The upper bound comes from short integral vectors and a second-moment spanning theorem; the lower bound comes from twisted determinant heights. Schematically, with target dimension D and selected independent family size n,

`D(main-3 loss) <= n(main-m rem+loss) + 2 D indexPerDim`.

Using n<=D, nonnegativity of main+loss, and n>=D/2 gives

`m rem <= f a (log b)^5`.

This is the exact statement of `star_inequality`; it is not just an informal description. The principal main terms cancel.

`New.Reduction.OneSidedBound` divides by the number of relevant places and uses an ordinary prime number theorem only at the much larger cutoff x1. It obtains an eventual upper bound `R_{d,q0}(x)<=x^(-1/2+epsilon)` for every epsilon>0, for q0 divisible by 18480 and auxiliary primes d in the prescribed congruence class.

`New.Reduction.Zeros.Criterion.LFunction_ne_zero_of_primeRemainder_le` chooses an auxiliary quadratic twist having no zeros in a finite rectangle to the right of beta>1/2. The residues of the Mellin/Laplace transform of the resulting remainder then encode the sum of untwisted zero multiplicities, divided by `phi(q0) s(1-s)`. At real points to the right of beta those residues have nonnegative real part. `New.IsPolar.landau` in `Lib/Analytic/Landau.lean` shows that the one-sided bound forces every residue to vanish in that half-plane. Each zero count is nonnegative, so every individual zero multiplicity vanishes.

`New.grh` induces an arbitrary modulus q to q0=18480q, applies the preceding argument, and removes the extra Euler factors using the product identity for change of level. `New/Main.lean` then obtains the critical-line statements by the functional equation, with the pole and gamma-factor cases handled explicitly.

## The finite-matrix bridge useful for a new theorem

The exact readable-source file is

`src/New/Spanning/SecondMoment/PositiveType.lean`.

It contains:

- `re_sum_addChar_dotProduct_mul_le`: an additive-character sum weighted by a positive-type function is bounded using the masses of stabilizers of a vector and a dual vector.
- `card_mul_sum_det_eq_zero_le`: for a nonnegative positive-type weight Theta on a finite group and two n-by-m frames, if every nonzero source vector's two stabilizers have Theta-mass at most Y, then the mass of singular m-by-m compressions is at most `(2 Theta(G)+q^(m+n/2)Y)/q`.

The proof expresses the character sum as an inner product of two orbit sums in a tensor-product Hilbert space. Orthogonality of additive characters and Cauchy-Schwarz give the bound; kernel counting converts it to singularity mass. These are unconditional finite statements.

This connects directly to the merged Article, section `spn`, whose positive-type subsection upgrades vector estimates to entire rectangular matrix laws. Its Lagrangian subsection derives a square projection likelihood, exposes the isotropic-kernel obstruction, and proves rank-only indistinguishability despite a persistent full-matrix total-variation distance. The final question `spn:q:symplectic` asks for growing-dimensional compression limits with arbitrary restricted forms.

A rectangular Lagrangian projection theorem, with a full aspect-ratio phase diagram, would be a genuine extension of the inspected square likelihood and growing-form results. It must be positioned as an unconditional transfer of the proof's finite-matrix ideas, not as a new consequence requiring Dirichlet GRH. Exact counts alone are already in the Article's complete-law theorem; novelty should lie in a new closed limiting law, sharp criterion, or information-theoretic separation beyond that exact count.

## Primary source links

All below use the ProveIt commit pinned above:

- Vendor status: https://github.com/VladimirReshetnikov/ProveIt/blob/3d8689ceae76501a5c50f67da37e85369aac4fb6/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/README.md
- Package README: https://github.com/VladimirReshetnikov/ProveIt/blob/3d8689ceae76501a5c50f67da37e85369aac4fb6/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/README.md
- Interface: https://github.com/VladimirReshetnikov/ProveIt/blob/3d8689ceae76501a5c50f67da37e85369aac4fb6/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/src/Statements.lean
- Main exports: https://github.com/VladimirReshetnikov/ProveIt/blob/3d8689ceae76501a5c50f67da37e85369aac4fb6/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/src/Main.lean
- Covolume inequality: https://github.com/VladimirReshetnikov/ProveIt/blob/3d8689ceae76501a5c50f67da37e85369aac4fb6/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/src/New/Reduction/MainInequality.lean
- Zero-free criterion: https://github.com/VladimirReshetnikov/ProveIt/blob/3d8689ceae76501a5c50f67da37e85369aac4fb6/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/src/New/Reduction/Zeros/Criterion.lean
- Finite positive-type estimate: https://github.com/VladimirReshetnikov/ProveIt/blob/3d8689ceae76501a5c50f67da37e85369aac4fb6/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/src/New/Spanning/SecondMoment/PositiveType.lean
- Article extension target: https://github.com/VladimirReshetnikov/ProveIt/blob/3d8689ceae76501a5c50f67da37e85369aac4fb6/Analysis/GeneralizedRiemannHypothesis/Article/sections/spn.tex
