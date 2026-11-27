# Source audit for the new rectangular symplectic extension

## Snapshot and scope

The inspected ProveIt snapshot is commit `497c1844e71393df41914f5b783d5dc9a618eb61`, dated 27 November 2026. The main research source is `Analysis/GeneralizedRiemannHypothesis/Article/`. Its README describes a 770-page merge of 142 delivered reports and counts 997 theorem/proposition/corollary/lemma statements. It records 619 unconditional marks, 291 Dirichlet-GRH marks and 43 reduction marks; these status counts are not a partition, because some lemmas and corollaries are unmarked. The README explicitly describes the article as a merge rather than an independent mathematical review.

The source theorem in `Article/sections/src.tex`, label `src:thm:dgrh`, is RH and GRH for Dirichlet L-functions over Q, for every positive modulus and every primitive or imprimitive Dirichlet character. Zeros in the open critical strip have real part 1/2. The half-plane nonvanishing statement excludes the principal pole at 1. It says nothing about multiplicity, or about general Artin, Hecke over nonrational fields, nonabelian Dedekind, or automorphic L-functions. All statements of a nonabelian RH in the article are reductions unless separately proved by an allowed input.

I directly read the vendored `src/Main.lean` and `src/Statements.lean`. `Statements.lean` imports Mathlib and states exactly these conventional objects; `Main.lean` exports the five named theorems listed by the project. This inspection establishes the statement and documented scope. It is not a local rebuild of their transitive proofs.

## Build status and external checks

The vendor is the readable edition of `lsernau/grh-lean`, pinned to `72fead102f663d5c7a407964a13dc0cf9d977207`, with Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. It is a separate Lake package. A build of ProveIt's root package, which uses Lean 4.32.0, does not check the vendor. Its import README says the files were copied without an import-time build.

The primary independent-check page at <https://math.mit.edu/~drew/shortgrh/> was accessed live during this task (page updated 27 November 2026 at 17:27 UTC). Andrew Sutherland reports successful builds, kernel replays of all modules, axiom checks restricted to `propext`, `Classical.choice`, and `Quot.sound`, independent theorem-export comparisons, and acceptance by nanoda, con-leche and con-ron for both editions at the exact pinned revision. The page reports `lake comparator --paranoid` success for both editions. A second readable-edition run was stopped for memory use and has no verdict; the larger-machine run succeeded. These are reported independent checks, not checks rerun in this task. The page also records an independently checked equivalence with Schoenfeld's explicit psi bound and an end-to-end derivation from the compact RH proof. These checks substantiate the documented Dirichlet-GRH input at the pinned revision.

The current `Lean/README.md` records actual further formalization, more recent than the article README's general warning: several singular-moduli support, determinant, p-adic root-count, and integer progression-free statements are covered by `GRHArticle`. It explicitly leaves the full five-term singular-moduli classification's CM reductions/certificates and the build connection for future Dirichlet-GRH applications open. No existing entry covers the new rectangular random-matrix theorem proposed here.

## Mathematical mechanism relevant to the extension

`src:sec:mechanism` describes comparison of upper and lower covolume bounds on one lattice, a second-moment spanning step, controlled torsion twists, and a one-sided analytic detector for zeros. The symplectic part of the merged article abstracts the spanning and frame statistics into finite-field matrix questions. These are unconditional consequences of finite linear algebra and do not depend on RH or GRH.

The precise source for the proposed extension is `Article/sections/spn.tex`:

- `spn:thm:complete-law`: exact pointwise law for arbitrary symplectic compressions.
- `spn:eq:E-count` and `spn:lem:gram-frames`: the number of isometric embeddings of a d-dimensional alternating space of rank 2s into a 2n-dimensional symplectic space.
- `spn:thm:balanced`: for complementary nondegenerate source and target frames, the residual form's singularity is the exact optimal distinguishing event. The full distance equals a product constant times the iid probability that the residual form is nonsingular.
- `spn:thm:nondeg-blind`: when both frame dimensions grow and the target-minus-source dimension tends to infinity, the rank discrepancy vanishes and the full discrepancy tends to the positive constant Delta_q.
- `spn:thm:square-block`: the equal-dimension case, with sharp first-order expansions of rank and full-matrix distances.
- `spn:thm:defect-universality`: the square translated quadratic residual has the nullity law of a uniform alternating matrix to first order.
- `spn:lem:block-moments`, `spn:eq:unified-moments`, and `spn:lem:interpolation`: the moment method used for that square result.
- `spn:q:symplectic`: explicitly asks for the complementary nondegenerate regime where a-b is fixed and positive, stating that only a lower bound was then available. It also asks more broadly about simultaneous growth of frame dimensions/radicals/complement dimensions.

A theorem covering all positive even rectangular dimensions, including a-b fixed and positive and uniformly varying aspect ratio, therefore answers an explicit inspected source question. It must distinguish its exact finite counting identities (which follow from the source framework) from any new uniform limiting analysis and sharp expansions. The article itself names classical antecedents for rank laws, pairs of alternating forms, and nondegenerate subspace counts; global priority cannot be certified by comparison with this repository alone.

## Reproducible source URLs

- <https://github.com/VladimirReshetnikov/ProveIt/blob/497c1844e71393df41914f5b783d5dc9a618eb61/Analysis/GeneralizedRiemannHypothesis/Article/README.md>
- <https://github.com/VladimirReshetnikov/ProveIt/blob/497c1844e71393df41914f5b783d5dc9a618eb61/Analysis/GeneralizedRiemannHypothesis/Article/sections/src.tex>
- <https://github.com/VladimirReshetnikov/ProveIt/blob/497c1844e71393df41914f5b783d5dc9a618eb61/Analysis/GeneralizedRiemannHypothesis/Article/sections/spn.tex>
- <https://github.com/VladimirReshetnikov/ProveIt/blob/497c1844e71393df41914f5b783d5dc9a618eb61/Analysis/GeneralizedRiemannHypothesis/Lean/README.md>
- <https://github.com/VladimirReshetnikov/ProveIt/blob/497c1844e71393df41914f5b783d5dc9a618eb61/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/src/Statements.lean>
- <https://github.com/VladimirReshetnikov/ProveIt/blob/497c1844e71393df41914f5b783d5dc9a618eb61/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/src/Main.lean>
- <https://math.mit.edu/~drew/shortgrh/>

## Audit limits

The inspected local article sections are a source snapshot, not independently verified wholesale. The source statement and independent-check report have been read; no full upstream Lean build or kernel replay was run here. New finite-field formulas were checked independently by exhaustive enumeration in `code/exhaustive_check.py`; the new proof was also checked by separate derivations of its moments, constants, and uniform error estimates. A finite check is evidence against implementation mistakes, not a substitute for the general proof.
