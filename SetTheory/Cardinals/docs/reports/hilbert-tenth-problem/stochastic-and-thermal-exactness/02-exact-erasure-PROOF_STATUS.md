# Proof status and scope

Date: October 2, 2026. Author of this development and implementation: ChatGPT.
Prepared for Vladimir Reshetnikov.

## Claims proved in the article

1. The positive affine lift is given by explicit integer numerator formulas, with
   strict entrywise positivity, common column sums, affine block identities, and
   deterministic total-variation contraction proved directly.
2. The two-guard compiler has no common invariant complex line. The proof treats
   lines in the zero-mass hyperplane and lines outside it separately. Every word
   has rank 1+2 times the rank of its source projection. Arbitrary interleaving of
   guards is covered; source-only or handpicked words are not the only case.
3. The four-dimensional PCP frontend is proved for every word, including adjacent
   idempotent connectors and empty component strings. It has no empty-word
   false-positive. Its nine-state stochastic consequence is many-one complete
   conditional only on the cited classical PCP/halting interface.
4. The higher tensor compiler excludes common invariant subspaces of dimensions
   1,...,r-1, via an explicit matrix-unit algebra argument.
5. Commuting induced matrices have a sharp n-1 exact-erasure horizon, proved by an
   invariant-image rank descent. The affine generators themselves need not commute.
6. Independent full-support switching admits an erasing word iff exact forgetting
   is almost sure iff its expected time is finite. A geometric block argument
   proves the explicit tail bound. This is a special absorbing-word phenomenon,
   not a classification of arbitrary almost-sure termination.
7. Full-prefix and mass-compressed numerical quartics have word-bijective natural
   zero sets and the stated witness/residual counts. Their projection is a
   zero-set bijection, not an off-zero polynomial identity. Natural selectors,
   not arbitrary signed or rational selectors, are required.
8. The uniform-input compressed schema is a polynomial of total degree <=4,
   including input parameters. Its extra selected-restriction and clock variables
   are explicitly counted. The input validity promises are separately identified.
9. Invertibilizing perturbations preserve every common invariant subspace and
   give arbitrarily close non-erasing positive stochastic alphabets.

## External mathematical dependencies

- Cassaigne, Halava, Harju, Nicolas, arXiv:1404.0644v3: the adopted mortality
  undecidability bounds (3,6), (5,4), (9,3), (15,2). Their paper defines general
  reductions by oracle Turing machines. Only undecidability, not an unverified
  many-one completeness strengthening of the small bounds, is imported.
- Classical many-one completeness of PCP; a primary formal-reduction source is
  Forster, Heiter, Smolka, arXiv:1711.07023v2. The halting-to-PCP reduction is not
  re-proved or implemented in this package. PCP-to-mortality and all later maps
  are printed and implemented here.
- DPRM: computably enumerable predicates have natural Diophantine representations.
  The fixed-arity quartic consequence uses standard circuit quadratization,
  proved in the article, but supplies no numerical universal witness/operation count.

## Verification actually performed

- 50,582 passing finite exact-arithmetic assertions, with category counts and
  deterministic sample seed recorded in `verification/check_results.json`.
- The certificate evaluator imports no generator module. This is implementation
  separation, not a claim of independent authorship or independent peer review.
- Both numerical quartic forms are executed. The uniform-input-parameter schema
  has a hand proof, not a separately implemented symbolic compiler in this package.
- The final PDF was compiled, rendered, and inspected; its receipt is in
  `verification/pdf_preflight.json`.
- No Lean/Rocq theorem was authored or compiled. No existing repository proof
  assistant development was rebuilt. No outside peer review was obtained.

## Novelty and limits

The explicit no-common-line tensor-guard compiler is presented as the proposed
research contribution. It answers the precise no-common-invariant-line
restriction raised in MathOverflow question 511960. A targeted literature and
repository search is not a certification of worldwide priority. The basic
stochastic lift, DPRM consequence, and general contrast between contraction and
exactness are not advertised as new foundational principles.

A common invariant hyperplane remains. The matrices are NOT asserted to form an
irreducible family. The labelled hidden-state example has iid outputs and an
explicit output entropy rate; it does NOT prove entropy undecidability. The
seven-state result concerns a parameterized family of alphabets, not one printed
fixed universal alphabet. The nine-state completeness result allows variable
alphabet size.

The bounded quartics vary in arity with T. Uniqueness per bounded labelled word
does NOT settle a finite-fold representation conjecture for arbitrary enumerable
sets. Fixed-arity DPRM witness multiplicities remain uncontrolled. No universal
87-operation record is improved. No optimality of the bounded certificate counts
or of the dimension/alphabet tradeoffs is claimed.
