# Source audit and attribution boundary

Prepared October 2, 2026. This is a targeted source review, not an exhaustive
bibliographic novelty certification. The new mathematical proofs and code are
contained in this package. No source paper or external font is redistributed.

## Pinned ProveIt context

Inspected snapshot: `e58b724c25bd34533b7a5834cfcbe873dfa01288`.

1. `Computability/HilbertTenthProblem/README.md` (opening 200 lines).
   https://github.com/VladimirReshetnikov/ProveIt/blob/e58b724c25bd34533b7a5834cfcbe873dfa01288/Computability/HilbertTenthProblem/README.md
   Used to identify the maintained universal-polynomial compiler program and
   to avoid confusing allocation counts with the reported 87-operation bound.
   No independent rebuild or audit of that bound was performed here.

2. `Computability/HilbertTenthProblem/Lean/MRDP.md` (proof-interface guide).
   https://github.com/VladimirReshetnikov/ProveIt/blob/e58b724c25bd34533b7a5834cfcbe873dfa01288/Computability/HilbertTenthProblem/Lean/MRDP.md
   Documents the natural-witness `Diophantine.mrdp` existence interface and its
   distinction from numerical bounds and specialized compiler obligations.
   The present paper invokes classical MRDP for a corollary; it does not run
   this Lean build or claim formal verification of the new sandpile theorems.

3. `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/12-rle-routing-SOURCES.md`.
   https://github.com/VladimirReshetnikov/ProveIt/blob/e58b724c25bd34533b7a5834cfcbe873dfa01288/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/12-rle-routing-SOURCES.md
   Used to locate the related rotor-routing work and its explicit distinction
   between finite periodic rotors and universal infinite sandpile backgrounds.

A repository code search for `sandpile` returned these routing references.
The article does not claim that this limited search proves the absence of all
related mathematics elsewhere in the repository or the literature.

## Primary literature

4. Deepak Dhar, *The Abelian Sandpile and Related Models*,
   arXiv:cond-mat/9808047v2 (1998).
   https://arxiv.org/abs/cond-mat/9808047
   Full HTML inspected, particularly Section 2. Classical source for the burning
   algorithm, forbidden subconfigurations, and the caveat about nonsymmetric
   toppling matrices. The paper's recurrence criterion is not being claimed
   as a discovery here; the report proves the needed fired-support statement
   and builds a canonical arithmetic compiler around it.

5. Hannah Cairns, *Some halting problems for abelian sandpiles are undecidable
   in dimension three*, arXiv:1508.00161v2 (2021; original version 2015).
   https://arxiv.org/abs/1508.00161
   Full HTML inspected; relevant PDF pages 25–26 were also visually inspected.
   Central dependency: Section 6, Theorem 3, which reduces Turing halting to
   finite total activity for periodic-plus-finite sandpiles in dimension three.
   The stable circuit background and finite added inputs are described in the
   gate and simulation construction. The current package does not instantiate
   the entire universal machine construction.
   Additional source locations: Section 2.5 (planar questions), end of Section 7
   (the complexity question for local infinite activity), Appendix A (abelianity
   and least action). Source-raised questions are not advertised as having a
   verified unchanged worldwide status in October 2026.

## Contribution status

- Proved here: the stated support-burning equivalence, canonical rank lemma,
  unique natural-helper compiler, exact arity/residual counts, halo theorem,
  fixed finite-deviation field normal form, and the stated height/support
  consequences, with external dependencies identified above.
- Constructed here: coefficient-level Python compiler, normalized field
  verifier, expanded sample quartic, concrete example witnesses and tests.
- Not established: literature priority, optimal counts, fixed-arity ordinary
  single-fold polynomial compression, directed sandpile generality, a new
  universality theorem, a solution to the planar or local-complexity questions,
  or Lean certification of the new proofs.
- The Python tests are exact finite checks. They are not a proof by exhaustion
  of arbitrary graphs, unlimited ranks, infinite field supports, or universality.
