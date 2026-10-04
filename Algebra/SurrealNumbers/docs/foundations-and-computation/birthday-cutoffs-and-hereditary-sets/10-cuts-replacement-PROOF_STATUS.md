# Proof and provenance status

## Proven in the manuscript by explicit mathematical arguments

1. A bounded-container construction of the simplest interpolant of an actual
   set cut over Zermelo set theory with Foundation, without Replacement.
2. Equivalence of six definable-family schemes with ordinal bounding over
   that base, including strict upper bounding inside (-1,0).
3. Equivalence with full Replacement and Collection only after adding the
   stated cumulative-hierarchy existence and coverage axiom H.
4. An explicit omitted definable cut in V_(omega+omega), despite interpolation
   for every internally existing set cut.
5. The basic axioms and kernel-confinement argument for M_kappa, with an
   ambient set of at least kappa atoms, ambient Choice, and infinite kappa.
6. The exact Collection-domain spectrum: first failure at cf(kappa) for
   limit cardinals (including omega); full Collection for successor cardinals.
7. After adjoining an external atom-enumeration predicate, exact first
   failure of both Replacement and Collection at cf(kappa).
8. Preservation of full pure-valued Collection in these ambient-definable
   expansions, and its consequences for all the surreal schemes.

## Distinctions that must not be omitted

- A formula with a set index domain is not automatically a set graph.
- The full Replacement conclusion in pure weak set theory assumes H.
- The first part uses only sign-sequence order, not an unproved field
  construction in the weak base.
- Internal proper-class atoms can form a set in the ambient universe.
- Cardinal computations in the support-model argument use ambient Choice;
  the agreement lemma justifies the internal interpretation.
- Replacement for the reduct is not Replacement for an expanded language.
- Pure-valued Collection is not Collection for arbitrary impure witnesses.
- The model constructions are relative interpretations, not proofs of a
  theory's own consistency.

## Attribution and priority

Classical surreal simplicity is not claimed as new. The finite-support and
countable-support models and their basic methods are explicitly compared
with Hamkins--Yao, including their attribution to Levy. Glazer--Yao's 2026
reflection separations are background and are not presented as new results
of this article.

The exact formulations and uniform refinements have been developed and
proved in this manuscript, but their historical priority is unverified.
No claim is made to resolve a named longstanding conjecture or to have an
independently certified breakthrough.

## Computation and formalization

All distributed finite tests were executed successfully. They test finite
sign comparisons, the cut algorithm, minimum birthday, prefix behavior,
negative ordinal-code analogues, and the local atom-transposition step.
They do not test infinite cardinals, class semantics, or full axiom schemes.

No new Lean or Rocq development is included or claimed checked. Repository
inspection was targeted at README descriptions and directory organization,
not a complete source audit or successful build of ProveIt.
