# Proof dependency and scope audit

This is a description of public proof dependencies, not a machine-verification
certificate.

## Imported mathematical inputs

- Ultraexacting witnesses at sufficiently correct heights, and their established
  rank-into-rank dynamics: Aguilera–Bagaria–Lücke, arXiv:2411.11568v4, and
  Aguilera–Bagaria–Goldberg–Lücke, arXiv:2509.10254v1.
- In particular, the critical sequence of the chosen witness is cofinal in the
  cardinal lambda. Its cofinality is not inferred merely from cf(lambda)=omega.
- The I0/ultraexacting equiconsistency and forcing V_lambda into HOD while
  preserving ultraexactingness: ABGL, Theorem A/4.5, Proposition 3.9, Corollary 3.10.
- The usual set-forcing theorem when passing from an inner ZFC model and a generic
  set to the forcing extension.

## Recalled, with proofs included

- Relative-HOD closure, including Choice for the one-parameter hereditary class.
- Fixed-small-set and fixed-small-family rigidity from the supplied synthesis.
- Normal-measure diagonal intersections and finite-color homogeneity.
- The strong Prikry lemma and Mathias's geometric genericity criterion.

## Continuation deductions

1. Fixed-counterexample principle: a finite list of first-order counterexample
   predicates is reflected uniformly before the witness and its classes are
   chosen. The least rank of a low parameter is fixed and hence below the
   critical point. A canonical least counterexample using that fixed parameter
   is then fixed, without assuming arbitrary ordinal parameters are fixed.
2. No splitter for a single orbit: a fixed subset has the same membership bit at
   every successive orbit point.
3. Tail constancy for bounded colorings: the canonical counterexample's range
   bound is a fixed ordinal below lambda and therefore below the critical point.
4. Internal lambda-completeness: a failed intersection of an internally indexed
   short family produces a bounded coloring with no tail-constant fibre.
5. Critical-sequence normality: a fixed tail-large set contains the first critical
   point; a regressive function's value there is below the critical point and is
   therefore fixed throughout the sequence.
6. The filter is an element of the inner model because its definition uses q and
   ordinals, and its members are hereditarily in the allowed definability class.
   For HOD_{ {q} }, use the restriction to that model's own subsets of lambda.
7. The geometric criterion makes each representative Prikry generic. Finite
   differences are ground-model sets, so all representatives yield the same
   forcing extension.
8. The paired-orbit construction preserves relative HOD and rigidity while
   changing tail normality and even tail decisiveness.

## Quantifiers that must not be strengthened

- Completeness quantifies over sequences belonging to the specified inner model.
- Tail(q,A) is an ambient predicate; q need not belong to the inner model.
- Normality of the canonical tail filter is proved for the critical orbit, not
  for every fixed quotient class or every forward orbit.
- The Prikry argument uses the ZFC model HOD_{ {q} }, not Choice in the possibly
  larger HOD_{V_lambda union {q}}.
- The witness height is correct for a fixed finite collection of formulas, not
  for all formulas at once.
- The canonical inner model is independent of a representative of q; no
  canonical selection of q from lambda is claimed.
- The Prikry extension is contained in V; equality with V is not asserted.
- Equiconsistency is an enrichment of the established calibration, not a new
  lower-bound proof for ultraexactingness.
