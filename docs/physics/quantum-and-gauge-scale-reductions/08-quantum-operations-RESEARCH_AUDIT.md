# Research and evidence audit

Date: 23 September 2026.

## Repository scope

Repository: VladimirReshetnikov/Surreal
Snapshot: c0a36eebe5cf30aa72abfe4ef8ff9e46f63c3c28

Read through the GitHub connection:

* Repository metadata/tree, the opening of `README.md`, and the documentation
  catalogue/reading routes in `docs/README.md`.
* `docs/physics/surreal-scalars-and-spacetime/README.md` (substantial guide excerpts).
* `docs/surreal/finite-surreal-probability/README.md` (substantial guide excerpts).
* `docs/surquaternions/surquaternions/README.md`, lines 1–180.
* `docs/surcomplex/spectral-theory/article.tex`, lines 1–260.

Known overlap: finite spectral algebra, standard-part quantum shadows including
the conditioning restriction, classical leading-weight rare-event conditionals,
Schur-type effective matrices, Hamilton algebra and the SU(2) representation,
and filtered quaternionic commutators. Those prerequisites are not claimed as
new inventions. The new proofs in this article do not depend on uninspected
repository proofs.

Code-search queries for Schur-related terms returned no matches. This was not
used to infer absence: the catalogue itself indicates related known material.
The repository was not cloned, its Lean build was not rerun, and no file in it
was changed. Reports of review or formalization status are the project's own
reports, not independently reproduced evidence.

## Literature scope

Primary sources and official author/publisher records were used. The article's
bibliography contains stable identifiers and pinned repository links.

* Bordemann–Waldmann, formal GNS construction: arXiv abstract, relevant PDF text,
  and opening page inspected. This is direct precedent for non-Archimedean
  formal quantum states, not a claimed invention of this article.
* Vidal, single-copy entanglement: abstract and theorem-page PDF inspected.
  The one-sided filtering law proved here is a restricted classical extension.
* Dusson–Sigal–Stamm, Feshbach–Schur map: abstract, relevant theorem text and
  theorem-page PDF inspected. The finite kernel/determinant reduction is classical.
* Anderson–Trapp, Shorted Operators II: official publisher abstract and metadata,
  not the full paywalled article. No absence/novelty conclusion is inferred.
* Gallier, Schur-complement notes: relevant text/page on positive forms and
  generalized inverses inspected.
* Watrous, author manuscript of The Theory of Quantum Information: chapter 3,
  including the trace-norm contraction statement (Corollary 3.40), consulted.
* Wilson, Confinement of quarks: publisher record/abstract consulted for historical
  context, not for a new claim about confinement.
* Torres–Salazar-Serrano, weak-value amplification: official article record and
  relevant discussion consulted for the distinction between normalized signals
  and resource-adjusted metrology.
* Barnum–Graydon–Wilce: primary abstract/publisher record consulted to distinguish
  SU(2) quaternion coordinates from quaternionic quantum compositional axioms.
* Gonshor and Berarducci–Mantova: foundational references and primary records
  consulted; no full-book or full-foundation re-audit is claimed.

Some broad web queries returned irrelevant results; those were discarded rather
than treated as research evidence. Targeted title searches and primary links
were used instead. This is not an exhaustive priority search.

## Claim status

Candidate additions are the complete finite fixed-shadow Schur-defect
classification with its realization and displacement restriction, and the
combined leading-Gram/commutator/conditioned-unitary application with scale
contracts. Their novelty is not certified. All general deductions are given
as written proofs under explicit hypotheses; none is machine-verified in Lean.

The main classification applies to limited positive-semidefinite matrices with
an actually positive-definite eliminated block. It does not assert a result for
arbitrary indefinite actions, exact gauge zero modes, or infinite-dimensional
operators. The instrument results assume finite Kraus families and ordinary
finite dimensions. The analytic invariant-germ result excludes nonsmooth and
singularly normalized observables. The real-specialization claims have their
own finite-expression restrictions.

The 1,861 exact program assertions check rational or symbolic finite examples.
They are not proof of a universal theorem, a Hahn support construction, or any
physical interpretation. PDF compilation and visual inspection are separate
from mathematical checking.

No external article, repository source manuscript, or font file is redistributed.
