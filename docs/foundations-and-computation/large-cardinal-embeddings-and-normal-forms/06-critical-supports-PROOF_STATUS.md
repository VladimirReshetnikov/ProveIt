# Proof status and source audit

## Scope of the mathematical assertions

The article supplies written proofs of its comparison, defect, descent,
measure-code, and compactness-reformulation theorems. It relies on the
classical construction of the surreal field and its normal forms, Hahn
arithmetic and the Neumann support lemma, Gonshor exponentiation, and
standard well-founded ultrapowers. The principal additional arguments
are given explicitly rather than attributed to a theorem in the repository.

The proposed novel material was not located in the inspected sources.
This is a limited literature comparison, not an exhaustive novelty search
or a claim of certified priority. No named published open conjecture is
claimed solved. The cover/exact-descent statements retain exactly the
classical large-cardinal hypotheses they characterize.

## Especially important proof interfaces

1. Lemma 2.3 identifies internal canonical surreal constructions and
   normal forms with their external values. Its proof invokes the
   constructive normal-form/sign-expansion theory, not merely uniqueness
   of a field representation. It requires a transitive target with the
   same ordinals and the stated class conventions.
2. Normal-form coefficient arrays contain no zero terms. This condition
   is essential to the exact equalizer.
3. The converse from seed membership to sequence closure in Lemma 5.3
   uses a set-ultrapower representation and its single evaluation seed.
4. The no-descent result above kappa uses an index set of cardinality
   kappa. It is not a theorem about every embedding of critical point kappa.
5. The support bound in the compactness cover is internal to M. The
   support-cardinality thresholds for an input surreal are external.
6. The two maps are proper embeddings, not automorphisms. The paper does
   not settle the omega-preserving automorphism question in Kaplan,
   Krapp, and Serra.
7. The exponential statements use Gonshor's real surreal exponential.
   The surcomplex extension uses only formal local analytic evaluation;
   no global surcomplex exponential is silently assumed.

## Repository inspection

Repository: https://github.com/VladimirReshetnikov/Surreal

Inspection date: 23 September 2026.

The recursive tree response identified the tree object:
`0865f043aec113c14c69ef45006bbc7546a4e75a`.
This is recorded as a **tree object**, not asserted to be a commit hash.

Inspected material included:

- Root `README.md`, including the descriptions of the Hahn and
  foundational formalization layers.
- `docs/README.md`, including the collection's research-draft and
  formalization-scope warnings.
- Directory trees for the relevant foundational reports and `docs/new`.
- `docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets/README.md`.
- `docs/foundations-and-computation/surreal-fields-across-universes/README.md`.

Those two report descriptions establish that birthday reconstruction of
sets, elementary embedding transfer, and forcing/saturation comparisons
were already in the project. They are not advertised as new here.
The inspection did not audit every repository proof, and the new paper
does not depend on the correctness of an unreviewed repository theorem.

## External sources inspected

- Kaplan, Krapp, Serra, *Decomposing the automorphism group of the surreal
  numbers*, arXiv:2509.22374v3, especially normal forms, exponentwise lifts,
  strong additivity, and the omega-map automorphism questions.
- Berarducci, Kuhlmann, Mantova, Matusinski, *Exponential fields and
  Conway's omega-map*, arXiv:1810.03029v2 / Proceedings AMS 151 (2023),
  especially the purely infinite/monomial correspondence and infinitesimal
  exponential/logarithmic series.
- Neeman, *Ultrafilters and Large Cardinals*, author-hosted survey,
  especially critical points and derived measures.
- Williams, *Math655 Lecture Notes, Part 1.2*, 25 February 2019,
  especially the supercompactness definition and Fact 7 (seed/closure).

Conway and Gonshor are cited as the classical foundational books. The
whole text of those books was not retrieved in this session. The user-
provided Wikipedia page served as orientation, not as a proof source.

## Verification performed and not performed

Performed: LaTeX compilation to a 27-page PDF, cross-reference checks,
inspection of compiler diagnostics, PDF text extraction, and visual
inspection of page contact sheets and selected full-size pages, including
the main trichotomy and references.

Not performed: independent peer review, Lean formalization, verification
in another proof assistant, or computation of a nonprincipal ultrafilter.
No finite experiment is offered as verification of an infinite
large-cardinal assertion.
