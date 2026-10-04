# Source and proof audit

Date: 3 October 2026.

## Status and scope

The delivered article is an expanded research synthesis with mathematical
proofs. It is not independently refereed. No historical-priority claim is made,
and no complete classification of arbitrary exponential, omega-field, or
differential self-embeddings is claimed.

Earlier project drafts from the user's Library were read and used as working
material. Their claims were not treated as external peer-reviewed authority.
The expanded results and examples are presented with proofs and explicitly
scoped background inputs.

## Repository sources actually inspected

Repository: https://github.com/VladimirReshetnikov/ProveIt  
Pinned commit: `51b0a69d7385a786661e0169dc13ee7ab02b921c`

The following were accessed with the GitHub connector at the pinned commit:

1. `Algebra/SurrealNumbers/Surreal/Foundations/SignSequence.lean`, opening
   115 lines. Observed the actual `Type (u + 1)` carrier, `Ordinal.{u}` birthdays,
   zero-extended sign functions, lexicographic order, and sign/ordinal constructors.
   Blob SHA: `e2c093860f29b0b9ea312d50099fc4aa89a76a99`.
2. `Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceCutOperation.lean`,
   opening 130 lines. Observed the actual cut constructor combining
   `existsUnique_simplest_separator` with `small_cut_fillers`, and proofs of
   separating/prefix properties, canonical reconstruction, birthday bounds,
   and reindexing/negation laws.
   Blob SHA: `478c1e7f603e44032ae180f38bb0601044a94bae`.
3. `Algebra/SurrealNumbers/Surreal/Algebra/ExponentialProfile.lean`, opening
   declarations and initial ordered-field proofs. The comments enumerate the
   generic displacement/profile/value-action results and explicitly mark actual
   surreal exponential/valuation instantiations as pending. The initial twisted
   product/probe proofs were visible. The entire file was not independently rebuilt.
4. `Algebra/SurrealNumbers/docs/surreal/exponential-automorphism-rigidity/README.md`,
   opening 190 lines: theorem statements, verification boundaries, the claimed
   application to the pinned KKS Question 5.4, and pending concrete instantiations.
5. `Algebra/SurrealNumbers/docs/surreal/omnific-preserving-automorphisms/README.md`,
   opening 100 lines: inventory and assembled-report metadata, not a reading of
   the entire 221-page report.
6. `Algebra/SurrealNumbers/docs/surreal/omnific-preserving-automorphisms/13-omnific-isomorphisms-SOURCE_AUDIT.md`,
   opening 110 lines: attribution of prior fraction-field work and the scope of
   proposed automatic-strongness and proper-embedding arguments.
   Blob SHA: `c4d3939dd582134df06259043db833f2feced35e`.

These are targeted source reads, not a complete repository audit. No local
repository clone or Lean build was completed. Searches also located other
sign-sequence field/real/game modules, but the existence of those filenames is
not treated as verification of every bridge among the foundational interfaces.

## Primary literature

The article contains its own bibliography. Particularly relevant sources:

- Bagayoko–van der Hoeven, *Surreal substructures*, arXiv:2305.02001,
  https://arxiv.org/abs/2305.02001 . Order/simplicity substructures and
  sign-concatenation background; not a blanket field-embedding theorem.
- Kaplan–Krapp–Serra, *Decomposing the automorphism group of the surreal numbers*,
  https://arxiv.org/abs/2509.22374v3 . The arXiv metadata displayed v3 submitted
  23 April 2026. The v3 PDF's printed pages 4 and 10 were visually inspected for
  the leading-term/valuation conventions and Questions 5.4 and 5.6. The PDF
  and experimental HTML displayed different internal dates; the version pin is
  retained rather than treating the HTML date as an additional revision.
- Kuhlmann–Serra, *The automorphism group of a valued field of generalised formal
  power series*, https://arxiv.org/abs/2107.03362 . Background for strong Hahn
  maps and coefficient/monomial factors.
- van den Dries–Ehrlich, *Fields of surreal numbers and exponentiation*,
  Fund. Math. 167 (2001), 173–188,
  https://doi.org/10.4064/fm167-2-3 . The primary PDF was consulted, including a
  visual check of Proposition 4.7 on printed page 183. Relevant inputs are the
  exponential elementary-extension theorem and bounded normal-form framework.
- Ehrlich–Kaplan, *Surreal ordered exponential fields*,
  https://arxiv.org/abs/2002.07739 . Proposition 1.5 records the elementary
  exponential-extension input and the paper discusses initial embeddings.
- Berarducci–Mantova, *Surreal numbers, derivations and transseries*,
  https://arxiv.org/abs/1503.00315 ; Aschenbrenner–van den Dries–van der Hoeven,
  *The surreal numbers as a universal H-field*,
  https://arxiv.org/abs/1512.02267 . Background for the distinguished derivation,
  not for the ordinary derivative of a function or for the artificial diagonal
  derivations defined in the article.
- Bagayoko, *Hyperseries subfields of surreal numbers*,
  https://arxiv.org/abs/2409.16251 . Used only for the scoped hyperseries context,
  not as a theorem that every formal substitution acts on all surreals.
- Hamkins's author exposition on elementary/second-order transfinite recursion:
  https://jdh.hamkins.org/second-order-transfinite-recursion-is-equivalent-to-kelley-morse-set-theory/ .
  Used to distinguish set-valued recursion, class recursion, and truth principles.

Conway, Gonshor, and Coste are standard background references. They were not
newly audited cover to cover. The Coste institutional archive metadata was
located, but its document access returned a bot challenge; the article's
standard o-minimal calculus inputs are stated explicitly rather than described
as the outcome of a fresh full-text audit.

Targeted searches do not establish absence of antecedents. In particular, this
package does not establish priority or community acceptance of the repository's
claimed answer to the KKS v3 question.

## Proof dependencies and stress points

### Explicit order and algebra constructions

The written proofs use the standard sign representation, set-cut filling,
Conway normal forms, and Hahn/Neumann support and convolution facts. A support
and each summable family remain sets. Applying a class map to a support uses
class replacement, not a proper-class sum. The two lifts do not assert that
Hahn truncation is sign-prefix simplicity.

### Topology and derivatives

Continuity and differentiation are formulated with all positive surreal radii.
The statement that every set is uniformly discrete is about the *full ambient
class*; on a universe-relative set carrier only the corresponding small-family
statement is valid. The derivative proofs use arbitrary increments, not merely
monomial or sequential tests. Zero derivative does not imply constancy here
without additional hypotheses such as internal o-minimal definability.

### Exponential rigidity

The displacement product rule is twisted:
`D(ab) = sigma(a) D(b) + b D(a)`.
The finite identity alone does not prove the surreal application. That
application additionally uses the monotonic real-extending exponential, the
natural valuation, `ker(v o exp) = finite surreals`, and the uniform *surreal*
bound omega on finite displacements. These dependencies are proved or named
in the article. The two-map comparison replaces surjectivity with cofinality;
that strengthening has no new Lean certificate in this package.

### Elementary copies

The cofinal omission construction uses small-type realization, definable
Skolem hulls, exchange for definable closure, and set-stage unions. The bounded
construction additionally moves an external upper bound by a small elementary
isomorphism before extending the next stage. Both use uniform satisfaction
and the specified class-recursion framework; GBC+ETR is presented as sufficient,
not minimal. No claim of an explicit strongly additive exponential formula is
made for these model-theoretic embeddings.

### Fixed fields and differential variants

Fixed fields of strong weighted maps are calculated by the rigidity of a
reverse-well-ordered invariant support. General fixed fields are real closed
by the finite ordered root-set argument. The artificial diagonal derivations
are explicitly distinguished from the Berarducci–Mantova derivation and from
ordinary epsilon-delta derivatives.

## What the finite checks verify

`verification.py` performs 146,914 exact assertions using fractions and sparse
symbolic polynomials. It checks finite word order/prefix/meet compatibility,
rational compression, additive exponent reindexing, nested finite Hahn
multiplication and composition, weighted characters and omnific predicates,
explicit monomial witnesses, and both displacement identities. It verifies a
counterexample to multiplicativity of arbitrary one-level reindexing.

It does not verify infinite summability, arbitrary ordinal recursion,
proper-class existence, class truth, any global derivative limit, the
model-theoretic constructions, or a Lean formalization.
