# Proof status and assumptions

## Overall status

All asserted new results have conventional proofs in `article.tex`. The
article is an AI-assisted research draft, not a refereed publication. No
Lean proof, full formal verification, or independently certified novelty is
claimed. Finite checks are deliberately separated from the transfinite
arguments.

## Foundational boundary

General statements use transitive common-ordinal universes `M subset N`
satisfying ZFC, with the inner-model predicate available for the Separation
and Replacement instances in the proofs. Cardinalities, cofinalities,
parameter sets, and types are computed inside the outer universe `N`.
Statements are not assertions of saturation in an arbitrary larger
metatheory.

Class field isomorphisms and simultaneous involutions additionally use GBC
with Global Choice. The back-and-forth has a set-sized partial map at every
ordinal stage. A set-indexed family of class structures is represented by
a uniform class relation, not by a set containing proper classes.

## Principal theorem dependencies

| Result | Assumptions beyond the standing conventions | Proof location |
|---|---|---|
| Cofinality pushforward | None; classical surreal cut principle | 3.2, 4.1–4.3 |
| External density ceiling | Set forcing and a ground dense set | 5.1 |
| Generalized Cohen singleton | Ground regular infinite kappa, alphabet size at least two | 6.1–6.3 |
| Easton realization | GCH; published Easton-spectrum theorem | 7.2–7.3 |
| Relative finite complements | GCH; sparseness (8.1); finite missing coordinate set | 8.2–8.5 |
| Same-saturation family | GCH; prescribed uncountable regular minimum | 8.6, 9.2–9.3, 10.1 |
| Involutions on one carrier | Previous family plus Global Choice | 11.1–11.2 |
| Equal-spectrum nonisomorphism | A measurable cardinal; Cohen followed by Prikry forcing | 9.3, 12.1–12.2 |

Numbered theorem references in the PDF are authoritative; the LaTeX labels
provide stable cross-reference identifiers.

## Imported mathematics

The following are inputs, not results newly proved in this article:

1. The standard sign construction and cut principle for surreal numbers,
   absoluteness of their arithmetic on old sign sequences, real closedness,
   and standard part of a finite surreal.
2. Quantifier elimination and the usual type descriptions for real closed
   and algebraically closed fields.
3. The set-forcing theorem and elementary closure/decision machinery.
4. Cardinal/cofinality preservation and the full Easton fresh-function
   spectrum from Fischer–Koelbing–Wohofsky.
5. Small-forcing preservation of measurability from Lévy–Solovay, and the
   stated Prikry properties and fresh-function spectrum.

The sign-gap correspondence and saturation framework also occur in the
repository report. The present manuscript supplies proofs rather than
assuming that the repository's unformalized arguments are machine-checked.

## Delicate steps checked during drafting

- A candidate shorter than a fresh root need not be its prefix. The cone
  proof separates the actual-prefix case from an earlier disagreement.
- The cardinal used by the density ceiling is `|D|` in the extension.
  Reconstruction uses the ground forcing relation, not an assumption that
  the cofinal repetition set is old.
- The block code preserves external cofinality, not necessarily birthday.
- The old poset is compressed using old words; no claim is made that an
  arbitrary new word belongs to that ground family.
- Relative upper factors are proved distributive in the intermediate
  model by high closure and a small-forcing argument. Ground closure is
  not merely assumed to remain true after small forcing.
- The finite-complement theorem does not extend without proof to infinite
  complements.
- The counterexample uses Prikry forcing computed in the Cohen extension.
  It is not presented as a product with an unchanged old measure or poset.
- Nonisomorphism of equal-gap fields uses omega-saturation, not an
  unsupported claim that birthdays are field-isomorphism invariants.
- Transported involutions are not claimed to preserve valuation,
  simplicity, exponentiation, derivatives, or omnific integers.

## Computational evidence

`checks/finite_checks.py` passed 469,107 checks. The checks are finite
identities only. In particular, there are no fresh finite signs over the
transitive grounds under discussion. The tests cannot establish any
forcing or proper-class assertion.

The PDF was compiled successfully, cross-references resolved, the LaTeX
log checked for warnings/overfull boxes, and the pages rendered and
visually inspected. These are document-quality checks, not a mathematical
proof certification.

## Priority and independent review

The proposed contributions should be independently reviewed, with special
attention to the relative intermediate-model argument in Section 8 and
the foundational interpretation of Section 11. The targeted source search
is not exhaustive. No named published conjecture is represented as solved
merely because a related restricted repository question has been answered.
