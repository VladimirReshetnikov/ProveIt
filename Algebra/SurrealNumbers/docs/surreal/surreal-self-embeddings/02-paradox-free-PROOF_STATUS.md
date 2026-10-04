# Proof and verification status

## Written proofs

The article provides proofs of its explicit order and simplicity constructions, rigidity statements, normal-form lifts and their composition/image/fixed-field formulas, bounded and ordinal-fixing examples, topology criteria, and the elementary algebra underlying exponential-valuation rigidity. Standard structural results about the surreal field, its exponential, and its derivation are attributed to the literature.

The exponential-valuation argument is explicitly attributed to the inspected ProveIt research program; it is not presented as a newly discovered resolution in this package. The discussion of elementary embeddings and o-minimal definability invokes cited model-theoretic results.

Large-cardinal constructions are conditional on the existence and stated properties of an amenable elementary embedding into a transitive inner model. They do not assert an elementary membership embedding V into V. A field-embedding conclusion is kept distinct from an elementary-embedding conclusion in an expanded surreal language.

## Finite checks

`validate.py` completed 198,220 exact assertions with seed 20261003. The checks cover finite sign sequences, rational compression and its iterates, finite support transport, the additive-exponent multiplicativity criterion in finite examples, fixed-support tests, and twisted displacement identities with explicit amplification witnesses.

These are regression tests, not proofs of assertions about arbitrary ordinal lengths, arbitrary summable families, elementary extensions, or proper classes. In particular, the double-lift theorem and its infinite-support consequences rely on the written proofs.

## Lean boundary

No new Lean file is included. No Lean or Mathlib build was executed for this article. The source audit identifies a complete inspected simplicity module and limited inspected portions of other modules. Claims visible in a module header are reported as source inventory, not independently reverified kernel results. The actual surreal exponential instantiation remains separate from the generic field lemmas inspected in the repository.

## Source boundary

The repository snapshot is af04de3fa423f8f3253ee28db9afeb7fc6171604. The article's bibliography and Appendix A provide exact paths, versions, and inspection ranges. The external-source audit distinguishes original publications, revisions, and the published van den Dries--Ehrlich erratum.

This is a research article with explicit proofs, not a refereed publication or a priority certificate. Further research questions are identified as such and are not silently used as established facts.

## Document checks

The PDF compiled without unresolved references or LaTeX warnings. All 36 pages were rendered and reviewed in contact sheets, with important formula and formalization pages also inspected individually. The delivery archive omits LaTeX build intermediates and does not contain font files.
