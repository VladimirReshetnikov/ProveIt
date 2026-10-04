# Sources, scope, and provenance

The topic was selected by comparing Glazer's published mathematical work with
ProveIt's actual surreal-number README and repository organization. The supplied
LinkedIn URL served as an identifying pointer, not as evidence for a current
employment role. No biographical inference is needed for the mathematics.

## Primary sources

1. Elliot Glazer and Bokai Yao, *Reflection Principles in ZFU*,
   arXiv:2602.21970v1 (February 25, 2026).
   https://arxiv.org/html/2602.21970v1
   Used for the research intersection, urelement conventions, and the
   permutation-model framework (especially Section 3.1). The article here does
   not claim to prove their reflection theorems anew or resolve their other
   published questions.

2. Asaf Karagila and Jonathan Schilhan, *Intermediate models and Kinna-Wagner
   Principles*, arXiv:2409.07352v1 (September 11, 2024).
   https://arxiv.org/html/2409.07352v1
   Used for KWP indexing, its standard coding formulation, and the status of
   KWP_1 in Cohen's first model. The Kinna-Wagner principle itself is classical.

3. Ovidiu Costin and Philip Ehrlich, *Integration on the Surreals*,
   arXiv:2208.14331v5 (July 4, 2024).
   https://arxiv.org/abs/2208.14331
   The PDF explicitly discusses NBG without set or class choice on printed
   page 6, and conservativity over ZF on printed page 50. Only the elementary
   surreal interface and foundational framework are relevant here, not the
   paper's integration results.

4. John H. Conway, *On Numbers and Games*, second edition, A K Peters, 2001.
   Classical background for surreal arithmetic, monomials, and normal forms.
   This is a standard bibliographic reference, not a claim to have inspected
   an entire digital edition during this task.

5. Vladimir Reshetnikov, *ProveIt*, `Algebra/SurrealNumbers/README.md`.
   https://github.com/VladimirReshetnikov/ProveIt/tree/main/Algebra/SurrealNumbers
   Accessed through the GitHub connector, not inferred from a generic search
   snippet. The README itself distinguishes unrefereed reports from checked
   declarations and describes an audit permitting `Classical.choice`.

   Inspected README blob SHA:
   `18478d58670c384953fb85dcd1a6d931c644aa32`

   Inspected main-tree SHA:
   `2b7b388ba81a3355b19a7c2d2fe797e92f572355`

   The latter is a tree identifier, not asserted to be a commit identifier.
   The full repository was not independently verified or built for this report.

## Contribution boundary

The manuscript's new work is the development and proof of its particular
calibration, optimal-target, and quantitative orbit-collapse statements, with
an explicit account of their foundational hypotheses. This does not establish
priority. The elementary sign coding, normal-form uniqueness, polynomial
universal property, finite-variable UFD theory, real-closed-field facts, and
permutation-model construction are classical background.

The literature search located directly relevant primary sources but did not
establish whether all combined statements or quantitative refinements have
appeared previously. Consequently no assertion of a historically verified
breakthrough is made. The twelve research questions are proposed next targets,
not certified entries in a catalogue of published open problems.

## Proof and computational boundaries

- Main positive results: arguments over ZF, with explicitly stated classical
  choice-free surreal background.
- Symmetry counterexamples: internal statements in the specified full ZFA
  permutation models over a choice-satisfying ground universe.
- ZFA-to-ZF transfer: not supplied or asserted.
- Prescribed-order universality from KWP_1 alone: not supplied or asserted.
- Arbitrary-ordinal and model-theoretic formal verification: not supplied.
- Finite test run: 20,595 exact assertions passed, with a fixed seed.
- Existing repository: not modified; the proposed module names are a roadmap.
