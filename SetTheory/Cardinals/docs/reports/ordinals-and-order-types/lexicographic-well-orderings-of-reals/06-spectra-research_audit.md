# Research and proof audit

## 1. Scope and date

Prepared October 2, 2026. The question is interpreted as comparing the canonical
ordinal enumerations of well-ordering relations on the *labeled* real line.
The real labels are compared in their ordinary order. There is no auxiliary
well-order of coordinate pairs and no order-type-first convention.

All main theorems of the article are accompanied by written proofs. The
finite checks have been executed successfully. No Lean, Rocq, or other proof
assistant has checked the transfinite arguments. The report is not a claim
of independent peer review or historical priority.

## 2. ProveIt snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `6ea60e3677bd847a00baf023c3c532c83884530e`.

The repository connector was used to inspect the tree and search for
`lexicographic`, `well-orderings`, and `sign sequences`. The recursive tree
response was too large to inspect exhaustively. Therefore the audit is
**targeted**, not a certification that no overlapping file exists anywhere
in the repository.

Relevant inspected files:

1. `SetTheory/Cardinals/README.md`: organization and status of the cardinal
   project and research reports; explicitly distinguishes reports from checked
   formalizations.
2. `SetTheory/Cardinals/docs/reports/README.md`: report index, including the
   ordinals/order-types and transfinite-word areas, and the unrefereed status
   of those materials.
3. `Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceSimplicity.lean`:
   the statements and source proofs concerning minimum-birthday elements of
   nonempty convex sets of sign sequences and uniqueness of simplest cut
   separators once a separator exists.

The last module is used as conceptual and formalization context. It was read,
not compiled. Its existence-versus-simplicity distinction is preserved in the
article. No unverified repository report is used to supply a missing premise
in one of the proofs.

## 3. Public primary sources

### Justin Tatch Moore

*A universal Aronszajn line*, author's manuscript (2008), Section 2.

https://pi.math.cornell.edu/~justin/Ftp/Aline_univ.pdf

Used for attribution of the standard representation of a linear order by
characteristic functions of its initial segments. The PDF was inspected,
including its representation discussion. No forcing-axiom theorem from the
paper is assumed in this report.

### Janak Ramakrishnan

*Definable linear orders definably embed into lexicographic orders in
o-minimal structures*, arXiv:1003.5400v5 (2010).

https://arxiv.org/html/1003.5400v5

Used for literature context on lexicographic representation, including its
references to Fleischer's original work and correction. The article does
not invoke the o-minimal theorem for arbitrary orders. In particular it
makes no converse claim that the absence of long monotone sequences alone
implies embeddability into a fixed lexicographic power.

### Terence Tao

*245B, Notes 7: Well-ordered sets, ordinals, and Zorn's lemma (optional)*,
January 28, 2009.

https://terrytao.wordpress.com/2009/01/28/245b-notes-7-well-ordered-sets-ordinals-and-zorns-lemma-optional/

Background on ordinal order types and well-ordering methods. The report
supplies its own first-disagreement, stabilization, and cut-spine arguments.

A direct copy of Fleischer's original paper was not obtained, so the article
does not represent that original as a source it independently verified.

## 4. Proof dependencies and checks

### Definition and universality

The canonical-enumeration carrier, no-proper-prefix lemma, and transitivity
are proved directly. The binary encoder is a disjoint-pair construction;
initial-segment coding is standard and proved again. Their finite analogues
are among the executed tests.

### Exact ordinal barrier

The essential proof is transfinite tail stabilization through the regular
successor cardinal c^+. At each stage a tail of a proposed long monotone
sequence agrees on the current prefix. Next coordinates become constant,
and limit stages preserve a tail by regularity. Continuing would inject c^+
into the real line. This does not assume that c itself is regular.

### Finite-tail structure and topology

The extremal-enumeration lemma classifies minima and maxima of residual
orders. Applying it to both sides of a potential jump forces the residual
alphabet to be finite. The resulting jump rule, factorial prefix-cone
cardinalities, and converse adjacency rule have finite sanity checks.
The density and derived-set claims remain written transfinite arguments.

### Gap classification and completion

The central additional argument is the unique straddling-prefix spine of a
cut. Each residual permutation order has countable cofinality or an endpoint
at either end; greedy removal of successive extrema proves this fact. A cut
stops either horizontally between next-value cones, or at a limit-prefix
boundary. This provides the gap-spectrum upper restriction. Explicit pair
prefixes realize each allowed pair. Counting descriptions and constructing
many distinct boundaries gives exactly 2^c proper gaps.

### Point characters and minimal slice

Available lower/upper disagreement positions determine local cofinalities.
An eventual absence of lower (upper) branches would force an increasing
(decreasing) real tail, which must be countable. The same observation applies
to the minimal slice. Its topological base consists of short-prefix cones;
König's diagonal argument gives cf(c) > omega.

### Further constructions

The first-c coordinates give the exact lexicographic-sum decomposition.
Appending a fixed limit-length tail yields an embedding into singleton
finite-condensation classes, proving equimorphism with the dense quotient.
Surreal sign comparisons use an explicit ternary encoding of termination,
followed by binary pair coding; no surreal arithmetic is assumed.

## 5. Deliberate limitations

- No classification of all orders of cardinality between c and 2^c that
  embed into the full order is claimed.
- Nonembedding of the full order into the minimal slice is proved only under
  2^{<c} < 2^c. The equality case is not resolved by the cellularity argument.
- No full automorphism-group description or uniqueness theorem for the dense
  quotient/completion is claimed.
- The set of proper gaps of the minimal slice is not fully classified.
  The injective missing-branch construction gives an explicit family, not
  every possible gap.
- No claim is made that full AC is necessary. All theorems are stated in ZFC;
  weaker-choice variants are retained as a separate research question.
- The question list gives problems left by this analysis. It is not a claim
  that each is a recognized, previously published open problem.
- Finite tests, PDF rendering, and successful LaTeX compilation are not
  substitutes for proof-assistant verification or independent mathematical
  review.

## 6. Packaging and verification

The delivered source compiles with pdfLaTeX, using an embedded bibliography
and no external graphical assets. PDF pages were rendered and visually
checked; layout warnings and long-source-link overflow were addressed.
The JSON records the executed finite check sizes and their successful status.
No repository file was created or modified by this work.
