# Research status and audit boundaries

## Proposed contributions

The article's exact affine itinerary fibers, native-topology cofinality
dichotomy, compact-subsystem rigidity, and combined scalar-extension /
flat-deformation statements are proposed as original results. Written proofs
are supplied. The literature search did not establish historical priority,
and these claims need independent expert review before publication as new.
No named published open conjecture is claimed solved.

Classical rank-one Cantor repellers, the full shift, its periodic counts,
Neumann's support lemma, formal implicit-function recursion, and Conway normal
form are not new. The article labels and cites these inputs.

## Repository audit

Repository: VladimirReshetnikov/Surreal
Pinned revision: a3124af79f66b8b9c196d76b4cbc5ac3938907c4
Audit date: 22 September 2026

The GitHub connector was used to read the recursive tree, root README,
documentation inventory, and relevant report descriptions, especially
`docs/surcomplex/dynamics-and-normal-forms/README.md`.

This was a targeted scope audit, not an exhaustive reading of all long reports
or Lean source files. No assertion of complete absence of overlap across every
file is made. No repository build, commit, or modification was performed.

## Literature comparison

The bibliography includes primary or author sources for Neumann's ordered
series construction, Gonshor's surreal monograph, Berarducci–Mantova's normal
form/summability exposition, and Benedetto's non-Archimedean dynamics notes.
Benedetto's definitions of equicontinuity and classical Fatou sets and his
quadratic Cantor example were inspected, including their rendered PDF pages.

Targeted searches combined Hahn/surreal fields, symbolic itineraries,
higher-rank valuations, polynomial dynamics, convex subgroups, and Julia sets.
Search results were incomplete and sometimes noisy. Failure to locate the exact
statements is not proof that they have never appeared.

## Mathematical boundaries

- The main theorem requires degree-preserving reduction with distinct roots
  all in the residue coefficient field. Repeated roots are not covered.
- It works over set-sized Hahn fields without requiring a divisible exponent
  group or general algebraic closedness.
- The expansion scale, not valuation rank alone, determines pointwise coding.
- Integral nonescape and valuation-boundedness are different, explicitly
  defined properties. The article proves an exact comparison.
- Strong evaluation is not assumed to be a native topological limit.
- The symbolic full shift is the Hausdorff quotient of the scale uniformity;
  it is not the native quotient topology in the noncofinal case.
- Empty J_aff,v is a statement about the article's specified affine native
  equicontinuity definition. It is not an assertion that classical spherical
  or Berkovich Julia sets are empty.
- Surreal specialization uses set-supported normal forms and pairwise
  workspace enlargement; no set of all surreal numbers is assumed.

## Verification boundaries

`code/verify.py` passed 38,139 exact finite checks. These check rational series
coefficients, finite periodic identities, first-mismatch orders, a two-parameter
perturbation identity, and rank-two leading terms. They are not proofs of the
infinite- or transfinite-support theorems. No independent peer review or Lean
proof checking has been performed.
