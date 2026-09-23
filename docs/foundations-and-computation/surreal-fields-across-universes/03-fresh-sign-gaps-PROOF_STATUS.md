# Proof and verification status

## What the article establishes by written argument

- Absolute inclusion of old sign sequences and field arithmetic.
- The canonical bijection between fresh signs and externally set-presented
  gaps, with the exact two-sided cofinality calculation.
- The entire filling class of each gap as its fresh-prefix cone.
- Regularity of the least length of a new ordinal-valued sequence and an
  explicit ordinal block code attaining the least missing cut.
- The uncountable saturation criterion and the separate finite-parameter
  criterion.
- The transport of gap spectra into real forms, its conjugacy invariance,
  and finite forcing-tower constructions.
- The topological comparison with the outer surreal field.

## Established ingredients, not claimed as new

- Conway/Gonshor surreal construction and real closedness.
- Fresh functions/subsets in forcing theory.
- Real-closed-field and algebraically-closed-field quantifier elimination.
- Standard forcing preservation facts; the Prikry example imports its
  usual no-new-reals and cofinal-sequence properties.
- Proper-class algebraically closed field back-and-forth and the
  fixed-field criterion for conjugacy, already present in the repository.
- Existence of nonconjugate real forms by a countable-cofinality
  construction, also already in the repository.

## Important boundaries

1. All external sets and sizes are relative to N, not an unrestricted
   larger metatheory.
2. Gaps must have N-set cofinal and coinitial presentations.
3. Birthday cofinalities are computed in N, and may differ from those in M.
4. The equivalence with the order-cut property applies to field saturation
   at uncountable cardinals; the omega case has a separate proof.
5. No compatibility of the transported field isomorphisms with simplicity,
   valuations, exponentials, or derivations is asserted.
6. Finite forcing towers do not establish an infinite-iteration result.
7. A matching prior theorem was not found in the inspected sources, but
   historical novelty is not certified.

## Checks actually performed

- LaTeX compiled with pdfLaTeX through latexmk.
- Final LaTeX log: no undefined references/citations, overfull boxes,
  underfull boxes, or warnings.
- PDF rendered with Poppler and visually inspected; final document is
  21 pages.
- The included finite Python regression tests were executed successfully.

No Lean proof, theorem-prover verification, forcing simulation, or
independent repository build was performed. The finite tests cannot
substitute for the transfinite proofs. Independent specialist review is
still appropriate before treating the manuscript as a research result.
