Constructive Diophantine geometry: checked Lean core
==================================================

DiophantineCore.lean is compiled source for Lean 4.32.0.
Only the bundled Std library is imported. Mathlib is not required.

Build:
  cd lean
  lake build

Alternative:
  lean DiophantineCore.lean

The source ends with #print axioms commands. All thirteen reported
theorems depend only on propext and Quot.sound (one only on propext).
No Classical.choice, sorryAx, added axioms, or native_decide occur.

See ../evidence/lean-build.txt for actual compiler output and
../evidence/lean-build.json for version and source-hash evidence.

What is proved:
- soundness/completeness of a bounded Boolean scan;
- soundness and failure completeness of an explicit witness search;
- explicit-fuel natural-rank descent;
- quadratic expansion and conic second-intersection identities;
- circle parametrization identities;
- cleared-denominator congruent-number curve/triangle identities.

What is not claimed:
- full formalization of every geometric theorem in the article;
- object-language iPRA derivations of the geometric statements.

These are ordinary Lean theorems. Their induction motives and uses of
the ambient Int library do not automatically satisfy the restrictions
of the deeply embedded first-order theory. The paper's formalization
chapter gives the explicit module plan, primitive recursive codes,
quantifier-free invariants, and ProveIt transfer interface needed to
complete that separate task.

The checked polynomial proofs deliberately use constructive expansion
of integer ring laws followed by omega on canonical monomials; they do
not rely on the classical ring-normalization theorems used by grind.
