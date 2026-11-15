LEAN FORMALIZATION OUTLINE -- UNCOMPILED

These files are not a completed Lean proof. No Lean compiler was available in
the delivery environment. They use the repository's inspected syntax/API,
but their elaboration and dependency axioms have not been checked. Importing
Mathlib alone does not establish an absence of Classical.choice dependencies.
No new axioms or sorry declarations have been inserted to conceal omissions.

What is written
---------------
FiniteKernel.lean gives typed data, finite search, and precise output predicates.
GeometricBridge.lean gives two short ordinary Lean proof scripts: the
symmetry/midpoint implication and preservation of nonzeroness by an injective
linear map. The centered-mesh identity is an explicit remaining obligation.
ObjectTarget.lean defines the actual first-order iPRA correctness formula,
its quantifier-free status, and a conditional transport to the concise theory.
It supplies neither the concrete PR syntax trees nor the correctness derivation.

Exactly seven completion milestones
-----------------------------------
1. Compile the scaffold against the pinned ProveIt checkout and align module
   paths. Resolve elaboration issues before treating even the short scripts
   as verified. Run dependency/axiom inspection after successful compilation.
2. Implement explicit codecs and PR syntax for signed integers, rational
   pairs, finite lists, arithmetic, bounded quantifiers, and bounded search.
   Prove their equations with PRA.precZero, PRA.precSucc, and PRA.qfInd.
3. Prove bounded finite pigeonhole inside Prf PRAAx, using the visited-color
   table and occupancy invariant. Every bounded invariant becomes a Boolean
   equation before invoking quantifier-free induction.
4. Prove base-m residue coding, Euclidean division, and nonzeroness of the
   quotient vector. Assemble the uniform coded mesh theorem in Prf PRAAx.
5. Implement and verify the FIXED rational symmetric-slab-plus-boxes checker:
   rational matrix and slab rows, positive denominators, nonzero determinant,
   rational box endpoints, disjoint interiors, strict total box volume, and
   exact endpoint support inequalities. Refine boxes to a common mesh and
   select the first m^n+1 distinct cell indices by bounded loops.
6. Prove the centered-cell identity and linear-map midpoint compatibility,
   then the slab membership conclusion. Instantiate CertificateSymbols with
   the actual fixed checker/extractor/output-checker PR syntax and construct
   Prf PRAAx [] (correctness thoseSymbols). The general represented-body
   version is a schema in a fixed sound inclusion relation and does not
   require decidable membership for arbitrary bodies.
7. Apply pra_theorem_iff / FromPRA.sigma to transport the object derivation;
   audit the final declarations and package a reproducible successful build.
   A host Lean Nat/Real theorem alone does not establish iPRA provability.

Suggested commands (not executed here)
-------------------------------------
In a ProveIt checkout at commit
329161f8da0b319d51ba9f6246c4b19d243f7193, with its dependencies installed:

  lake build ConciseIPRA.BiInterpretation
  lake env lean /absolute/path/to/lean/FiniteKernel.lean
  lake env lean /absolute/path/to/lean/GeometricBridge.lean
  lake env lean /absolute/path/to/lean/ObjectTarget.lean

The inspected root lakefile already declares the ConciseIPRA library at
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean and pins mathlib v4.32.0.
The included lean-toolchain records the matching Lean version. This directory
is NOT a standalone Lake package; do not run lake build in it expecting a
complete project. The object target requires the actual ConciseIPRA sources.

See FORMALIZATION_STATUS.txt for detailed proof invariants and sources.json
for exact inspected source paths, content SHAs, and immutable URLs.
