# Lean formalization status and completion path

The two Lean files are **uncompiled blueprints**. Lean was not installed in the
artifact-building environment. They contain explicit `sorry` obligations and
must not be read as completed formal proofs.

- `TopologySemanticBlueprint.lean` gives host-level definitions of finite
  preorders, finite complexes, strong simplicial carriers, selections,
  contiguity, chain maps, prism operators, and Betti certificates.
- `IPRAObjectLanguageBlueprint.lean` names the corresponding object-language
  formulas and uses the current ProveIt interfaces `PR`, `PTm`, `PRAAx`,
  `PRA.qfInd`, `Prf`, `NFm.ofPRA`, and `pra_iff_native`.

The decisive distinction is preserved throughout: a semantic Lean theorem is
not an iPRA derivation. The formal endpoint for each main lemma is an explicit
term of type `[] ⊢[PRAAx] φ`; the native bridge is applied only afterwards.

## Ordered completion milestones

1. **Coding library.** Explicit PR syntax for pairs, lists, bitsets, bounded
   folds, parity, matrices, and lexicographic bounded search, with object proofs
   of defining equations.
2. **Bounded Booleanization.** A syntax-directed compiler from fixed bounded
   formulas to Boolean PR tests, with `Prf PRAAx` equivalence proofs.
3. **Finite topology.** Preorder laws, upward-open sets, inverse images, and the
   monotone/continuous equivalence.
4. **Carrier calculus.** Relational composition, least selection, simpliciality,
   and selection contiguity.
5. **Chains and prism.** Enumerated simplices, normalized mod-2 chains,
   boundary-squared-zero, chain-map laws, and the prism identity.
6. **Homology certificates.** Bounded Gaussian elimination over `F_2` and, as an
   optional extension, checked Smith-normal-form certificates over the integers.
7. **Observation towers.** Fixed cover/refinement evaluators and naturality
   carriers for maps; applications instantiate these symbols and certificates.
8. **Repository integration.** Compile against Lean/Mathlib 4.32.0 at the pinned
   ProveIt baseline, remove all `sorry`, instantiate `TopologyObjectProofs`, and
   transport the finished derivations with `pra_iff_native.mp`.

The Python companion implements the same finite mathematics over exact data and
serves as a regression oracle, not as an iPRA proof checker.
