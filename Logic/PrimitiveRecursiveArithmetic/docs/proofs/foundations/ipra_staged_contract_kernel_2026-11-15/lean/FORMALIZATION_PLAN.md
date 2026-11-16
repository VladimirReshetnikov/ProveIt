# Dependency-ordered path to a complete Lean formalization

1. **Compile the kernel unchanged.** Place `StagedContractKernel/` under
   `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/` and the
   umbrella module beside it. Resolve only API spelling changes. Run
   `#print axioms` for `instantiateInto`, `NodeObligation.compile`, and
   `LoopObligation.compile`.
2. **Add a small PR Boolean library.** Define zero-test, truncated subtraction,
   comparison, Boolean conjunction/disjunction/complement, bounded product,
   and bounded maximum as concrete `PR` terms. Derive their equations from
   `PRA.proj`, `PRA.comp`, `PRA.precZero`, and `PRA.precSucc`.
3. **Booleanize fixed bounded syntax.** Define `BForm.toFormula` and
   `compileBForm`. Prove reflection by recursion on `BForm`; bounded quantifier
   cases use a single quantifier-free induction over the finite fold.
4. **Least bounded search and enumeration.** Use a state `(found,index)` and the
   invariant stated in report Section 5. The result is a concrete witness term
   plus `Prf PRAAx` correctness, not a host-level existential.
5. **Finite traces.** Reuse `LoopObligation.compile`. Build one concrete
   state-transition `PR` term and prove the base, step, and finish fields.
6. **Demand closure.** Encode fixed-length vectors by mixed radix. For acyclic
   graphs, prove the reverse pass by finite unrolling. For cyclic monotone
   demands, iterate inside an explicit cap and use the sum-increase invariant.
7. **Relational viability.** Define the backward Boolean table and least
   successor selector. Prove by reverse finite induction that the selected path
   reaches the final level and every edge is valid.
8. **Stable observation.** Add exact branch independence and rational-diameter
   variants. The latter concludes only the displayed error inequality.
9. **Resource layer.** Formalize fixed-dimensional mixed-radix rank and prove
   that strict lexicographic descent lowers it. Keep dimension fixed in every
   generated program.
10. **Domain libraries.** Instantiate the interfaces for rational arithmetic,
    polynomial certificates, represented reals, formal series, finite
    simplicial complexes, finite categories, and finite affine covers.
11. **Native export.** After each main ordinary-iPRA theorem is complete, export
    with `pra_iff_native.mp`; do not develop applications directly in the
    native syntax.

A complete application should end with a theorem whose conclusion literally
has type `Prf PRAAx Gamma Goal`, followed by an optional `NPrf` corollary.
