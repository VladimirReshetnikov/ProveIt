# Dependency-ordered Lean completion plan

1. **Place the package in the ProveIt checkout.** Use the root workspace at
   commit `9df5cbdf39e6220be823f611987bd584d37711fd`.
2. **Compile `ObjectTraceCompiler.lean` definitions first.** Repair only arity
   or namespace drift; do not change the variable layouts documented there.
3. **Finish the two recursion equations.** They should close by `simpa` from
   `PRA.precZero` and `PRA.precSucc`.
4. **Create substitution normal-form lemmas.** Prove named simp lemmas for
   `BaseFm`, `StepFm`, `FinalFm`, and `InvRunFm` under the exact substitutions
   used by the compiler. This prevents the main proof from becoming a de
   Bruijn calculation.
5. **Finish `trace_base` and `trace_step`.** Use `Prf.subst`, `Prf.ofNil`,
   `Prf.impE`, `Prf.eqCongr`, `Prf.eqSubst1`, and the run equations.
6. **Apply `PRA.qfInd`.** The theorem `trace_all` is already isolated so that
   the only side condition is `invRun_qf`.
7. **Finish `trace_final` and `traceReflection`.** Use `Prf.allE`, substitution
   of the final local proof, `Prf.impI`, and `Prf.allI`.
8. **Add one concrete checked trace.** The triangular-number loop is the
   smallest regression target; the cubic bisection trace is the first analytic
   target.
9. **Implement the Boolean library.** Pair each PR symbol with closed
   `Prf PRAAx` truth-table and fold theorems; then prove
   `boundedFormulaReflection` structurally.
10. **Implement finite viability.** First prove a host-level list theorem, then
    replace lists by Nat codes and construct the `Prf PRAAx` induction.
11. **Build the finite program compiler.** Structural cases use `Prf.trans` and
    substitution; the loop case calls `traceReflection`; relation nodes call
    stable erasure.
12. **Transport only at the end.** Invoke `pra_iff_native` after the ordinary
    object-language derivation has typechecked.

A CI gate should reject any file under this directory containing `sorry`,
`axiom`, or `admit` before the package is reclassified as formalized.
