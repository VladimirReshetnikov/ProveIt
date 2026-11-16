# Formalization status

These files are an **uncompiled Lean outline**, not a kernel-checked extension
of `ConciseIPRA`.

They are written against ProveIt commit
`9df5cbdf39e6220be823f611987bd584d37711fd` and use the exact upstream names
`PR`, `PTm`, `PRAAx`, `Prf`, `PRA.qfInd`, `NFm.ofPRA`, and
`pra_iff_native`.

## Completed at source level

- explicit arity-correct term builders `app1`, `app2`, and `app3`;
- all trace-system formulas with documented de Bruijn layouts;
- direct run-equation lemmas reducing to `PRA.precZero` and `PRA.precSucc`;
- theorem signatures for the four small milestones consumed by the main
  trace compiler;
- structural bounded-formula, relational-tower, and finite-program APIs.

## Static close-out audit

- Lean executable: unavailable in the artifact runtime.
- Visible `sorry` occurrences in the five `.lean` files: 31.
- Explicit `axiom` declarations: 0.
- `admit` occurrences: 0.
- The two run-equation lemmas and the quantifier-free side-condition lemma are written without placeholders, but remain uncompiled here.

## Visible remaining obligations

1. Prove `trace_base`, mainly one state-argument transport.
2. Prove `trace_step`, mainly substitution simplification and successor-run
   transport.
3. Specialize `trace_all` and discharge the final contract.
4. Close the input binder in `traceReflection`.
5. Implement the Boolean fold symbols and their object proofs.
6. Implement finite viability as a PR symbol and migrate the semantic proof to
   `Prf PRAAx`.
7. Replace the abbreviated `Prop` fields of `CertifiedProg` by actual formula
   builders and derivations.
8. Build under the repository Lake workspace and remove every `sorry` before
   making a kernel-check claim.
