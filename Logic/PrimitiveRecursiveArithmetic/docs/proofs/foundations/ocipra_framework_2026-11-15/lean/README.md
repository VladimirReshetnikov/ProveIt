# Lean outline

The outline uses the current ProveIt names `PR`, `PTm`, `PRAAx`, `Prf`,
`NPrf`, `PRA.qfInd`, and `native_iff_pra`.  Its main architectural decision is
a dual backend:

- use `NPrf` to generate equational/iterator proofs with minimal syntax;
- transfer them to iPRA with `native_iff_pra`;
- use full `Prf PRAAx` for bounded Boolean logic, witnesses, and contract
  packaging.

`Contracts.lean` and `Examples.lean` are intended to be close to compilable in
the root ProveIt workspace.  `TargetInterfaces.lean` records proof obligations
without asserting instances.  `CompilerBlueprint.lean` gives the precise
construction route and theorem signatures.

No Lean build was performed in this delivery because the runtime contained no
Lean executable.  This limitation is recorded rather than hidden by a
successful host-language test.
