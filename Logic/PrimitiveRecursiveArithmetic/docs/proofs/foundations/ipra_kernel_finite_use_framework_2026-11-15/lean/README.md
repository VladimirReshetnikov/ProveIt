# Lean formalization package

The formal target is the deep embedding in `ConciseIPRA.PR`:

```lean
Γ ⊢[PRAAx] φ
```

not merely a proposition about host Lean naturals.

## Files

- `KernelCompiler.lean` supplies the generic kernel-facing layer.  It contains
  no `sorry`, `admit`, or new axiom.  The central `ProofBuild.step` theorem
  performs simultaneous cut through a reverse-topological proof schedule and
  returns genuine `Prf PRAAx` values.  It also contains the QF loop compiler,
  stable-observable rule, boundary rule, gap rule, and native export.
- `ArithmeticInterface.lean` packages the exact fields a domain development
  must fill.  Constructing a record requires object-language proofs; the
  `compile` methods are generic.
- `../examples/GeneratedSchedule.lean` is produced from the JSON DAG by
  `code/generate_lean_schedule.py`.

## Status

The source was written against the API in ProveIt main commit
`9df5b64f82b891640b2154bd14dcee251a25d37f`, including:

- `ConciseIPRA/Syntax.lean` SHA `a3c8ec9700382e34df9ffdeaa2f2066bbfaf1348`;
- `ConciseIPRA/Deduction.lean` SHA `0969040f77fdd3ed9526e360e7a998584b4d9d8c`;
- `ConciseIPRA/PR.lean` SHA `3251631592070d9ed3687cc0bf7dbd5eb452e46f`.

Lean was not installed in the artifact-building runtime, so these modules have
**not been typechecked here**.  Static auditing verifies that the generic files
contain no placeholders.  The next authoritative step is compilation in the
repository's pinned Lean 4.32.0/Mathlib environment, followed by `#print axioms`
inspection.

## Integration

Place `KernelCompiler.lean` and `ArithmeticInterface.lean` where the import
`ConciseIPRA.PR` resolves.  Then run:

```sh
lake env lean KernelCompiler.lean
lake env lean ArithmeticInterface.lean
```

Any type mismatch should be repaired at the interface boundary rather than by
weakening a theorem to `True` or replacing an object proof by a host theorem.
