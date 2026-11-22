# Lean status and completion path

**No Lean executable was available in the authoring environment. These files
are source candidates and outlines, not a claim of successful compilation or
of a completed formalization.** There are no `sorry` or new `axiom`
declarations in the candidate source files.

## Existing repository infrastructure inspected

The reference commit is
`d36b35eed5bd01af4ade66bf539622495813ccc8` of
`VladimirReshetnikov/ProveIt`. Paths below are relative to
`Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/`.

- `IPRADerivations/Core/Tactic.lean`: `natEq`, `deriveNat`, and `ipra_simps`
  move a derivability judgment to the ring of differences of the syntactic
  quotient and back. This is why `IPRABridge.lean` has deep iPRA conclusions.
- `IPRADerivations/Core/OrderCertificates.lean`: `ipra_le` constructs a
  derivation from an explicitly nonnegative combination of inequality slacks.
- `IPRADerivations/Analysis/TaggedFTC.lean`: `tagged_upper` and `tagged_lower`
  perform the finite telescoping step by `PRA.qfInd`. Their source explicitly
  leaves the derivative-to-cell estimate and the passage to real names open.
- `IPRADerivations/Analysis/RiemannSumRules.lean`: finite sum additivity,
  scaling, and error estimates have deep `Prf PRAAx` conclusions.
- `IPRADerivations/Topology/EulerCharacteristic.lean`: the finite
  Euler--Poincare statement has a deep conclusion; its additional general
  finite-set additivity/collapse lemmas are ambient Lean statements.

## Candidate files

`Assembly.lean` proves the rational aggregate identity and its error bound in
ambient Lean. This is useful algebraic bookkeeping, but ambient Lean proves
far more than iPRA and is not the final logical target.

`IPRABridge.lean` gives the sign-free Euler coefficient identity and the
upper/lower residual combination as actual `Γ ⊢[PRAAx] ...` judgments. These
small steps use the inspected repository API; they still need compilation.

`Blueprint.md` lists the remaining definitions and proof obligations. No
unproved smooth theorem is introduced as a Lean axiom, opaque declaration,
or theorem with an admitted proof.

## Suggested compilation

Use the repository's own pinned toolchain and dependencies. From its
`Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/` directory, copy
`IPRABridge.lean` to `IPRADerivations/Geometry/GaussBonnetAssembly.lean`, and run
`lake env lean IPRADerivations/Geometry/GaussBonnetAssembly.lean`.
`Assembly.lean` needs a Mathlib environment; run `lake env lean` on that file.
The paths are integration instructions, not a report that these commands were
run successfully here.
