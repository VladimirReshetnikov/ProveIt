# Peano arithmetic is undecidable

This project proves that the set of syntactic theorems of first-order Peano
arithmetic is not a computable predicate. Here “decidable” has its
computability-theoretic meaning: there is no total computable Boolean function
which, given an encoded arithmetic sentence, says exactly whether that
sentence has a formal PA derivation.

This is different from saying that one particular sentence is independent of
PA. The theorem concerns the algorithmic decision problem for the entire set
of PA theorems.

## Mathematical reduction

The two formalizations use equivalent standard routes.

- The Lean proof starts with mathlib's noncomputability theorem for the
  halting problem. The arithmetization theorem from
  FormalizedFormalLogic/Foundation produces one unary arithmetic formula
  `H(x)` representing that recursively enumerable predicate. For every
  program code `n`, Sigma-1 completeness and standard-model soundness give

  ```text
  program n halts  <->  PA proves H(n).
  ```

  Foundation's arithmetized numeral-substitution function gives a computable
  map from `n` to the Goedel code of `H(n)`. Consequently a decider for the
  full predicate on encoded PA theorems would decide halting. The public Lean
  theorem has type
  `¬ ComputablePred PAUndecidable.EncodedPATheoremhood` and is named
  `PAUndecidable.peano_arithmetic_theoremhood_not_decidable`.

- The Coq proof uses the fully mechanized DPRM theorem in the Coq Library of
  Undecidability. A Diophantine equation is translated to the existential PA
  sentence asserting that it has a solution. PA proves the sentence from a
  concrete solution, while soundness in the standard natural-number model
  gives the converse. Since Hilbert's tenth problem is undecidable, PA
  deduction is undecidable. The public theorem is
  `peano_arithmetic_theoremhood_not_decidable`.

Both developments concern the ordinary language with zero, successor,
addition, multiplication, and equality, together with the full first-order PA
induction schema. Neither proof assumes PA's consistency: soundness follows
externally from the standard natural-number model.

## Dependencies

The Lean project uses the repository submodule
`lib/FormalizedFormalLogic-Foundation`, pinned at commit
`32e1a0956a8622fad067328ca1959729a7634428`, and a Lake lockfile pinning its
mathlib dependency. Foundation is registered directly as a source library so
the proof build does not load Foundation's unrelated documentation tooling.
The root Lake workspace exposes `PAUndecidable` and its audit as default
targets, but deliberately does not import them into the monolithic
`ProveIt.lean` facade: Foundation's `Vorspiel.Matrix` and mathlib's broader
linear-algebra surface both declare `Matrix.map`, so those two module worlds
cannot inhabit one Lean environment without changing vendored namespaces.

The Rocq project uses the repository submodule
`lib/Coq-Library-Undecidability-current`, pinned to the upstream Rocq 9.2
revision `9b626193c1e27901976d1dc4c9db01e68aee89ca`. Initialize submodules
before building a fresh clone. Its declared toolchain is Rocq Core 9.2.0 with
Rocq Stdlib 9.1.0.

## Verification

Lean:

```powershell
$env:LEAN_NUM_THREADS='0'
lake --dir Logic/PeanoArithmetic/Undecidable/Lean build
```

Rocq:

```powershell
Push-Location Logic/PeanoArithmetic/Undecidable/Coq
rocq c -Q ../../../../lib/Coq-Library-Undecidability-current/theories Undecidability `
  PAUndecidable.v
rocq c -Q ../../../../lib/Coq-Library-Undecidability-current/theories Undecidability `
  Audit.v
rocq check -Q ../../../../lib/Coq-Library-Undecidability-current/theories Undecidability `
  PAUndecidable Audit
Pop-Location
```

The audit modules print the assumptions of the headline results.
