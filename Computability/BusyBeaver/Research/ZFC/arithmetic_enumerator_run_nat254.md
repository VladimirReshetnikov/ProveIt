# Ordinary-Nat scheduler execution

[`ArithmeticEnumeratorRunNat254`](../../Lean/BusyBeaver/ZFC/ArithmeticEnumeratorRunNat254.lean)
proves exact agreement of the represented scheduler iteration with the literal
`Enum254.run` for every ordinary Nat time and all six native fields, including
arbitrary dirty registers. The semigroup law rewrites the arithmetic successor
to execute the first step before the remaining run; the actual native
one-step adapter then supports induction on ordinary time.

Scalar 0 means native `none`; all live native states encode positively. The
adapter recovers an actual reachable halting edge from native `run=none`,
and maps each native halting edge to `none` one tick later. Consequently
`∃ time, arithmeticRun time 1 = 0` is equivalent to the existing
`Enum254.Halts`, since the literal zero six-register state encodes as 1.

The [fresh source/audit check](results/arithmetic-enumerator-run-nat254-verification.json)
passes eleven ordered axiom reports and fourteen callers with standard axioms
only and zero warnings. It identifies all 72 inputs, 27 exact project
source/object prerequisites and four external providers, with before/after
hashes and the fresh object captured before audit. The
[independent review](results/arithmetic-enumerator-run-nat254-review.json)
checks the full source, audit, native halting definition and exact artifacts.
External dependency caches are reused with identified hashes. Maintained
portable preparation is separate from this successful Lean check.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_enumerator_run_nat254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --run-evidence /outside/successful-enumerator-run/verification.json \
  --output /outside/new-empty-enumerator-nat-check
```

This adapter concerns ordinary natural numbers. It does not identify
nonstandard internal times with external finite runs. Reverse internal
soundness, binary-machine transport in PA and the PA consistency equivalence
remain separate obligations. The original draft record is preserved as
unbuilt history.
