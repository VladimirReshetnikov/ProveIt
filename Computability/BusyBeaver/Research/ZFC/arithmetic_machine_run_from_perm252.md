# Binary execution from arbitrary internal configurations

[`ArithmeticMachineRunFromPerm252`](../../Lean/BusyBeaver/ZFC/ArithmeticMachineRunFromPerm252.lean)
iterates the actual frozen 252-state step from any numeric configuration.
Its fixed Σ1/Δ1 graph is total for every time and initial configuration in
every IΣ1 model. Scalar 1 recovers the existing blank run at every internal
time.

The iteration satisfies zero, successor, first-step and addition equations.
A configuration whose state projection is zero remains exactly the same
configuration, including its entire tape. Invalid positive state codes retain
the existing step's behavior; they are not identified with halt.

A separate IOpen lemma evaluates every fixed natural lookup key in every
model using the same literal table. It supplies the static transition facts
needed by unbounded tape-scan proofs. On ordinary natural inputs, the new
iterator agrees with iteration of the already checked native numeric step.

The [fresh check](results/arithmetic-machine-run-from-perm252-verification.json)
passes nineteen axiom reports and twenty callers, with only standard Lean
axioms and no warnings. It reuses 24 exact project prerequisites, four external
providers and the identified toolchain Omega provider. The
[independent reviews](results/arithmetic-machine-run-from-perm252-review.json)
cover the final source, audit, exact provenance and portable checker. The
first source attempt's numeral-key simplification failure is retained.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_machine_run_from_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --machine-evidence /outside/successful-arithmetic-machine/verification.json \
  --output /outside/new-empty-machine-run-from-check
```

The checker accepts the full successful machine-arithmetic record or its
compact published record, with explicit relocation options for evidence and
objects. Maintained-default and relocated preflights invoke no Lean process.
Neither this iterator nor its Nat adapter proves the all-internal runtime
simulation. That remains necessary to instantiate the
[positive-clock transport theorem](arithmetic_positive_simulation254.md).
