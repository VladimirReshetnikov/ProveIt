# Internal positive-clock transport

[`ArithmeticPositiveSimulation254`](../../Lean/BusyBeaver/ZFC/ArithmeticPositiveSimulation254.lean)
proves a conditional simulation theorem in every IΣ1 model. Once its local
simulation premises are supplied, logical and binary halting are equivalent.
The logical run, binary run and simulation relation must be Σ1 definable.
All clocks and configurations are internal model elements.

The Σ1 induction invariant is

```text
exists clock >= n, Related(logicalRun(n), binaryRun(clock, initial)).
```

Every continuing logical step advances the binary clock by a positive
amount. If the logical run never halts, the simulation therefore reaches
beyond any proposed binary halting time. Binary halt persistence would then
contradict the activity of a related configuration. Conversely, a logical
halting step supplies a binary halting witness through the local halt
premise. The argument requires no upper bound on the cumulative clock.

The explicit premises include zero and successor equations, binary
additivity, an initial related pair, live/active related states, continuing
and halting local simulations, and halt persistence. The concrete 252-state
runtime has **not** yet been shown to satisfy these internal premises. This
module supplies the final clock-composition argument, not the binary bridge
or a PA consistency equivalence.

The [fresh check](results/arithmetic-positive-simulation254-verification.json)
passes four axiom reports and four callers, with only standard Lean axioms
and no warnings. Eleven exact Cantor prerequisites and four external
providers are reused. The [independent review](results/arithmetic-positive-simulation254-review.json)
checks the full proof, audit, dependency closure and final evidence. Earlier
notation, section-hypothesis and comment-placement failures are retained.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_positive_simulation254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --refutation-evidence /outside/successful-refutation-word/verification.json \
  --output /outside/new-empty-positive-simulation-check
```

The refutation-word record supplies only the selected Cantor dependency
objects. No compiler or refutation theorem is imported. Maintained-default
preparation is recorded separately and invokes no Lean process.
