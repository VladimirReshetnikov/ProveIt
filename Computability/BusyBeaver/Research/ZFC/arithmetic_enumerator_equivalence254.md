# PA proves the validator–scheduler equivalence

[`ArithmeticEnumeratorEquivalence254`](../../Lean/BusyBeaver/ZFC/ArithmeticEnumeratorEquivalence254.lean)
proves this fixed arithmetic sentence in IΣ1 and PA:

```text
(exists code, valueDef(2, code)) iff (exists time, runDef(0, time, 1)).
```

The left side says that the original C254 validator accepts a proof of
falsity. The right side says that its represented scheduler halts from its
actual blank logical configuration. The proof establishes that scalar 1 is
`liveValue 0 0 0`; validator result 2 is the accepted falsity marker.

The reverse direction is proved in
[`ArithmeticEnumeratorSoundness254`](../../Lean/BusyBeaver/ZFC/ArithmeticEnumeratorSoundness254.lean).
Its Σ1 time invariant retains an accepted falsity proof after scalar-zero
halt, and otherwise carries one bounded certificate for the actual top,
cache and stack. The nonzero guard distinguishes a running configuration
from the absorbing halt. Both scheduler branches use
[local command preservation](arithmetic_command_preservation254.md).

Soundness requires certified initial working fields. It applies to zero
working fields at arbitrary pointers and candidate indices. The
[forward theorem](arithmetic_enumerator_refutation254.md) allows arbitrary
working fields and starts at pointer/candidate zero. Together they give the
blank equivalence. Every code and time ranges over the arbitrary IΣ1 model;
arithmetic completeness and weakening yield the stated derivations.

Both new sources and audits passed their first Lean check: nine axiom reports
and ten callers for soundness, five reports and seven callers for composition.
The checks use only standard Lean axioms and emit no warnings. The
[full verification record](results/arithmetic-enumerator-equivalence254-verification.json)
identifies 46 reused project providers and four external providers. The
[independent reviews](results/arithmetic-enumerator-equivalence254-review.json)
cover the final sources, audits, exact dependencies and portable checker.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_enumerator_soundness254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --preservation-evidence /outside/successful-command-preservation/verification.json \
  --forward-evidence /outside/successful-enumerator-refutation/verification.json \
  --output /outside/new-empty-scheduler-equivalence-check
```

Maintained-default and relocated-repository preflights invoke no Lean process
and are recorded separately from the successful proof check. Internal binary
execution and the translation between ZFC proof codes and the C254 validator
remain open. The requested PA consistency equivalence for the 252-state blank
machine is therefore still unfinished.
