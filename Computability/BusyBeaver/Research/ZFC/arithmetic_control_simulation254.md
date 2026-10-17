# Concrete simulation of the represented literal control step

`ArithmeticControlSimulation254.lean` closes the local runtime obligations for
`ArithmeticControlStep254.stepValue`. In every `IΣ1` model, a valid related
coded control and whole binary frame satisfy two checked statements:

- a nonzero coded successor reaches a frame related to that exact successor
  after a positive internal binary clock;
- a zero coded successor reaches the actual binary halt after a positive
  internal binary clock.

The relation is the fixed Sigma1 `ArithmeticControlFrame254.Related`, which
requires a nonzero logical state and a valid actual catalogue control. Invalid
control0 is excluded. Thus the total evaluator's default output0 cannot be
mistaken for the literal halt opcode4. Validity of a live successor follows
from the resolver's `Fin 6460` result, rather than an additional invariant
assumed of an arithmetic key.

Six exact coded equations calibrate the actual source columns. Increment reads
the old selected physical register and then writes its successor. Decrement
branches on the old value: its zero case writes the same zero value and hence
preserves the packed file, while its positive case truncates by one. The
selector is the exact `physOf` image of the actual source's logical register.
Break and continue preserve the file and use the resolved path successor.
Actual halt yields zero. The proved finite opcode classifier excludes node
instructions and ensures that any zero step from a valid entry is that halt
case.

The binary side invokes the checked whole-frame source-case runtime theorems.
The same nine-field file, original values and exact resolved source appear on
both sides. Positive decrement's spare count increases once; overflow adjusts
the PC gap as specified by rebasing. These frame witnesses remain existential
internal values. No global register-size bound, standardness assumption for
register contents or first-exit theorem is introduced. The halt case retains
the actual site's literal final write/move.

The pinned Lean 4.32 check passed the 220-line source in 2.547956s and the
62-line audit in 2.075707s: ten ordered axiom probes, ten all-model caller
examples, standard axioms only and zero warnings. It reused 84 exact project
source/object providers and six external boundaries, with all 191 inputs
checked before and after. The fresh object remained unchanged after the audit.
Actual first Init and Omega providers are checked explicitly. No dependency,
coverage-guard or 82,552-step bootstrap replay occurred.

One source-failing attempt is preserved. Its local successor proof needed the
literal `false=true` condition reduced, and rewrite targets needed the
physical index written explicitly rather than through a definitionally equal
local `Fin` alias. The zero-file identity was also made an explicit equality
rewrite. These proof changes preserved every function, theorem statement and
option; they removed the failed attempt's four style warnings. The original
unbuilt preparation, failed and successful records, source/audit/driver
snapshots, source-first review and exact diffs remain separately archived.

A focused portable replay uses the matching whole-frame evidence:

```sh
python3 Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_simulation254.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/Proofs \
  --frame-evidence /path/to/arithmetic-control-frame254-verification.json \
  --output /outside/new-empty-directory
```

`--prepare-only` validates selected providers and snapshots the inputs without
compiling the source or audit; compiler-version discovery may run. Optional
cache/library paths must select objects with the recorded hashes. The portable
driver differs from the executed driver only in its final frozen default
source hash. Its maintained-default preflight is recorded as unbuilt. Repeated
rejection/relocation controls were explicitly waived for this unchanged guard
logic; this packet claims no such additional tests.

The remaining next runtime task is represented iteration and exact blank-entry
composition using the existing bootstrap and positive-clock transport theorem.
The relation of this numbered literal control interpreter to the all-internal
L2/Enum scheduler is a further separate obligation. This local simulation does
not yet prove the binary/validator equivalence in PA, and changes no machine,
calculus, instruction table or state bound.
