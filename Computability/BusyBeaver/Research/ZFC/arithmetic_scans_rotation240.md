# Internal tape scans for the exact 240-state machine

[`ArithmeticMachineScansRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticMachineScansRotation240.lean)
proves single-row and bidirectional scan contracts for the exact arithmetic
evaluator. States, lengths and both complete numeric tape halves may be
arbitrary elements of an IΣ₁ model. Read and written bits may differ.

For example, the rightward contract is

```text
runFrom n (frame q left (bitPrefix read n right)) =
  frame q (bitPrefix write n left) right
```

Its explicit premise is the corresponding self-loop row in the actual
240-state lookup. The leftward version uses the recentered `leftFrame` codec.
Π₁ induction quantifies over both complete tape halves. Numeral variants lift
finite row equations to every model. These are exact endpoints; they make no
claim that the machine exits the scan state at that time.

The source reuses the generic prefix, frame and action-decoding algebra from
the checked Perm252 development. All execution statements use the Rotation240
lookup and run. The audit includes four actual unchanged scans, three writing
scans, and the terminal row's complete write-one/right-move effect.

The [actual check](results/arithmetic-scans-rotation240-verification.json)
passes 13 axiom probes and 15 typed callers with zero warnings and standard
Lean axioms only. Source compilation took 7.894 seconds and the audit 2.592
seconds, sharing 120 seconds, one thread and 4,096 MiB with default proof limits.
The first source compilation also passed; its audit needed an explicit
`Nat.cast_one` conversion in one caller. The second attempt changes only that
caller. Both attempts and the exact correction remain in the history.

The actual parents are RunFromRotation240 and the older uniform Perm252 scans.
The selected boundary contains 33 project prerequisites, four direct external
pairs, one retained external pair, and Init/Omega. All 222 recorded inputs,
first providers and the new source object were checked before and after the
audit. The legacy parent's nondefault proof limits and absence of a recorded
pre-audit capture/deadline remain explicit; this check does not retroactively
add those guarantees. Dependencies were reused without a rebuild.
The [completed-run review](arithmetic-scans-rotation240/review.json) checks the
source scope, correction and actual evidence, and discloses that the reviewer
authored the initial guard. Its [history](arithmetic-scans-rotation240/review-history.json.gz)
preserves the reader and review notes.

The [publication record](results/arithmetic-scans-rotation240-publication.json),
[guard, audit and raw logs](arithmetic-scans-rotation240/), and
[history](arithmetic-scans-rotation240/history.json.gz) preserve the execution
evidence. The records retain historical scratch paths and do not constitute
a clean-checkout build package.

These lemmas supply the scan layer for the
[internal binary/register bridge](rotation240_pa/w6-route/README.md).
The register-box contracts, complete simulation and PA consistency equivalence
remain open. Attribution follows Mira-Cult, Jeff Ketchersid, Andrew James Wade
and the ProveIt arithmetic proofs.
