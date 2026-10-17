# Composable arithmetic dispatch entries

`ArithmeticDispatchRebasePerm252.lean` proves that one actual accepted instruction
reaches the next canonical arithmetic Site entry. It rebases the entire numeric
tape, retains the updated registers and spares, and derives both the next leaf's
acceptance and its exact `follow` equation for the literal `Prog254.program`.

The preceding Site theorem ends at `Site.target P overflow effect`. That target
is not automatically the next `Site.start Q`: the decoder may consume a shorter
or zero-extended path. Here the complete finite PC region is represented by

```text
padded P budget = P ++ replicate (budget - P.length) false
budget overflow = 40 + overflow.toNat
```

Equality of these padded regions implies equality of the whole arithmetic
frames. The effect is absorbed into the new physical register list. Increment
adds one to the selected original value; the raw decrement effect subtracts
one and increments the zero-spare count exactly once. The new gap is
`gap + digit overflow`. Continue preserves it, since its overflow flag is false.
All numeric register values, counts, gaps and execution clocks range over the
IΣ1 model. The finite path and operation syntax remain external.

The next padding equality is derived from actual program facts. The imported
closed coverage theorem supplies the next walk and its accepted consumed path.
`RegisterPathClean.gap_consume` turns the clean outgoing path into the complete
padding equality. Outgoing cleanliness is derived from `execute_clean` for the
actual operation. A dummy Nat register file with value zero or one selects the
same decrement branch in that pure path theorem; no internal register value is
converted to an external natural or required to be standard.

The resulting contracts cover increment, zero and positive decrement, break
and continue. Each gives a positive internal clock, exact updated canonical
frame, next accepted site and next actual `follow` premise. The current leaf's
actual `follow` equation and accepted check remain explicit hypotheses. Final
halt soundness is supplied by the preceding Site module.

The two initial-entry theorems close a necessary bootstrap detail. `Site.start []`
starts with blank PC bits and is not itself a fully consumed leaf. Its entire
numeric configuration equals the first accepted all-zero consumed entry.
Composing this equality with the checked bootstrap reaches that actual accepted
leaf at the same 82,552-step clock; no additional binary steps are inserted.

This is composable single-instruction refinement with external finite control
syntax. A represented variable-PC state/run, numeric finite-control transition
representation, logical-register/scheduler correspondence and whole internal
binary runtime remain separate. No new PA endpoint, state reduction or machine
mutation is claimed. Mira-Cult, Jeff and Wade retain their attribution.

## Verification

The focused final source/audit check passed 16 ordered axiom probes and 18 caller
examples with only `propext`, `Classical.choice` and `Quot.sound`. Neither command
produced warnings. The official absolute Lean 4.32.0 compiler used one thread
and a 4 GiB limit, taking 2.953 seconds for the source and 2.514 for the audit.
All 180 selected inputs were checked before and after, together with the fresh
object. Exactly 78 checked project modules, six external boundary providers and
the actual first `Init` and `Omega` providers were reused. No dependency was
built or downloaded. No coverage chunk, guard or bootstrap was replayed.

The original first attempt had the initial 14-probe/16-caller scope and failed
only because the Foundation subtraction operation makes `effectValues`
noncomputable. Its driver and record remain unchanged. After that failure,
`initial_entry` and `internal_boot_entry` were added and independently reviewed,
with two probes and two callers. A separate driver records the expanded final
16/18 scope. The only other source edit was the `noncomputable` marker.

The successful record is preserved byte for byte in
[the verification record](results/arithmetic-dispatch-rebase-perm252-verification.json).
[Publication metadata](results/arithmetic-dispatch-rebase-perm252-publication.json)
keeps the original failed scope distinct from the final proof, maintained-default
preparation and guard controls. Those metadata checks perform no source or
audit proof compilation; compiler discovery may invoke `lean --version`.

```sh
python3 Computability/BusyBeaver/Research/ZFC/check_arithmetic_dispatch_rebase_perm252.py \
  --repo "$PWD" \
  --dependency-root /path/to/built/Proofs \
  --boot-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-site-boot-perm252-verification.json \
  --native-evidence Computability/BusyBeaver/Research/ZFC/results/command-word254-integration-verification.json \
  --output /outside/empty/dispatch-rebase-check
```

The dependency root must contain the pinned already-built Foundation/Mathlib
providers. `--prepare-only` checks identities without proof compilation.
Optional `--cache` and repeated `--library-path` arguments relocate checked
objects only when their selected source/object hashes still match. This is a
fresh check of the new module and audit, not a fresh build of all dependencies.
