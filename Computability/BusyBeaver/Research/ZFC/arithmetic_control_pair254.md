# Internal pairing and its actual DROP/MP occurrences

`ArithmeticControlPair254` proves that the literal Cantor pairing routine
terminates on every internal register file in every model of IΣ1. It clears
scratch1 and TW and adds `cantor(oldScratch1, oldTW)` to scratch2, preserving
every other field. The initial scratch2 value is arbitrary; a pure pair output
requires it to start at zero.

The source also gives reusable transfer and two-target copy contracts with
exact logical runtimes `3*n+1` and `4*n+1`. Their finite shapes record actual
control edges, logical/physical register bindings and disjointness conditions.
The copy inside pairing writes scratch2 first and scratch1 second.

A positive pairing cycle maps `(a,b,z)` to `(0,a+b-1,z+b+1)` in
`4*b+3*(a+b)+2` logical instructions. The zero case exits in two instructions.
The termination proof uses a bounded Σ1 induction with the original file fixed,
an existential elapsed clock, and the invariants `a+b+t=N` and
`z+cantor(a,b)=Q`. Its counters and witnesses may be nonstandard.

Both actual occurrences are bound to the literal program through its catalogue,
walk and resolver equations: DROP controls 6346–6355 reach 6356, and MP controls
6373–6382 reach 6383. These are the pairing portions of those instructions;
the complete DROP/MP contracts require further composition.

The third source attempt and focused audit passed all 13 ordered axiom probes
and 18 callers, with only `propext`, `Classical.choice`, `Quot.sound` and zero
warnings. Source checking took 14.848 seconds and the audit 2.429 seconds.
Two earlier source failures are retained: explicit unfolding of local values
and actual shape projections repaired elaboration, with no limit increases or
changes to the mathematical contracts.

The checker matched 95 project prerequisites, six external boundary providers
and 213 inputs before and after compilation. It recorded the new object before
the audit and checked it unchanged afterward. Commands used one thread, 4 GiB,
default Lean limits and a 120-second timeout. No dependencies were rebuilt or
downloaded, and neither bootstrap nor site guards were replayed.

The successful verification record is copied byte for byte. History preserves
all three attempts, exact source/audit/driver snapshots, repair diffs and
preparations. The independent child review covered the initial unbuilt draft;
the root reviewed the repairs and final kernel evidence. The portable checker
is identical to the successful executed checker. Its maintained-default
preparation queried the compiler version but compiled no proof.

This supplies local interpreter contracts. The complete interpreter-to-Enum
connection, reverse internal proof translation, internal L schemas and final
PA equivalence remain open. It establishes no smaller state count.

```sh
python Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_pair254.py \
  --repo "$PWD" --dependency-root /path/to/pinned/Proofs \
  --unpair-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-unpair254-verification.json \
  --output /external/fresh/pair-check
```
