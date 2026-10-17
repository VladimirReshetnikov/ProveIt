# Complete actual DROP in internal arithmetic

`ArithmeticControlDrop254` proves the complete literal DROP instruction and
its AC=1 dispatcher entry in every model of IΣ1, for arbitrary internal register
values with both scratch registers initially zero. DROP returns to the actual
fetch control with

```
TW := old cache
WS := cantor(old TW, old WS).
```

All other fields, including the cache and scratch fields, retain their values.
The dispatcher composition additionally clears AC. The theorem supplies a
positive internal logical runtime, which may be nonstandard.

The proof composes the checked transfer, copy and pairing contracts. The two
prefix transfers move TW to scratch1 and WS to TW; pairing followed by the
scratch2-to-WS transfer pushes the original pair and clears TW. The cache
copy/restore then adds the cache to TW, preserves the cache and clears scratch1
in exactly `7*cache+2` logical instructions. One final literal break returns
to fetch. Every loop and continuation is bound to the actual program through
its walk and resolver equations. No new unbounded induction is needed.

The source and focused audit passed 12 ordered axiom probes and 18 callers
with only `propext`, `Classical.choice` and `Quot.sound`. Source checking took
4.966 seconds and the audit 2.176 seconds. Eleven unused-simp source warnings
remain; the audit has none. The first source attempt failed at an unavailable
finite-cases tactic and a conditional simplification. Explicit register cases
and a direct conditional rewrite repaired those proofs without changing their
statements, imports or limits.

The checker matched 96 project prerequisites, six external boundaries and 215
inputs before and after checking. It saved the fresh source object hash before
the audit and verified it afterward. Both commands used one thread, 4 GiB,
default Lean limits and a 120-second timeout. Dependencies, site guards and the
bootstrap were not rebuilt or replayed.

The exact PASS record, failed attempt, source/audit/guard snapshots and repair
diffs are retained separately. Independent review checked the mathematics,
existing kernel evidence, actual providers and maintained files. The portable
guard equals the executed guard byte for byte. Its maintained-default
preparation queried the compiler version but compiled no proof.

The complete MP and AX branches, internal interpreter-to-Enum connection and
final PA equivalence remain open. This contract does not assert a first-exit
property, an exact binary clock or a smaller state count.

```sh
python Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_drop254.py \
  --repo "$PWD" --dependency-root /path/to/pinned/Proofs \
  --pair-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-pair254-verification.json \
  --output /external/fresh/drop-check
```
