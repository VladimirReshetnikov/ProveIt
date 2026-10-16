# The exact public 330-step register prefix

16 October 2026. The new modules
[`RegisterPath.lean`](../../Lean/BusyBeaver/ZFC/RegisterPath.lean),
[`Prog254.lean`](../../Lean/BusyBeaver/ZFC/Prog254.lean), and
[`Prefix330.lean`](../../Lean/BusyBeaver/ZFC/Prefix330.lean) prove the finite
register computation used by the public 253-state reduction. This completes
the register-prefix item left open by [the binary bootstrap
certificate](finite253_lean.md). The binary/register runtime correspondence
remains open.

The imported semantics and all 6459 decoder-node pairs come from Jeff's
verification of Mira-Cult's machine, using Wade's TMBuilder framework:
busy-beaver commit `297ab8df7e5de329605c3875b4934643b371a5e3`,
`ZF/m254/coq/tm/{RM,Prog254}.v`. Their source SHA-256 values are respectively
`214a6016420e48f4432565ce97f1a27d07ac42642f8ed170d5d0ee02c5994ee8`
and `1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746`.
Both files are unchanged at mira-emmy's public
[PR20](https://github.com/jeff87654/busy-beaver/pull/20) head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`, whose
`ZF/m253/coq/tm/Boot253.v` supplies the attributed 330-step computation.
These are Lean ports and literal data imports, with no upstream Coq build
or imported Coq proof, and no relicensing of the upstream snapshot.

`RegisterPath` retains the exact source path semantics. Paths are MSB
first, and a decoder read beyond the stored path supplies zero. On finding
a leaf at depth `d`, execution first takes exactly `d` bits of the old path
with appended zeros. This truncation matters: the audited prefix truncates
the old path on 18 steps. Increment, decrement, break, and continue retain
the source conventions. A failed `run` may indicate halt or exhausted walk
fuel; the separate `Halts` definition therefore requires a literal halt
leaf, just as the source does.

The finite executor stores registers in a list, reads zero outside it, and
zero extends a list on an out-of-range write. `read_writeRegisters` proves
these writes agree at every natural-number index with the infinite register
update. `finiteStep_sound` and `finiteRun_sound` then prove agreement with
the actual `Nat → Nat` semantics for every program and execution length.
The finite certificate is consequently about the full register vector.

`Prog254` preserves every pair in its original DFS order, with original
node numbers beside the literal pairs. Balanced blocks make kernel lookup
inexpensive. Their cached sizes are checked, and `lookup_eq_flatten` proves
agreement with the flat nth-row lookup for every index, including the
original `(halt, halt)` default beyond the table. Kernel facts check all
6459 rows, all node targets below 6459, all register operands below 9, and
the single literal halt leaf. The different published 219-node structured
Wade DAG is not substituted for this decoder.

`Prefix330.prefix330` proves, starting from empty path and register 0 equal
to 2 with every other register zero:

```text
RegisterPath.run Prog254.program 330 Prog254.initial
  = some (path 000, registers [5,0,0,0,2,0,0,0,0] followed by zeros).
```

The underlying finite-data equality is checked by kernel `decide`, then
transferred through the generic soundness theorem. Separate theorems give
the nine projections, the entire zero tail, and the next decoded leaf:
decrement register 8, at depth 3. The public physical register permutation
`[2,4,3,7,6,8,0,1,5]` gives `[0,2,0,0,0,0,5,0,0]`, the primary-register
values appearing in `Boot253`. This numerical agreement does not establish
an instruction simulation. The 158 additional tape blocks retained by
the binary bootstrap, including its two nonzero spare blocks, are not
extra logical registers of the RM configuration.

[The verification record](results/rm330-verification.json) preserves the
source identities, exact commands, fresh-source checks, axiom audits, and
a checked caller. All three new modules depend only on each other and
Lean's standard library; the finite certificate needs no other repository
cache. A standalone replay from the repository root is:

```sh
set -e
task_scratch=$(mktemp -d /tmp/zfc-rm330-check.XXXXXX)
mkdir -p "$task_scratch/BusyBeaver/ZFC"
export LEAN_PATH="$task_scratch"
for module in RegisterPath Prog254 Prefix330; do
  lean +leanprover/lean4:v4.32.0 -o "$task_scratch/BusyBeaver/ZFC/$module.olean" \
    "Computability/BusyBeaver/Lean/BusyBeaver/ZFC/$module.lean"
done
```

The fresh three-module replay passed without warnings in 45.6 seconds on
**Lean 4.31.0**; the register certificate itself compiled in 4.6 seconds.
The runner initially mislabeled this as 4.32.0: it queried the version in
the repository, but ran the compiler in a scratch directory, where elan
selected the global 4.31.0 default. All three emitted `.olean` headers
confirm 4.31.0. That evidence is retained and corrected. A fresh replay
with the explicit pinned 4.32.0 executable now passes all three modules in
29.42 seconds, followed by all 17 axiom audits, the caller and the updated
umbrella. Replay commands pin the toolchain on each invocation. The final
verification record uses this 4.32.0 run as its primary evidence.
The final infinite-register
theorem uses only the standard `propext`, `Classical.choice`, and
`Quot.sound` axioms; the finite prefix equality uses only `propext`.
An independent read-only review also found no source-fidelity or contract
defect, and independently compared all 6459 pairs and the block order.

The evidence also checks each imported pair and its original index against
the pinned vendored source, and checks the order of all 101 block references.
This source-import comparison is an external data audit; the kernel proves
the stated facts about the literal Lean data and its execution.

There are no admissions, custom axioms, or native evaluation oracles.
This certificate does not prove the complete binary runtime simulation,
any first-arrival property, the proof enumerator/calculus bridge, or a
consistency equivalence in Lean or PA.
