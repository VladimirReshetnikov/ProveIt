# Zero-mask certificate prototype

The incoming `pa_tm_extended_research_2026-11-13.zip` contains a proposed
source-level zero/nonzero invariant for PA196. For each of 3,812 source
ordinals, its certificate lists a set of nine-bit masks, encoded as a 512-bit
integer. A bit of a mask represents whether the corresponding source register
is positive. The archive uses the invariant when analyzing four closing-command
variants of PA196.

`check.sh` extracts three pinned archive members into a private temporary
directory. It executes the pinned archive parser to extract source instructions
and generates Lean files for the following kernel checks:

* 477 independently proved, eight-ordinal chunks check the certificate's
  bitset transfer tests for all 3,812 extracted instructions. For an increment,
  they set the relevant bit; for a zero decrement they retain the mask; for a
  positive decrement they allow the bit to remain set or become clear; and for
  a jump they retain the mask. Halt imposes no successor test.
* `Transfer.lean` proves generic soundness lemmas for bitset inclusion and each
  increment and decrement transfer case. The seed mask 1 is present at ordinal
  25. At ordinal 3692, each recorded mask has bits 3, 4, 5, and 6 clear.
* The first 32 extracted instructions and ordinal 3692 are checked directly
  against the actual resolver. Separate bounded checks prove equality of the
  entire segmented lookup with `PA196.Program.sites` resolution, including
  ordinals outside the source table. The checker rebuilds the upstream resolver
  and verifies that archived and upstream `Program.lean` hashes match.
* `Abstraction.lean` defines a Boolean positivity mask for actual source
  register stores and proves that its nine-bit numeric encoding has exactly
  those bits. Given an explicit `Closed` hypothesis for the source resolver,
  the invariant holds along every finite `M6.Source.Semantics.Steps` run.
  `Conclusion.lean` applies this result conditionally: if the certificate agrees
  with the archived masks at ordinals 25 and 3692 and satisfies `Closed` for
  `PA196.Program.sites`, a source run starting at ordinal 25 with register 0
  equal to 2 and the others zero reaches ordinal 3692 only with registers
  3, 4, 5, and 6 zero.
* `MaskEncoding.lean`, `MaskSets.lean`, and `CertificateBridge.lean` prove
  that the bitset transfer checks imply `Closed`, conditional on two explicit
  assumptions: a `TableClosed` proof of the checks for every relevant row in
  an extracted instruction table, and equality of that entire table with the
  source resolver. The proof checks the finite encoding identities in Lean.
* The generator also builds the extracted table and the archived masks as
  arrays of blocks of 16, together with bounded Lean row-check modules.
  `SegmentAssembly.lean` and the generated `SegmentAll2.lean` assemble them
  into an unconditional `TableClosed` theorem for that extracted table.
  The generated `ResolverBinding.lean` proves the required equality with the
  upstream resolver, so `SegmentEnd.lean` proves the ordinal-3692 result for
  actual source runs without a table-binding hypothesis. It also proves that
  every reached ordinal-26 frame has registers 3, 6, and 7 zero, and hence that
  a decrement of register 6 with zero successor 34 has the same source effect
  there as the original jump to 34.

The final Lean theorem is a standard-natural-number statement about the source
program under `M6.Source.Steps`, whose exited control is absorbing. A bridge to
the cyclic driver (`CycleSteps`, which restarts after a normal exit) has not
been proved here. No correspondence between its source seed and a blank-tape
run is proved here. This also does not establish any
physical-machine simulation, equivalence between the
four variants and PA196, iPRA theorem, or PA consistency result. Hash checks
and the archive's parser are part of the reproduction procedure, not Lean
theorems.

Run from the repository root with Lean 4.32.0 and the root Lake environment:

```sh
bash Computability/BusyBeaver/Research/PA/pa196-vs-u208/archive-audit/zero-mask/check.sh
```

The generated certificate code is kept in the temporary directory, not in
the repository. The check prints selected axiom dependencies and rejects
`sorryAx` in the recorded results. The bounded row modules are checked in
separate Lean processes, using two workers by default; set `PA196_ZERO_JOBS=1`
to use one. Set `TMPDIR=/dev/shm` to keep their temporary files in memory when
that directory is available. Checking all rows can take several minutes.
