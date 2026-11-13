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
* The first 32 extracted instructions and ordinal 3692 agree with the actual
  `PA196.Program.sites` resolver in Lean. The checker rebuilds the resolver
  modules from the pinned upstream sources and also checks that the archived
  and upstream `Program.lean` files have the same hash.
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

The source-run result is **conditional**: `Closed` has not been proved for the
archive certificate. The generated checks are separate closed facts, and the
extraction of the remaining 3,779 source instructions has not been bound to
`Program.sites` in Lean. The generated chunks have not yet been assembled into
the universal `TableClosed` hypothesis for an extracted instruction table.
No correspondence between the assumed source seed and a blank-tape run is
proved here. This also does not establish any
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
`sorryAx` in those printed results. In the initial local run, the 3,812
bitset checks took about nine seconds; rebuilding the source resolver and
checking the other results adds time and memory use.
