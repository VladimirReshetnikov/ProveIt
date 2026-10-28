# Actual DagPerm–p215 internal control bisimulation — author record

Author: `controller_certificate`. The final 160-line main and 47-line Checks
are frozen. This records full author source/data review and bounded fresh
compilation, not an independent peer review. I read the complete proof text,
Checks and executed driver before compiling. The entire packed numeral was
decoded and round-tripped; its digits were not merely sampled.

The public `halts_iff` proves, in every model of IΣ1 and for every internal
nine-register file `x`,

```lean
(∃ t : V, ArithmeticDagControlPerm222.run t (liveValue 1 x) = 0) ↔
  (∃ t : V, ArithmeticControl215Table.run215 t (liveValue 1 x) = 0)
```

Both time witnesses range over the internal model. The proof instantiates the
accepted generic `ArithmeticControlBisim.halts_iff_of_check`, with the actual
represented register projections/writes, live-state coding, both accepted
table specifications and their run laws. Its generic positive segment clocks
and internal induction supply both directions. No table equality, certificate
validity, external-Nat conjugacy, standard-time bound, or structured-run premise
is supplied by a caller. It does not yet identify these numbered control runs
with the binary Turing machine. Actual EnumStep dispatch, tape/site/boot/clock
simulation, source-ZFC interpretation, Pell arithmetization and the final HA
proof remain separate obligations.

## Complete certificate

The fixed certificate contains 2,850 entries at fuel 6. Every entry has equal
control numbers and **two literal nine-element zero vectors**; these are not
empty lists. Entry zero has controls `(1,1)` and successor indices `(2,1)`.
The data were generated from the accepted complete DagPerm and p215 packed
tables, whose catalogue bindings are already kernel proved. The candidate's
canonical entry-list SHA256 is
`22677a305a6889a1d731f1d78467314bca4ae1f9a889705fffed70d61065b6db`.
The packed numeral has 273,590 bits / 68,398 hexadecimal digits, hexadecimal
SHA256 `9bc370253311f236e8c4a8276b88b5c8d4a7491060580a0dc01defd2864494a1`.

Forty-five kernel-checked blocks cover every valid index, including the final
34 entries. Each block checks `entryOK` itself, a bound below `2^86` for its
96-bit slot, equal controls, and both exact vectors. Thus positive entry
controls, fuel sufficiency, matching tests/offsets and both bounded successor
entries are checked against the actual tables. Generic quotient/remainder
composition supplies `check_all`; the finite metadata yields
`reserved_bits` and `entry_diagonal_offsets`. `packedCert_bound` separately
rules out bits beyond all 2,850 slots. `cert_outside` checks the total lookup
boundary. Checks include the final valid entry, first invalid entry, both root
successors, explicit vector length/nonemptiness, and both theorem directions.

The generator independently follows all certificate segments and decodes every
slot. The final freeze also checks the complete 45-block wiring and literal
identity across both attempts. These finite audits corroborate the kernel
proof; no `native_decide`, new INC-commutation lemma, omitted entry or cap
increase is used.

## Exact cache and execution

The import is only `ArithmeticControl215Table`. Its exact reachable closure is
141 custom modules including 95 Foundation modules, 426 recorded artifacts,
and 39 external boundaries; all were authenticated reuse. No prerequisite or
Foundation module was rebuilt. The accepted table provider is
`/tmp/control215-table-peer-_nt2n9b9/lib`, root acceptance `048399e422`.
Its root manifest is pinned at
`e09c83c858e0bef4e35a7cbf73c6bca04cc8fc6ccd1e701aa9048b2375a68768`.
The separate supplement retains the original historical 140-module first-leaf
plan and selects the accepted table object without rewriting that plan.
The already accepted DagControl/PackedTables root-provider supplement is also
retained.

The driver checks complete current source headers and the reachable import
graph, all selected sources/artifacts and boundary pins, actual first object
providers, and the pinned Lean 4.32.0 executable. Each invocation uses
`-M6000 -j1 -DElab.async=false`, one Lean thread, an explicit private `LEAN_PATH`
excluding the shared project cache, and the 512 MiB free-space guard. Outputs
are fresh regular nonsymlink files. The final attempt records 1,919 preflight
and 2,661 total observations over 738 distinct original paths; the durable
freeze repeats 2,966 checks across both attempts. These include repeated
observations, not additional dependencies or fresh closure compilation.

There were two attempts, both fully preserved. The first main exited normally
after 5.035 seconds with 45 missing-`Decidable` elaboration errors for the
per-entry shape predicate. A constructive instance by cases on `cert i` fixed
that inference issue. The certificate, all mathematical statements and imported
interfaces were unchanged. The generator/data audit retain their original
pre-fix source pin; the separate final data audit binds the final source and
proves that the entire literal is unchanged. The second fresh main/check pair
passed in 63.438 / 2.218 seconds, with an empty main log and maximum main RSS
1,984,808 KiB. No other failed attempts or diagnostics are omitted.

All eleven axiom reports are standard only. `root_controls` and `root_offsets`
are axiom-free; the finite entry checks and metadata use at most `propext` and
`Quot.sound`; the internal halting equivalence and its two clients additionally
use `Classical.choice` through the accepted generic theorem.

| Module | Source SHA256 | Object SHA256 |
|---|---|---|
| `ArithmeticControlBisimPerm215` | `3461125ae6452972b135a1c44edbacd5ab5e86455d2fc10a0a1e2d98edae1ca6` | `7f69aa45eb3aefb5d4c552cb6bcc9bbb6cea2847600ad9c3597e0afa8318f562` |
| `ArithmeticControlBisimPerm215Checks` | `d46a47ae2ca3552e0de87a50e300e63a64ec5da2bd977934ba62d2b3470233de` | `f314bf5216e22d4b44a0ae30dfeaf0cc61ad720f634af95306a4eb46c0acd27e` |

The final private provider is
`/tmp/control-bisim-perm215-controller-author-3xtztw47/lib`.
Replay packet `reviews/arithmetic-control-bisim-perm215-replay.json` has SHA256
`5771db7650be9a5b85a8e093b05f11b65d17b7d5abae9640ad8a2f314bc5d862`.
The 23-file manifest
`reviews/arithmetic-control-bisim-perm215-author-replay/FILES.json` has SHA256
`97da04e2f77d7e75e1b717daf1aafeadeb1026a4b43d2fdb53d0f32f349c7e9c`.
It preserves both attempts, commands, source snapshots, drivers, logs, timings,
objects, full data audits, supplements and authentication. No accepted source,
shared object, shared documentation or Git state was changed by this author.
