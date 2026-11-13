# Guarded low-priority 76Y graph compilation

The fourth attempt compiled the generated `P64QCube76Y` definition with
Lean exit 0 and an empty log. It is a check of the **graph definition only**;
it does not establish either positive-zero direction, an iPRA endpoint, or
JSON/PDF semantics. The source, Lean executable and direct captured `P64Graph`
object and companion hashes were checked before and after; full transitive,
dynamic and historical provider ancestry remains inherited.

The successful [receipt](observations/attempt04/result.json) records
`-M2400`, nice 19, idle I/O priority, a 120-second bound, and sampled stops
at 3.5 GiB process-group RSS and 10 GiB `MemAvailable`. It recorded 9 group
RSS samples, with sampled maximum 2,041,397,248 bytes and minimum available
memory 18,808,905,728 bytes; neither stop fired. These are observations at
sampling instants, not hard RSS or available-memory reservations. The output
object is `/tmp/p64-qcube76y-priority-check04/P64QCube76Y.olean`, SHA-256
`fab5716c55ab761f1c6e7b644d8c1063da766629613fe5a48c465b5529c5f822`.

Earlier attempts are retained:

1. [Attempt 1](observations/attempt01/result.json) exited −6 with a
   thread-creation exception under a 2 GiB address-space limit. Its exact
   cause and elaboration stage are not proved; the recorded 11 MiB is only a
   sampled RSS value. No object was produced.
2. [Attempt 2](observations/attempt02/result.json) exited −6 with Lean's
   `-M1500` interpreter memory exception. No object was produced.
3. [Attempt 3](observations/attempt03/result.json) had Lean exit 0 and an
   object, but the RSS monitor reported a missing child at process exit; the
   runner correctly marked the attempt FAILED, so it is not accepted as a
   guarded check.

The final runner waits briefly if a group sample misses the child: a child
that completes is distinguished from one still alive but unmeasurable, which
causes failure. It also refuses success if process-group members remain after
the leader exits. The synthetic [sampler controls](sampler-control.json)
passed both finished-child and live-unmeasurable cases without launching Lean.
Only the extra check's own process group is ever sent a termination signal.
The check was run alongside the separately managed current14 rebuild.

## Generic bounds

The corrected `IndependentYBounds.lean` passed its third bounded check: Lean
exit 0, four `[propext, Classical.choice, Quot.sound]` reports, no warnings or
`sorryAx`, and stable direct guards. The [successful receipt](observations/bounds-attempt03/result.json)
and [log](observations/bounds-attempt03/compile.log) record 80 RSS samples,
with sampled maximum 2,129,199,104 bytes and minimum `MemAvailable`
18,789,101,568 bytes; neither stop fired. Its object is
`/tmp/p64-qcube76y-bounds-priority-check03/IndependentYBounds.olean`, SHA-256
`6458991845eba747546b4d45c454a31a907e226a98fbb7301d6cf30ae41da582`.
This proves the generic model lemmas, not their graph-specific hypotheses or
either witness direction.

The retained [first](observations/bounds-attempt01/compile.log) and
[second](observations/bounds-attempt02/compile.log) checks exited 1 with
source errors; the second report contained `sorryAx` in the unresolved
strong-bound theorem. Both exact source versions are preserved alongside
their receipts. The successful third source SHA-256 is
`7ac6662b3b6055cb30091b0d9feb958a76246381207028dc45cbf8890db69744`.

To repeat, choose a fresh output path in a copy of `check_graph_final.py` and
coordinate the single additional Lean slot; do not overwrite prior evidence.

| Artifact | SHA-256 |
| --- | --- |
| `check_graph_final.py` | `b9f8b17cf786092506cffe6e2825a6ccefb254043e337052ffe508e4e42e7d41` |
| `missing_child.py` | `c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1` |
| `check_sampler.py` | `f581e81b4002872534c2b1a47cd7a3fed34fb1714fd87ed1b32871aac3af57a1` |
| `sampler-control.json` | `af53917bb5ac0e7d9376218be9c2b7d551ba3a1f49fc9d3987a67fe635883a7d` |
