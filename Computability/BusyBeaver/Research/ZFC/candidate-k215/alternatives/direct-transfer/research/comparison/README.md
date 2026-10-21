# Independent finite review of ST215

This folder contains two independent audits of the final append-zero ST215
candidate and all their inputs. It uses only the Python standard library. No
code from an incoming ZIP is executed by these audits.

Run, from any working directory:

```sh
python3 -B /path/to/compare-portable/run_audits.py
```

Use `--out /path/to/results` to select the output directory. Assertions must be
enabled; Python `-O` is explicitly rejected. The saved results are in `evidence/`.

## Exact candidate and source

| Object | SHA-256 |
|---|---|
| Final native table | `d5237504325eee96b0040d4d9574731a1caf4bcda3d6a49e94827d9532a664e1` |
| Final source leaves | `212cf0ffde43c1cc22c183dd8bf0b3a699396f96c9942ee92a7cc372cd273ca9` |
| Context-root reference source | `19074981026ca9a46030f13ac57231f5b5131c7d826cf02739bf232ede591ba8` |
| Canonical rooted transition graph | `28eceb93cebfd2529c9140f0bf6c6d7c3bf110f921cf584958caa61efa5e02f4` |

The table has **215 working states**, **430 specified transitions**, native start
state **0**, and halt target **254**. All 215 working states are reachable in the
transition graph. This graph reachability statement allows arbitrary sequences
of read symbols; it does not assert that each state is reached on the blank tape.
The append-zero action is explicitly checked as native row `198/0 = 0 L 40`.

## Source and physical prefix binding

The source has **4,732 primitive leaves**, **4,731 internal tree prefixes**, and
**201 distinct DAG nodes** when structurally identical subtrees are shared.
Its maximum depth is 44 and its longest zero run is 6. A direct reconstruction
of the primitive control-flow graph gives **6,150 directed edges**.

The new source preserves both the complete ordered primitive word and the
complete primitive control-flow graph of the pending context-root short-transfer
source. The audit derives branch targets from binary increment and the relevant
zero/one strip operations; it does not trust supplied edge lists. For every
internal source prefix, it executes the actual table from dispatcher state 84
on that known prefix and checks that the head reaches its end without changing
the tape. It records the ensuing leaf-entry actions for every primitive.

This is an exact finite source/table binding check. The code stops at primitive
entry; arithmetic execution on unbounded registers is covered by the separate
symbolic runtime work in the main packet.

## Material difference from supplied 215-state tables

The corpus contains **78 distinct table byte files**, appearing under **332
original names**, extracted from the 12 incoming ZIP archives (recursively
including nested ZIP members) and the pinned repository's `candidate-k215`
directory. The repository HEAD recorded for this comparison is
`75716498437bfc7291d5900cab2983a11fd54bac`.

The tables are copied verbatim into `comparison-inputs/`, one file per SHA-256.
`comparison-inputs/provenance.json` records every original archive/member name,
the outer archive hashes, the repository location and pinned HEAD. Thus no
original ZIP or repository checkout is required to replay the comparison. Some
corpus entries are rejected experiments; inclusion in this corpus is not an
endorsement of their runtime or logical correctness.

For each table, the audit attempts the unique mapping forced by the start state,
halt state, ordered read-symbol branches, write symbols, and head directions.
It also tries reversing every head direction in the comparison table. Every
comparison fails, both directly and after reflection. Each failure is recorded
with a finite distinguishing read word or forced-map/injectivity obstruction.
An independently constructed canonical breadth-first graph serialization gives
the same result. Consequently ST215 is not a state renaming or reflected state
renaming of any table in this specific corpus. This is a graph-level claim; it
does not claim that no equivalent machine exists outside the corpus.

As a control, the audit also changes only ST215's appender write back to one
and repeats all 78 comparisons. This control also has no direct or reflected
match. The graph difference therefore persists when that appender bit is
restored. Its table is saved as `append-one-control.native.tm` in the audit
output; it is not the primary candidate.

The substantive design change is the physical realization of the 35-leaf direct
transfer body in a suitable outer source association. With work tuple
`(t,w,d,h)` and `unpair(w)=(a,v)`, that body halts exactly when incoming `h=1`
and otherwise returns `(h,v,d,a)`. The older 78-leaf `DROP;NIP;NIP` body also
tests incoming `t=1`. Thus the replacement changes the command contract and
needs its own consistency calibration. The shorter body was already proposed
in incoming research; the new result is its corrected contextual realization
and accompanying calibration, rather than invention of that arithmetic body.
The semantic calibration is supplied by the main report, not by this audit.

## Independent audit of the saved runtime evidence

`runtime/runtime.json` and `runtime/cases.json.gz` are the fresh runtime
producer's evidence for these exact table/source bytes. The independent
`audit_runtime_metadata.py` checks every saved case record, without importing
the executor:

- The expected ordered inventory contains **6,151 cases**: one for each leaf,
  with both zero and positive branches for the **1,419 decrement leaves**.
- Every case has a positive constant duration and nonnegative coefficients in
  its thirteen-component affine duration. The minimum constant is **5**.
- Every nonhalting primitive's displacement equals the independently derived
  program-counter overflow displacement. There are 6,149 zero displacements,
  one displacement of -1, and the single halt case has displacement +5.
- Every named row belongs to the exact converted table, and their union is all
  **430 table rows**. Aggregate metadata accounts for **1,617,630 symbolic
  rules**: 1,363,173 literal rules, 250,671 unary scan rules, and 3,786 list rules.
- All four one-block certificate traces name actual table actions. Their
  duration and displacement sums agree with the stated `v+2` schemas.

The case execution traces themselves were not retained in the producer's
compressed inventory. This metadata audit therefore does **not** independently
replay all arbitrary-value runtime derivations. It checks input binding,
inventory completeness, arithmetic summaries and row accounting. The full
symbolic executor, its induction rules, and the logical argument must be
reviewed separately. Neither audit in this folder is a proof-assistant kernel
check, and neither establishes `Con(ZFC)` from bounded blank-tape simulation.

## Scope of the 214-state search

Separate physical searches found no valid 214-state result. On the short-transfer
layout, a radius-7/fuel-97 finite local fold-certificate search tested 309,444
specifications without a certificate. A primitive-level finite screening of
91,164 row-supplier pair quotients likewise retained no candidate. A known
runtime-only 214-state fold enters an outward blank ray from all four tested
append/start combinations. These are negative results for explicitly bounded
search families, not a lower bound of 215 states.
