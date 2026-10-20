# Rebase the equality sources onto the K220 engine

**No valid machine with 218 or fewer states was found.** The smallest raw
allocations have 219 states. Two checked examples fail their primitive
contracts, with concrete complete-tape counterexamples. All candidate tables
here are research specimens; the accepted [K219](../candidate-k219/README.md)
table is unchanged.

The five original-theory sources are equality hits 0, 1, 2, 3 and 12 from
[source search](../k219-source-search/README.md). Their all-natural macro
contracts and contextual replacements are separate evidence in that packet.
Each has 207 distinct source subtrees. This experiment changes allocation and
engine entries, not that calculus. The separate R205 diagnostics concern the
membership-fourth-parameter proposal whose consistency calibration remains open.

## Engine comparison

[measure_rebase.py](measure_rebase.py) uses pinned K221 source/decoder tools
and the earlier allocation algorithm. It compares the exact K219 and K220
tables, then two explicit K219 hybrids. The first hybrid restores the exact
K220 increment rows `113/0 = 0L40`, `198/0 = 1L198`. The second additionally
substitutes the generic B1 return `103/1 = 0L40`. Both retain K219's shared
state 108. The latter return is a hypothesis, not an inherited proof.

Every strict allocation rejects a missing right-CI5 or right-CI6 entry.
For measurement only, an explicitly separate mode supplies `1R63` for right
CI5 and `1R13` for right CI6. Neither was certified by the source/decoder test.
The following counts include those hypotheses:

| Backend | Hit 0 | Hit 1 | Hit 2 | Hit 3 | Hit 12 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Exact K219, same-position origin reuse | 220 | 220 | 220 | 220 | 220 |
| Exact K220, same-position origin reuse | 219 | 219 | 219 | 219 | 219 |
| K219 with K220 increment rows | 219 | 219 | 220 | 219 | 220 |
| Previous row plus generic B1 return | 219 | 219 | 219 | 219 | 219 |

The protected allocator, which never reassigns an old state's role, produces
239–243 states across these comparisons. Both allocators exactly reconstruct
the original 219/220 tables in identity controls. Every reported successful
allocation passes source ordinal identity, two independent source-CFG
constructions, table totality/roundtrip, graph pruning, and the exact decoder
prefix relation. These checks do not prove arithmetic leaf behavior.
All 80 outcomes are retained in
[allocation-run1/result.json](results/allocation-run1/result.json).

Removing the old 302 helper is not the same as removing its numeric label.
After pruning the old helper, the allocator can reuse label 302 for a fresh
decoder. Inspect its two literal rows and incoming edges; the recorded
`retained302` field only reports label membership. Increment restoration alone
leaves the original B1 caller in hit 2. An additional return substitution can
remove the old helper, but has its own runtime obligation.

## Located primitive failures

The unchanged symbolic runtime engine was run on the native-K220 allocations
for hits 2 and 0. Both prove 5,930 guards before rejecting CD6-zero at leaf
index 4568. The hit-2 run took 144.87 seconds; hit 0 took 141.77 seconds.
Their complete required censuses are respectively 6,167 and 6,171 guards.
Neither run is a full runtime success.

The allocator selected old entry 13 for the unchanged subtree
`P = (CD6, CC2)`. Its original occurrence at path `0111` has a special entry
context. Using that state at new equality occurrences is invalid. The
[first shared-108 repair](results/shared108-v1/result.json) redirected every
P caller to 108 and changed `108/1` to the K219 row `0L10`. It repairs the
new CD6-zero case but breaks the original CC2 at index 8 by also changing
caller `8/1`. That failed draft is retained.

The [second repair](results/shared108-v2/result.json) preserves `8/1` and
redirects only new equality callers. Every hit then passes 255 selected
guards, including the known CD6-zero failure, before rejecting its first
new right-CI5/CI6 entry at index 4570. Thus the hypothesized right-CI entry
is a second, independent defect. No further full suite was run on that repair.

Both hit-2 failures have concrete witnesses, using all nine registers zero,
one spare of value zero, and gap zero. They return to the clean dispatcher
at the expected head position, but with the wrong entire tape:

| Table / guard | Steps | Extra one cells | Missing one cells |
| --- | ---: | --- | --- |
| Native-K220 hit 2, CD6-zero at 4568 | 620 | 83, 85, 87, 88 | 84 |
| Shared-108 v2 hit 2, right-CI6 at 4570 | 622 | 84 | 83, 85, 87, 88 |

The first discrepancy is an unwanted increment and spare append; the second
omits those effects. Full initial data, actual/expected tapes and literal
step traces are preserved in
[finite-failure-witnesses.json.gz](results/finite-failure-witnesses.json.gz).
These witnesses establish contract failures, rather than only failure of
symbolic proof search. They make no claim about the defective table's blank run.

The completed records and cases are under
[runtime-native220-hit02](results/runtime-native220-hit02/result.json),
[runtime-native220-hit00](results/runtime-native220-hit00/result.json),
[entry-checks-v1](results/entry-checks-v1/result.json), and
[entry-checks-v2](results/entry-checks-v2/result.json).
The remaining two queued full checks were cancelled after the failure was
located; [the interruption record](results/full-batch-interruption.json)
distinguishes completed results, unsaved console output, and jobs never started.

## Global reuse of retired decoder states

[global_allocator.py](global_allocator.py) is a separate policy. A pool state
must have no old subtree role still live in the new source. Every old incoming
edge must be a literal `(read bit, R, q)` internal-child edge for **every** old
decoder role at its predecessor. Start 0 and dispatcher 84 are excluded.
The primary policy additionally requires both old rows at q to preserve the
read bit and move right. A separately labelled supplementary policy omits
only this own-row condition. Neither policy changes states outside its pool
and the dispatcher. Per-state incoming certificates and assignments are saved.

| Backend | Pure-row pool: each equality hit | Incoming-only pool: each hit |
| --- | ---: | ---: |
| K219 | 223 | 222 |
| K220 | 222 | 222 |

These have exact decoder binding but pending primitive runtime. The three
205-subtree RAB-left, RBC-left and RCA-right variants fail prefix checking
on K219. Their rejected diagnostic allocations have 222 states. On K220
the allocator instead rejects a missing generic right-CD6 entry.

The K219 failure exposes a limitation in the proposed pool criterion:
state 145 has the pure incoming edge `131/0 → 145`, but state 131 itself has
the contextual/arithmetic incoming edge `188/0 = 0L131`. Rewriting 145 can
therefore disturb that entry. The first rejected prefix is
`11101001001100000110`: unchanged state 39 reads 1, writes 0 and advances,
corrupting a bit that must be preserved. The state-145 rewrite, rather than
state 39's unchanged row, caused this wrong path. Protecting 131 and 145 alone
still leaves other prefix failures after pool reassignment. Those attempts
are preserved; no transitive-safety theorem or successful new allocator is
claimed. See [global-pool-v1](results/global-pool-v1/result.json),
[diagnostics](results/global-rejected-diagnostic/RAB-left/result.json), and
[explicit-protection v2](results/global-explicit-protection-v2/result.json).

A separate bounded fold search on the rejected raw native-K220 hit-2 table
examined 320,464 candidates: all state pairs excluding 0/84, inherited rows,
and all one-branch helper actions when the other branch agrees. Radius 5,
fuel 97 yielded no discovery-filter survivor. The filter is incomplete;
this is neither a state lower bound nor a verified 218-state construction.
The [search record](results/fold-search-native220-hit02/result.json) binds
the unchanged Source139 acceptance checker that would have checked a survivor.

## Reproduction and attribution

The scripts reject existing output directories. [inputs.json](inputs.json)
retains the actual workspace paths and SHA-256 values used in the experiment;
relocation requires rebinding paths without changing those input bytes.
From this repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-engine-rebase/measure_rebase.py --out /tmp/engine-rebase-fresh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-engine-rebase/measure_global.py --out /tmp/engine-global-fresh
```

`check_runtime.py --help` describes explicit candidate pins and the recovered
K221 runtime-library input. Its mathematical engine bounds proof construction
at 4,000 symbolic steps per guard; actual register values, gap and spare list
remain unbounded. No Lean or Rocq compilation was performed for this packet.
Only identity/hash/parser checks, source allocation, symbolic/finite runtime,
and the stated bounded search were executed.

The K220/K219 tables and runtime checker retain their submitted attribution
and licenses; see the linked candidate packets. Preserved `source_language.py`
and `build221.py` come from the pinned K221 construction. The original
allocator is opening_encoder's earlier pivot packet; `original_search_v3.py`
is drop_contract's bounded search, and `check_joint_fold.py` is the unchanged
Source139 checker. New policies, drivers and this analysis are opening_encoder's
follow-up research, at root's requested scope. Source authorship and measured
failure do not substitute for an independent proof review.

Large case arrays are losslessly gzipped. [compression.json](results/compression.json)
records both compressed and original byte identities, and every compressed
file was decompressed and compared before publication. Original scratch paths
and copied-file bindings remain in [copy-map.json](results/copy-map.json).
