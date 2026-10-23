# Phase24 source review

**The full selected kernel check, independent actual readback, capture and
independent capture review pass.** The final table binds the repaired source
bytes. Earlier source proposals, author reports and source-spec status labels
retain their chronological scope; later terminal evidence establishes acceptance
without rewriting those receipts.

## Complete maintained-file comparison

Positive bytes removed means a saving; the shared library growth is charged in full.

| Source | Before lines | Final frozen lines | Bytes removed |
|---|---:|---:|---:|
| `KBoot` | 76 | 71 | +118 |
| `KRuntimeCore` | 562 | 538 | +1,232 |
| `KZip` | 226 | 224 | +133 |
| `L2Lib254` | 355 | 388 | -1,723 |
| `L2Root222` | 236 | 184 | +2,937 |
| `L2Root254` | 236 | 183 | +2,974 |
| `L2RootDom` | 174 | 170 | +314 |
| `L2RootPerm` | 168 | 166 | +214 |
| `TarskiCalculus` | 195 | 195 | +58 |
| `TarskiClean` | 214 | 193 | +661 |
| `TarskiDerived` | 196 | 190 | +450 |
| `WFModelCore` | 196 | 166 | +976 |
| `WFRelativization` | 166 | 157 | +91 |
| **Total** | **3,000** | **2,825** | **+8,435** |

The net saving is 175 physical lines / 8,435 bytes over all thirteen files.
The primary `KEndpoint215` closure separately remains 172 modules and changes
from 1,728,487 to 1,726,277 selected source bytes. No module or producer is retired.
These measures overlap and must not be added. Relative to the first proposal,
six explicit annotation lines add 298 bytes; that cost is already included.
The earlier 181-line / 8,733-byte count remains historical, not an additional saving.

## Proof mechanisms and obligations

The attributed runtime patch preserves definition bodies, theorem statements
and attributes. Constructor equality elimination replaces explicit injectivity
bookkeeping; matching branches share proof bodies, and reachability composition
reuses existing `run_add` facts. Machine transition data and endpoint statements
remain exact.

`L2.dec_brk`, `L2.dec_halt`, `L2.pass` and `L2.fall` generalize the existing Dom/Perm
selector mechanism over the program while retaining its exact node equation.
The eight 254/222 dispatch proofs use their existing program-specific bodies.
Scratch-register and `p2` premises remain at their old callers; normal and halt
exits stay distinct. The seven specialized names remain typed wrappers. No run
is transferred across the different AX or fetch implementations, and root-step,
iteration, boot and program-halting proofs remain untouched.

`WFRelativization` uses constructive subtype quantifier equivalences and the
existing `liftEnv_scons` bridge. Both WF guards remain. The final universal and
existential branches explicitly type their subtype predicates and reflexive
raw Sat equivalences. These annotations resolve the two rejected inference
stages without changing the proof mathematics. `WFModelCore` reuses
`sat_translate_scons` and `sat_translate_relOf` instead of repeating environment
equalities and the private `raw_rel_iff` lemma. `replacementForm` and its
specification retain both WF guards, output slot 0 / input slot 1 orientation
and global functionality.

The existing `Tarski.update_comm` header and proof move unchanged from
`TarskiClean` into `TarskiCalculus`, where soundness reuses them. Existing import
paths still expose the same global name. `imp_cases` reuses `Kalmar.cases_on`;
`occurs_lt_top` follows constructively from `not_occurs_of_top_le`. All old logic
headers and imports stay exact. No new public logic helper is added.

## Evidence boundary

The final source/plan readback binds all thirteen before/candidate/canonical rows,
all 230 selected source hashes, physical sizes and actual import edges, exact DFS
order and source-transitive freshness. It independently verifies the metrics
above and 102 current present pins / sixteen absences. That is a binding/count
review, not an independent mathematical review of its author's three logic edits.
Each original source report remains an author's readback for its own files;
mathematical review and measured full evidence keep their separate scope labels.

Native-diagnostic-v2 passes sixteen providers, two fresh and fourteen exact phase23
reuses; the two fresh WF sources match the final map and have no warnings.
The diagnostic supplies no objects to the full run. The later full check passes
230 providers and two endpoint audits with exact profiles and zero selected
warnings. The [independent actual readback](lean/result-review.json) checks
1,250 owner inputs, 102 present pins and sixteen absences, with 218 adjacent raw
provider records and twelve inherited absences. Both capture and its
[independent review](integration/capture-review.json) pass.

Four terminal focused diagnostic contexts are retained as 240 explicit inert
files. The first fails the metadata ordering gate before any compiler; the next
two fail separate elaboration inferences; the final native diagnostic passes.
None supplies full-run objects, and there is **no failed full-run prefix** this
phase. Source reports' initial 181-line / 8,733-byte arithmetic remains historical;
the final typed annotations and current source bindings establish 175 / 8,435.
The [integration notes](integration/README.md) retain preparation chronology.

The separate new batch219 review of commit
`56b37bde8b064d852154ad8478d58ec9ab5375d6` reads proposal sources and historical
evidence only. It is outside these thirteen checked sources; this phase does not
claim to compile or adopt its future control or scheduler leads.
