# Contextual alternative with 218 working states

This is the distinct Source 147 construction submitted in `3c7c3aa5a3`, from `K218_Contextual_Alternative_2026-10-20.zip`. It has 218 working states and a separate halt outcome,436 binary transition rows, and a fully counted blank initializer. The [primary K218](../../README.md) remains the main candidate. This alternative is not a 217-state result.

**Six fresh direct verification jobs passed**, including complete source reconstruction, table lineage, whole blank startup, and the full 6,167-case symbolic runtime. The [actual result](evidence/actual.json), [runtime audit](evidence/integrity.json), and [fresh-evidence review](reviews/fresh-actual-review.json) bind the exact files here.

The construction preserves the original K219 calculus and complete source behavior. Under the pinned inherited calibration, its ordinary mathematical proof gives ZFC ⊢ (blank nonhalting ↔ Con(ZFC)). This is not an unconditional nonhalting claim or a new exact-byte Lean/Rocq endpoint. The separate membership fourth-parameter supplement is not a premise.

## Exact files and mechanism

- [Canonical table](machine/k218.tm): states 0–217, start 0, halt 218.
- [Native table](machine/k218.native.tm): historical labels, start 0, dispatcher 84, halt 254.
- [Normalized table](machine/k218.normalized.tm): native 301/302 renamed 102/120.
- [Complete source](machine/sites218.json): 4,744 occurrences, 205 distinct subtrees.
- [Canonicalization](machine/canonicalization.json): exact inverse maps and delivered complete startup receipt.
- [Proof exposition](proof.md): source relation, contextual saving, full computation and nonstacking boundary.

The allocation adds 79 and removes 190 and 96 relative to K219. Its final fold routes state 85 through 221 to choose child 12 or 150 using the preceding tape bit. Accepted K218 routes the same two logical roles through 190 and removes 212. The [own comparison](comparison/comparison.json) checks the complete primitive word, all 6,166 guarded successor edges, and all 4,743 interior source-prefix contracts for each table. Both sources have 205 subtree types, with 162 in common. Their transition graphs are not related by a start-preserving label isomorphism; no computational-behavior inequivalence is inferred from that.

The named contextual folds are the same saving applied to different allocations and cannot simply be counted twice. The separately checked [row157 stack](variant-row157/README.md) preserves halting on every initial tape and remains 218 states. Further 217-state work needs a distinct reduction and its own proof.

## Scope and reproduction

The freshly checked whole startup is 312,701 transitions, reaching head −5, state84, header 139, gap 80, the logical seed `[3,0,0,0,3,0,0,0,0]`, 130 one-valued spares and 277 exact one cells. Its freshly checked runtime has 6,167 universal primitive cases and 1,514,325 symbolic rule applications, with all 436 rows covered and positive duration constants at least 13. The six direct jobs took 147.997 seconds in total, including 144.368 seconds for the full-runtime process. All selected inputs remained unchanged and eleven exact reconstructed artifacts matched the delivered bytes. The wrapper, manifest/checksum suites, ancestor proofs, delivered negative-control wrapper, and proof assistants were not executed in this replay.

The candidate files and own ordinary proof exposition are kept here. The original main report and its TeX inputs are recovered from the original Git archive through [intake190](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-190.md); they are not duplicated as a new article. The code/data payload and full fresh cases/logs are retained in the [host evidence](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake190-fresh-k218/execution/result.json). Follow the [recovery and reproduction instructions](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-190-reproduction.md) to restore the original packet. The accepted [prepare helper](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake190-fresh-k218/prepare.py) and [serial runner](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake190-fresh-k218/run.py) use only the six direct jobs described above.

For the independent literal comparison alone, from this directory:

```sh
python3 -B comparison/compare-portable.py --repo /absolute/path/to/Proofs \
  --output /tmp/k218-contextual-comparison-fresh
```

This recomputes source/tree/CFG and local prefix facts; it does not execute the submitted full runtime or claim a fresh logical-calibration replay. The original comparison script and its preserved unexecuted syntax-error draft remain alongside the portable path adapter.

The [source review](reviews/drop-review.json) lists full reads and exact scope. The [independent ordinary proof review](reviews/independent-source-peer.json) and [exposition peer](reviews/proof-exposition-peer.json) found no blocker; neither claims a new machine execution. Original credit is retained in [NOTICE.md](NOTICE.md), [PROVENANCE.json](PROVENANCE.json), and the submitted [provenance addendum](PROVENANCE_ADDENDUM.md). Source 147 contributes this source/allocation construction and its submitted proofs. `drop_contract` authored the intake exposition, independent comparison and row157 composition; the row157 checker is unchanged Source139 code. Fresh original-packet replay is owned by `opening_encoder` under root's execution authorization.
