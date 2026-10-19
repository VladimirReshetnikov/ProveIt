# K-theory 228-state candidate

This binary, single-tape machine has **228 working states**, including
initialization, plus a separate halt state. It starts in state 0 at head 0
on an all-zero two-way infinite tape. Every transition moves left or right.
The complete 456-row table is [zfc_k228.tm](zfc_k228.tm).
**It is the smallest known candidate** whose blank-tape non-halting is equivalent
to Con(ZFC).

It removes two states from Elliot Glazer's 230-state machine
([`elliotglazer/k230-rocq`](https://github.com/elliotglazer/k230-rocq), commit
`3142e4d`). That machine searches for a contradiction in a compact set theory K,
proved equiconsistent with ZFC, instead of the original calculus. Rocq proves that
it halts from the blank tape iff ZFC proves a contradiction. The two saved states come
from ProveIt's own reductions between 241 and 238 states. Both live in the machine's
engine, which k230 inherited unchanged.

An ordinary mathematical proof, formalizable in ZFC, establishes

  ZFC ⊢ (this machine does not halt from the blank tape ↔ Con(ZFC)).

It composes four parts:

- an unbounded executable runtime certificate for this table on its own source;
- its exact blank startup;
- an equivalence between the rewritten source and k230's source;
- Elliot Glazer's Rocq theorem for k230's source program.

**No Rocq or Lean theorem exists for this table**, and no proof internal to PA. No
absolute consistency, unconditional non-halting, minimality, or two-sided independence
from bare consistency is claimed.

## Why ProveIt's reductions apply to k230

k230 keeps ProveIt's [241-state](../candidate-fold241/README.md) engine and blank
initialization. Run from the blank tape, fold241 and k230 agree step for step for the
whole startup: 408,419 transitions, the same tape at every step, and both end at their
dispatchers. The induced state map is injective on the 133 states visited, and both
rows of every mapped pair agree ([code/engine_map.py](code/engine_map.py)). It covers
50 of the 51 engine states. The two machines differ in their decoders: k230's source
has 5,125 instruction leaves and 189 distinct interior subtrees, against fold241's 202.

ProveIt went from 241 to 235 states in six steps. Two of them saved an engine state;
the other four saved decoder states on subtrees of the original calculus's axiom
section, which K replaces:

| ProveIt step | Saving | In k230 |
| --- | --- | --- |
| 241 → 240 | loop rotation, fold 90 into 72 (engine) | **applies**: k230 has the same loop at the same four occurrences |
| 240 → 239 | source reassociation, split 218 (decoder) | k230 shares 218's two roles in its state 161, but the reassociated subtree is absent |
| 239 → 238 | delayed erasure, fold 169 into 80 (engine) | **applies**: every row it edits is identical |
| 238 → 237 | fold 235 into 98 (decoder) | subtrees absent |
| 237 → 236 | rotation, then fold 223 into 182 (decoder) | subtrees absent |
| 236 → 235 | seven rotations, then fold 193 into 74 (decoder) | subtrees absent |

All labels below are fold241's inherited labels: start 95, dispatcher 96, halt 254.
[code/build_k228.py](code/build_k228.py) renumbers k230 into them through the startup
map, asserts every edited row's old value, and writes both tables.

### 1. Delayed erasure (230 → 229)

This is the step from Sources 101 and 102; see the
[238-state page](../candidate-combined238/README.md). Delete state 169 and change
three rows:

| Row | k230 | 229 |
| --- | --- | --- |
| `147/0` | `0 R 169` | `0 R 80` |
| `80/0` | `0 R 25` | `0 L 106` |
| `91/1` | `0 L 50` | `1 L 167` |

The source is unchanged. Our helper-row fold search, run on k230 from scratch,
rediscovers exactly this fold, together with a variant whose `80/0` row is `0 L 8`.

### 2. Loop rotation and the 90/72 fold (229 → 228)

This is the step of the [240-state candidate](../candidate-rotation240/README.md).
In the source, the transfer-plus-one loop `((CD6 (CI5 CC2)) CI5)` occurs four times.
Replace each occurrence by `(CI5 (CD6 CC2))`. Both forms send `(R5,R6) = (a,b)` to
`(a+b+1, 0)` and exit to the same successor.

- **Old form.** Decrement R6 and increment R5 until R6 is zero; the `continue 2`
  re-enters the decrement. When the decrement fails, step to the final `CI5`, then
  leave the subtree.
- **New form.** Increment R5, then decrement R6 and `continue 2` back to the start.
  When the decrement fails, leave the subtree at the same successor.

The source shrinks from 5,125 to 5,121 leaves. The decoder changes `142/0` from
`0 R 37` to `0 R 72` and `142/1` from `1 R 72` to `1 R 17`. Then delete 90, redirect
`79/1` to 72, and set `72/0 = 0 L 144` and `72/1 = 1 L 36`. These are the same edits
that turned ProveIt's 241 into its 240.

## Verification

| Check | Result |
| --- | --- |
| Direct unbounded runtime of **this table** on its source, with Source 103's checker ([receipt](evidence/runtime228.json), [cases](evidence/runtime228_cases.json)) | `UNIVERSAL_MATHEMATICAL_PASS`: **6,656** guarded cases, **1,614,426** symbolic rules, all 456 rows, minimum instruction duration 13 |
| The same checker on the 229-state table, and on unmodified k230 as a control ([229](evidence/runtime229.json), [230](evidence/runtime230_control.json)) | both pass: 6,660 cases each, with 1,612,207 and 1,605,903 rules |
| Exact blank startup, sparse and dense ([code/boot.py](code/boot.py), [record](evidence/boot.txt)) | the complete dispatch frame after **409,835** steps (k230: 408,419; 229: 408,563) |
| Startup lockstep with fold241 ([code/engine_map.py](code/engine_map.py), [record](evidence/engine_map.txt)) | 408,419 equal steps; 133 states mapped; rows agree |
| Finite screen on every leaf and both decrement guards ([code/screen.py](code/screen.py), [record](evidence/screen.txt)) | 0 failures for 228, 229 and 230 |
| Source equivalence: both programs run as register machines from the post-startup registers ([code/program_compare.py](code/program_compare.py), [record](evidence/program_compare.txt)) | identical (PC, registers) at all 2,999,664 instructions outside the four rewritten loops, over the first 3,000,000 steps of k230's program |

The runtime checker is an induction engine over all natural register values, an
arbitrary gap and an arbitrary finite spare list. Its 4,000-rule cap bounds proof
construction, not machine time. The checker is Source 103's
[`check_literal_runtime.py`](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/103-bound239-validation-check_literal_runtime.py),
with three changes in [code/check_literal_runtime.py](code/check_literal_runtime.py):

- the hash pin of ProveIt's 6,455-leaf source is removed;
- the expected case count is computed from the supplied source, one case per leaf plus
  one per decrement, instead of being fixed at 8,386;
- the fixed source size is dropped.

The checker uses the frame of k230's own Rocq proof: dispatch offset 64 and physical
register order `[6,2,0,4,3,7,8,5,1]`. It passes unmodified k230.
`code/setup_checkers.sh` copies the two placed runtime libraries next to it.

**The logical chain.** This table does not halt iff its source program, started from
the startup registers, does not halt: that is the runtime certificate plus the exact
startup. The rewritten source runs exactly as k230's program does outside the rewritten
loops, and each loop computes `(a+b+1, 0)` and exits to the same successor, as shown
above. So it halts iff k230's program halts, and by Elliot Glazer's Rocq theorem that
happens iff ZFC proves a contradiction. The comparison run checks the first link of
that argument concretely; it is not itself the proof.

**Looking further.** Our generic fold searches find nothing more on k230 or k228:

- plain, helper, two-helper, tag-toggle, tag-helper, offset and shifted folds on k230
  (the only hits are the delayed erasure and its variant);
- plain, helper, tag-toggle and offset folds on k228;
- 33 compilable node-neutral rotations of k230 (Source 112's method), of which 20
  pass the screen, all with 0 plain folds;
- exact reassociation walks of the k228 source, which found nothing below 212
  distinct subtrees.

ProveIt's four decoder savings depend on axiom-section subtrees that K does not have,
so the analogous savings on K's decoder remain open. These are bounded searches, not
lower bounds.

## Exact files and attribution

| File | Meaning |
| --- | --- |
| [zfc_k228.tm](zfc_k228.tm) | Canonical table: states 0–227, start 0, halt 228. |
| [zfc_k228_old.tm](zfc_k228_old.tm) | fold241 inherited labels: start 95, dispatcher 96, halt 254. |
| [sites_logical.json](sites_logical.json) | Exact 5,121-leaf rotated K source (212 distinct subtrees, depth 40). |
| [renumbering.json](renumbering.json) | Canonical state bijection. |
| [construction.json](construction.json) | Hashes of every stage, the rotated occurrences and k230's relabeling. |
| [ingredients/k230.tm](ingredients/k230.tm), [ingredients/sites230.json](ingredients/sites230.json) | Elliot Glazer's exact table and source, from `machine/` at `3142e4d`. |
| [ingredients/](ingredients/) | k230 and the 229-state table in inherited labels, and k230's source in ProveIt's site format. |
| [code/](code/) | `build_k228.py`, `engine_map.py`, `screen.py`, `program_compare.py`, `boot.py`, the adapted runtime checker. |
| [evidence/](evidence/) | Runtime receipts with per-case records, startup, lockstep, screen and comparison records. |

Canonical SHA-256:
`6abdf014301b80a0b48ebffd2c7b39649c936b68adb1e254987269e914477f38`.
Inherited SHA-256:
`de08436d579074b6ba946635661299b57c43cd8fc2682e582426674ad790dd00`.
Source SHA-256:
`fbc2a77c1da72147c84abf4ee16c76bf3b53811985a647e4c0b9989ad396d934`.
k230's table SHA-256, as published:
`e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8`.
Each non-comment row is `state read write direction next_state`.

The theory K, its consistency proofs, the K source program and the 230-state table are
Elliot Glazer's. The original calculus, program and 254-state construction are credited
to Mira-Cult, upstream verification to Jeff Ketchersid, and the compiler framework to
Andrew James Wade. The delayed erasure belongs to Sources 101 and 102. The loop rotation
with the 90/72 fold is ProveIt's 240-state step (commit `e5c2b3337e`). See
[ATTRIBUTION.md](ATTRIBUTION.md). k230-rocq asserts no repository-wide license; its two
data files are kept byte-identical, with their provenance, and are not relicensed.
