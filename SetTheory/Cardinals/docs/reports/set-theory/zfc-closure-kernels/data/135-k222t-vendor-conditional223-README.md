# K-theory 223-state candidate

This binary, single-tape machine has **223 working states**, including initialization, plus
a separate halt state. It starts in state 0 at head 0 on an all-zero two-way infinite tape.
Every transition moves left or right. The complete 446-row table is [zfc_k223.tm](zfc_k223.tm).
**It is the smallest known candidate** whose blank-tape non-halting is equivalent to Con(ZFC).

It is Source 127 of the ZFC closure-kernels host (arrival `281af27565`; see the
[batch 180 reconciliation](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-180.md)).
It builds on the [224](../candidate-k224/README.md) (Source 125). An ordinary mathematical proof,
formalizable in ZFC, establishes

  ZFC ⊢ (this machine does not halt from the blank tape ↔ Con(ZFC)).

The 223 searches a third calculus. It keeps the 224's fused bundle and restricted equality
helper, but its K core is **conditional**. K's root `∃c ((m → c ∋ b) ∧ H)` becomes
`m → ∃c (c ∋ b ∧ H)`, with the same support-and-closure formula H. The calibration therefore
has two parts, both argued in the package:

- **Upper direction.** The conditional core follows from K's in ordinary logic, because the
  private name is not free in the decoded matrix (k230's `D_private_fresh`).
- **Lower direction.** Unconditional K + IR is interpreted in conditional K + IR by a
  two-marker hereditary-domain construction (inherited from the 224 package's
  `conditional_k_calibration.md`). The equality-helper interpretation is then composed with it.

**No Rocq or Lean theorem exists for this table**, and no proof internal to PA. The smallest
table with a kernel-checked endpoint is the [225](../candidate-k225/README.md). The
[224's Rocq endpoint](../k225-formal/rocq224/README.md) is in progress, and almost all of it
carries over to the 223. The 223 additionally needs the conditional-K interpretation in Rocq.
No absolute consistency, unconditional non-halting, minimality, or two-sided independence from
bare consistency is claimed.

## How the state is saved

| Step | Saving |
| --- | --- |
| 230 → 224 | as on the [224's page](../candidate-k224/README.md#how-the-states-are-saved) |
| 224 → 223 | conditional-K source; four new source roles assigned to existing helper states 37, 26, 162 and 11 (all 24 priority orders checked; greedy allocation loses the sharing); then native state 18 merged into 180 by a left-neighbour tag and an existing helper |

The source still has 4,799 instructions and 210 distinct subtrees, but 1,162 of its leaves
differ from the 224's. In state-count terms the 223 is 49 engine states + 187 distinct interior
source nodes − **13** tag-shared roles (the 224: − 12).

## Verification

| Check | Result |
| --- | --- |
| Direct unbounded runtime of **this table** on its own source, with Source 103's checker ([receipt](evidence/runtime223.json), [cases](evidence/runtime223_cases.json)) | `UNIVERSAL_MATHEMATICAL_PASS`: **6,238** guarded cases, **1,515,697** symbolic rules, all 446 rows, minimum instruction duration 13 |
| Exact blank startup, sparse and dense ([code/boot.py](code/boot.py), [record](evidence/boot.txt)) | the complete dispatch frame after **409,835** steps |
| Finite screen on every leaf and both decrement guards ([code/screen.py](code/screen.py), [record](evidence/screen.txt)) | 0 failures |
| Delivered canonical table vs the checked inherited-label table ([code/make_inherited.py](code/make_inherited.py)) | the same machine (BFS-canonical forms equal) |
| Decoder accounting | 49 + 187 − 13 |

These checks are the intake's own. The intake has **not** replayed the package's logical
certificates: the conditional fusion certificate (1,611 nodes) and the source/emitter binding.

## Exact files and attribution

| File | Meaning |
| --- | --- |
| [zfc_k223.tm](zfc_k223.tm) | Canonical table as delivered: states 0–222, start 0, dispatcher 22, halt 223. |
| [zfc_k223_old.tm](zfc_k223_old.tm) | fold241 inherited labels (start 95, dispatcher 96, halt 254), the table the checkers ran on. |
| [sites_logical.json](sites_logical.json) | Exact 4,799-leaf conditional-K source. |
| [ingredients/](ingredients/) | Delivered legacy- and K-label tables, the delivered renumbering, and the label compaction. |
| [code/](code/), [evidence/](evidence/) | Checkers as for the 224, and their records on this page's files. |

Canonical SHA-256 `7edafbb2395d39e3b0895a5e0f4da61e12a371b0af71ef4cfb1a43c06e7b917f`; inherited
`a0654e2db4affd97477f18c938fe6d40893bbd545cd3947193f9cf6e917f29a9`.

The theory K, its consistency proofs, the K source and the 230-state machine are Elliot
Glazer's. The conditional-K calibration and the restricted equality helper come from the 224
package (Source 125). The helper allocation and the 18 → 180 fold belong to Source 127. See
[ATTRIBUTION.md](ATTRIBUTION.md).
