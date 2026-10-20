# K-theory 224-state candidate

This binary, single-tape machine has **224 working states**, including initialization, plus
a separate halt state. It starts in state 0 at head 0 on an all-zero two-way infinite tape.
Every transition moves left or right. The complete 448-row table is [zfc_k224.tm](zfc_k224.tm).
It was the smallest known candidate until the [223](../candidate-k223/README.md) (Source 127),
which builds on it.

It is Source 125 of the ZFC closure-kernels host (arrival `49ee7cfdc8`; see the
[batch 179 reconciliation](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-179.md)).
It builds on the [225](../candidate-k225/README.md) (Source 124), which descends from Elliot
Glazer's [k230-rocq](https://github.com/elliotglazer/k230-rocq) (commit `3142e4d`). An ordinary
mathematical proof, formalizable in ZFC, establishes

  ZFC ⊢ (this machine does not halt from the blank tape ↔ Con(ZFC)).

Unlike the 225, the 224 changes the logic the machine searches, not only its layout. Its
source enumerates the theorems of a calculus K′. K′ fuses four double-negation pairs, and it
replaces K's equality vacuity by one canonical helper. The calibration K′ ⊢ ⊥ ⟺ K ⊢ ⊥ is
argued in the package's report, as is the rest of the chain. The proof composes four parts:

- the unbounded runtime certificate for this table on its own source;
- the exact blank startup;
- the package's finite certificates for the formula fusion and the equality helper;
- the K′ calibration, then k230's Rocq theorem for K.

**No Rocq or Lean theorem exists for this table**, and no proof internal to PA. The K′
calibration in particular is not yet formalized. The smallest table with a kernel-checked
endpoint is the [225](../candidate-k225/README.md): ProveIt rebuilt its Rocq endpoint
`K225F.CorrectDense225`, which passes `coqchk`
([k225-formal](../k225-formal/README.md)). No absolute consistency, unconditional non-halting,
minimality, or two-sided independence from bare consistency is claimed.

## How the states are saved

This table deletes K230 states 79, 140, 175, 191, 208 and 229 (in K labels). The first five
steps are the 225's; see [its page](../candidate-k225/README.md#how-the-states-are-saved). The last
step is Source 125's, in three changes:

1. **Fuse the formula.** Cancel four double-negation pairs in the K formula and its final
   bundle, and reassociate the closed existential constructor program. This removes eight
   negation constructors and one distinct source subtree. Alone it still leaves 225 states.
2. **Change the equality helper.** Keep full membership vacuity and the original bundle gate,
   but use only the canonical primitive-equality helper `Eq(a,b) → All(RelCode(a,b), Eq(a,b))`
   with `RelCode(a,b) = 4·P(a,b) + 1`. This binder is strictly larger than both endpoint
   labels. Three closed source rotations then expose a decoder layout with a 225-state parent.
3. **Share two decoder states.** In that parent, K states 157 and 191 are entered after writing
   opposite preceding tape bits. State 191 is redirected to 157, and existing helper states
   reproduce its four transitions in blocks of three or five steps.

In state-count terms the 224 is 49 engine states + 187 distinct interior source nodes − 12
tag-shared roles, one node fewer than the 225's 49 + 188 − 12.

## Verification

| Check | Result |
| --- | --- |
| Direct unbounded runtime of **this table** on its own source, with Source 103's checker ([receipt](evidence/runtime224.json), [cases](evidence/runtime224_cases.json)) | `UNIVERSAL_MATHEMATICAL_PASS`: **6,238** guarded cases, **1,503,342** symbolic rules, all 448 rows, minimum instruction duration 13 |
| Exact blank startup, sparse and dense ([code/boot.py](code/boot.py), [record](evidence/boot.txt)) | the complete dispatch frame after **409,835** steps |
| Finite screen on every leaf and both decrement guards ([code/screen.py](code/screen.py), [record](evidence/screen.txt)) | 0 failures |
| Delivered canonical table vs the checked inherited-label table ([code/make_inherited.py](code/make_inherited.py)) | the same machine (BFS-canonical forms equal) |
| Decoder accounting | 49 + 187 − 12, startup and leaf count as above |

These checks are the intake's own, run with the same adapted checkers as for the 225. The rule
count equals Source 125's receipt. The intake has **not** replayed the package's logical
certificates: the fusion certificate (1,563 nodes), the equality-helper certificate (68 closed
roots, 59,947 nodes) and the eleven local register-program bisimulations.

## Exact files and attribution

| File | Meaning |
| --- | --- |
| [zfc_k224.tm](zfc_k224.tm) | Canonical table as delivered: states 0–223, start 0, halt 224. |
| [zfc_k224_old.tm](zfc_k224_old.tm) | fold241 inherited labels (start 95, dispatcher 96, halt 254), the table the checkers ran on. |
| [sites_logical.json](sites_logical.json) | Exact 4,799-leaf source (210 distinct subtrees, depth 38, zero run 6). |
| [ingredients/](ingredients/) | Delivered legacy- and K-label tables, the delivered renumbering, and the label compaction. |
| [code/](code/) | `make_inherited.py`, `boot.py`, `screen.py`, the adapted runtime checker and `setup_checkers.sh`. |
| [evidence/](evidence/) | Runtime receipt with per-case records, startup and screen records. |

Canonical SHA-256 `6361b0b29c2e0485bf8cf025dcf2606c2fac071f3f6e24fbde04016466d92168`; inherited
`f8928feb4cd0d58e6489f7c8577421ae956bf2aefdf4391813599aace6b26072`; source
`309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878`.

The theory K, its consistency proofs, the K source and the 230-state machine are Elliot
Glazer's. The formula fusion, the canonical equality helper with its K′ calibration, the three
rotations and the 191 → 157 fold belong to Source 125. Everything up to the 225 is credited
as on the 225's page. See [ATTRIBUTION.md](ATTRIBUTION.md).
