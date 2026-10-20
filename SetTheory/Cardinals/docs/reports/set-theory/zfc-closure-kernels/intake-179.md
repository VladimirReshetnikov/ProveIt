# Intake 179: a 224-state machine, and a double-negation 225

Placement `4a59278837` imports two packages as **Sources 125–126** and retires their ZIPs. The
host now reconciles **126 sources**; the collection remains **290 reports**. The
[placement map](data/intake179-placement.json) accounts for all 423 members:

- 333 staged byte-identical, 5 of them at the host root;
- 82 exact aliases of blobs already tracked or staged earlier in the batch;
- 2 history aliases: both packets vendor Source 124's archive
  (`K225_Construction_2026-10-19.zip`, blob `928ef523` of `680f058702`);
- 6 archive-only (the two main manuscripts, their PDFs and the delivery READMEs).

Verification logs were force-added past the repository's `*.log` ignore, since they are the
packets' receipts.

## Source 125 — `K224_Construction_2026-10-20.zip` (prefix `125-k224-`)

Arrival `49ee7cfdc8`, pinned to ProveIt `ad8cbe8249` and to Source 124's archive. It delivers a
**224-state machine** (canonical SHA-256 `6361b0b2…`), now the
[smallest known candidate](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k224/README.md).
The saving comes in three changes on top of the 225:

1. **Formula fusion.** Four double-negation pairs in the K formula and its final bundle are
   cancelled, and the closed existential constructor program is reassociated. This removes
   eight negation constructors and one distinct subtree, but alone stays at 225.
2. **A canonical equality helper.** Equality vacuity becomes the single helper
   `Eq(a,b) → All(RelCode(a,b), Eq(a,b))` with `RelCode(a,b) = 4·P(a,b) + 1`. This is
   Source 116's code-specific reduction, now specialized to K. Three closed rotations then give
   a 225-state parent.
3. **A decoder fold.** K states 157 and 191 are entered after opposite preceding bits. State 191
   is redirected to 157, and existing helpers reproduce its transitions in blocks of three or
   five steps.

The calculus searched is therefore **K′**, not K. The package argues K′ ⊢ ⊥ ⟺ K ⊢ ⊥ in its
report and supports it with finite certificates: fusion (1,563 nodes), equality helper
(68 closed roots, 59,947 nodes) and eleven register-program bisimulations. The direction
K′ ⊢ ⊥ ⇒ K ⊢ ⊥ is the easy one. The converse needs the equality-indiscernibility argument.

**Intake replays**, with the same adapted Source 103 checkers as for the 225, on the
inherited-label table of the candidate page:

| Check | Result |
| --- | --- |
| Decoder accounting | 49 engine + 187 nodes − 12 shared = 224, 4,799 leaves |
| Finite screen | 0 of 6,238 failed |
| Exact blank startup | the dispatch frame after 409,835 steps, sparse and dense |
| Unbounded runtime | `UNIVERSAL_MATHEMATICAL_PASS`, 6,238 cases, 1,503,342 rules, all 448 rows |

The rule count matches the package's receipt. The intake has **not** replayed the logical
certificates. No proof assistant checks the K′ calibration yet.

## Source 126 — `ZFC_Compact_Search_2026-10-20.zip` (prefix `126-dn4-`)

Arrival `490a3c3bcd`. It is a research packet. Its own first line says the requested strict
improvement below 225 was **not** attained. Its positive result is a different 225 (`DN4`,
canonical SHA-256 `07d77875…`):

- **Double-negation normalization.** The numeric axiom constructor is normalized across
  double negation, with a proof that the changed constructor yields exactly the same numeric
  theorems: two effective finite proof translations, in `report/full_dn_proof.tex`.
- **Where the saving lands.** The source drops from 5,121 to 4,745 leaf occurrences (376
  fewer), but the decoder keeps **188 distinct interior nodes and 12 sharings**: 49 + 188 − 12 =
  225, as for Source 124. Leaf occurrences cost no states. Only distinct decoder nodes do.
- **Negative and partial results**, each bounded and stated as such:
  - an inductive abstraction showing that NIP's general comparison is a test against 1 on
    every reachable entry, with a correct source specialization and a counterexample to its
    first binary compilation;
  - failed scanner and arithmetic-negation reductions;
  - a conditional proof of 6,083 of 6,168 primitive cases for a shortened scanner;
  - an equality-vacuity probe on the K230 source costing 227 states;
  - C++ fold searches over 747,955,300 helper combinations without a reduction.

**Intake replays** of the DN4 table:

| Check | Result |
| --- | --- |
| Decoder accounting | 49 + 188 − 12 = 225, 4,745 leaves, startup 409,835 |
| Unbounded runtime | `UNIVERSAL_MATHEMATICAL_PASS`, 6,168 cases, 1,483,121 rules, all 450 rows (the packet's figures) |

## How the two relate

Both packets cancel double negations in K's formulas. Source 126 does it everywhere and proves
the calculi equal; Source 125 cancels four pairs and treats the result as part of K′. Neither
saves a state by this alone: the 224's state comes from the equality helper and the fold it
enables. Whether DN4's normalization, combined with Source 125's helper and fold, exposes a
further fold is open. The intake has not searched it, since the search below 225 is paused at
the user's request.

## Formal status

- **The 225's Rocq endpoint now passes here.** The intake built the pinned Rocq 9.1.0 and
  replayed Elliot Glazer's K230 development with `coqchk`. On top of Source 123's K226F
  extension, it then compiled `K225F.CorrectDense225` closed and rechecked it with `coqchk`
  (`PASS_CLOSED_KERNEL`, [k225-formal/rocq](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/README.md)).
  The 225 is now the smallest table with a kernel-checked endpoint.
- **Lean.** For the 225 the source equivalence is proved (`KSource225`). The machine layer is
  under way: the executor, the register lemmas for every K-family table, and the 225's
  agreement with K230's engine.
- **The 224** needs, beyond the 225's work, a formal K′ calibration and an adapted
  program-to-calculus layer. Neither exists in Rocq or Lean.

## Non-claims

No proof-assistant theorem for the 224 or for DN4. No PA endpoint for any K-family table. No
minimality.

## Attribution

The theory K, its consistency proofs, the K source and the 230-state machine are Elliot
Glazer's. The constructions of Sources 125 and 126 are their own, building on Source 124 and,
for the equality helper, on Source 116.
