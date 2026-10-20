# Intake 183: a 221 by rotation and tag fold, and four 222 packages

Placement `c92e98e674` imports five packages from arrival `c011e44bc2` as **Sources 132–136**
and retires their ZIPs. The host now reconciles **136 sources**; the collection remains
**290 reports**. The [placement map](data/intake183-placement.json) accounts for all 613
members:

- 363 staged byte-identical (13 at the host root);
- 229 exact aliases;
- 6 history aliases: vendored copies of the archives of Sources 125 (K224), 128 (G223),
  129 (Seed223) and 131 (K222), recorded against their arrival blobs;
- 15 archive-only (each package's main manuscript, its PDF and the delivery README).

## Source 132 — `K221_Construction_2026-10-20.zip` (prefix `132-k221-`)

A **221-state machine**, canonical SHA-256 `6457dce8…`. It is now the smallest known
candidate, published as
[candidate-k221](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k221/README.md).

It starts from Source 131's seed-K 222. That machine is the same source as the intake's
[variant-bc](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k222/variant-bc/README.md),
but with its own helper allocation.

- **Three closed rotations** re-associate the source at paths `11101001001110111110` (one)
  and `111010010011101` (two). The primitive word and every guarded branch target stay
  fixed; only the tape-address tags seen by the decoder states move.
- **One fold.** Native decoder states K172 and K192 then act identically on read 1. On every
  arrival the bit left of the head is 0 at K172 and 1 at K192 (a radius-8 inductive tape
  invariant from an unconstrained start). So the kept state's read-0 row becomes
  `(0, L, K112)`, and the existing helper K112 continues each context to its old successor
  in five steps (K172) or three (K192).
- **Accounting** 49 + 185 − 13: the 222's nodes with one more tag-shared role.

**The intake's own replays**, on the table relabelled into fold241 labels:

| Check | Result |
| --- | --- |
| Accounting | 49 + 185 − 13; 208 subtrees, 4,744 leaves, depth 38, zero run 6 |
| Leaf sequence against variant-bc | identical |
| Guarded CFG against variant-bc | identical under both resolvers (arithmetic and interval), 6,167 checks |
| Exact blank startup | 409,835 steps |
| Finite screen | 0 of 6,167 failures |
| Unbounded runtime | `UNIVERSAL_MATHEMATICAL_PASS`: 6,167 cases, 1,514,663 rules, all 442 rows, minimum duration 13 |
| Canonical, native and inherited tables | one machine (BFS-canonical forms equal) |

**The calibration transfers.** The 221 runs the seed-K 222's register program exactly: same
primitive word, same guarded control flow. So the 222's ordinary argument applies unchanged:
Source 129's seed presentation, which Elliot Glazer's Rocq development calibrates, composed
with Source 128's G equivalence. The package adds no logical change, and claims none.

## Sources 133–136: four 222 packages

All four reproduce the two 222s the intake built at [batch 181](intake-181.md). Three ship
canonical tables **byte-identical** to the intake's:

| Source | Package | Tables | Same as |
| --- | --- | --- | --- |
| 133 | `K222_Composed_Construction` | `01fb8d98…` | variant-bc's source and its 12 sharing groups; a third allocation of the seed-K 222 |
| 134 | `K222_Construction (1)` | primary `3bcf4678…`, alternative `60e21a04…` | variant-bc and the A + B 222, byte for byte |
| 135 | `K222_Construction (2)` | seed `3bcf4678…`, conditional `60e21a04…` | the same two |
| 136 | `ZFC_K222_Construction` | `60e21a04…` | the A + B 222 |

**Their research sections contain no idea that goes below the 221.**

- **Source 134:**
  - its binder probe measures Rel, Eq and All binders for the G row, and none is cheaper;
  - its local fold search (radius 8, synthesized retained rows) found no fold on four
    tables: the three 223s and an intermediate 222.
- **Source 135:**
  - its C++ neutral-then-fold search tried all 404 accepted neutral row rewrites of the
    conditional 222, then fold synthesis, and found no 221;
  - its single-rotation screen found 193 closed rotations of the seed 222. Only 30 keep 208
    subtrees and zero run 6, and the best of them compiles to 222.
- **Source 136:** its bounded C++ searches (neutral rows, two coordinated helpers, halting
  folds) found no 221.
- **Source 133:** it measures an EqCode-binder alternative. Its restricted fold search from
  a G226 ancestor reaches 223 at best (17 tables), and finds no fold of its final 222.
- **Source 134's binder table** for comparison: Rel keeps 208 subtrees, Eq adds two leaves,
  All adds two subtrees.

All are bounded negatives, and the packages say so. Together with Source 132 they show
**why** those searches missed the 221: its fold needs **three** rotations, not one. It also
needs a retained row whose helper takes several steps, not an exact row copy.

**What stacks.** The 221's trick on the A + B 222 would give at best 49 + 186 − 14 = 221
again. A's conditional root and C's seed root are alternative presentations of the same root,
so they cannot both be applied. A 220 therefore needs a further fold on the 221 itself.

## The intake's search below 221

**The earlier miss.** The intake's batch 181/182 search (recorded in
`candidate-k222/variant-bc/evidence/rotation_fold_search.txt`) had already explored rotation
chains. It missed this fold for two reasons:

- it ran on variant-bc's table, which lacks Source 131's helper K112;
- its detector took tags from plain decoder walks and required a helper's rows to copy the
  old rows exactly.

**The new detector.** It is the
[candidate-k221](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k221/code/)
`sim_fold.py` and `rot_fold_search.py`. Tags come from the inductive radius-8 invariant, and
a retained row is accepted when a bounded symbolic run reaches exactly the old step's
configuration in both contexts. Read bits that one side never sees are free slots.

**Calibration.** Replaying the 221's three rotations on Source 131's table, the detector finds
exactly the delivered fold and its mirror.

**Result: no 220 in this family.** From the 221 the search explored 19,041 tables:

- all 74 first-level closed rotations, and every second-level rotation;
- third-level rotations sharing a decoder state with the second;
- rotations up to zero run 7, with tables screened at zero run 6 or less.

No pair of states folds by the detector, for any table ([log](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k221/evidence/rotation_fold_search.txt)).
This is a bounded negative, not a lower bound: deeper chains, other helper allocations, and
folds whose helper needs more than seven steps lie outside it.

## Credit

Source 132's rotations, fold and certificates are its own. The four 222 packages
independently reach the intake's two batch-181 compositions; the constructions are recorded
under every source, and none claims priority.

## Non-claims

Later the same day the 221 received a closed Rocq endpoint, which `coqchk` rechecked
([k225-formal/rocq](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/README.md)).
No Lean theorem yet. No PA endpoint. No minimality.
