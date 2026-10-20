# Intake 178: the K-family machines (228 to 225) and an equality reduction

Placement `ad8cbe8249` imports nine packages as **Sources 116–124** and retires their
ZIPs. The host now reconciles **124 sources**; the collection remains **290 reports**. The
[placement map](data/intake178-placement.json) accounts for all 2,242 members:

- 1,006 staged byte-identical (0 mismatches against a fresh extraction);
- 1,207 exact aliases of blobs already tracked or staged earlier in the batch;
- 1 history alias: Source 120 vendors Source 115's archive (`0128d662fd`);
- 28 archive-only (main manuscripts, PDFs, delivery READMEs).

Sources 117–124 build on Elliot Glazer's
[k230-rocq](https://github.com/elliotglazer/k230-rocq) (commit `3142e4d`). It has a 230-state
machine that searches a compact set theory K, proved equiconsistent with ZFC, with a Rocq
proof that it halts iff ZFC is inconsistent. ProveIt's
[228-state candidate](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k228/README.md)
(commit `672bcf20be`) showed that k230 keeps ProveIt's 241-state engine. It applied two of
ProveIt's engine savings to it. The packages below go further.

## Source 116 — `zfc_equality_reduction_20261019.zip` (prefix `116-eqred-`)

Arrival `aaf47dea43`, pinned to ProveIt `7ba1598461` and Source 112's archive. It is a
logic-level reduction:

- **The main result.** Replace full fresh equality vacuity by the single code-specific helper
  `Eq(a,b) → All(weq(a,b), Eq(a,b))`. The theory stays equiconsistent with ZFC, relative to
  the existing completeness and model endpoints, with equality read as two-sided membership
  indiscernibility. Appendix A admits any auxiliary `κ(a,b)` distinct from `a,b` when `a ≠ b`.
- **The cost.** The edited source has 201 decisions and 6,511 instruction occurrences.
  Its generic-compiler cost is 263 states.
- **Variants.** `H_sym` keeps primitive symmetry and drops ρ7; `H_7` keeps ρ7.
  - Their snapshots have 198 decisions in the generic layout.
  - The repaired backend sources have 199 and 200 distinct interior nodes, against the
    original's 201. But they have depth 92 and zero run 8, where the specialized decoder
    needs depth below 64 and zero run 6.
  - An exact-reassociation walk could lower the depth only by adding nodes.

The package claims **no machine**, and the intake found no way to compile these variants
into the specialized decoder at a saving.

## Sources 117–124: the K-family

| Source | Package | States | K230 states deleted | Table, canonical SHA-256 |
| --- | --- | ---: | --- | --- |
| 117 | `K226_Construction` (49-atom layout) | 226 | 79, 140, 175, 208 | `f2c2fde3…` |
| 118 | `K227_Construction (1)` | 227 | 79, 140, 175 | `0264f969…` |
| 119 | `K227_Construction` | 227 | 79, 140, 175 | `f821e7fb…` |
| 120 | `K228_Construction` | 228 | 79, 140 | `06726bd7…` |
| 121 | `K228_Transfer` | 228 | 79, 140 | `06726bd7…` |
| 122 | `ZFC226_K230_Transplant` | 226 | 65, 79, 140, 175 | `789e9d1c…` |
| 123 | `K226_ZFC_Construction` | 226 | 65, 79, 140, 175 | `b58279b8…` |
| 124 | `K225_Construction` | **225** | 79, 140, 175, 208, 229 | `f5d69a16…` |

A canonical census of every delivered table, up to relabeling, shows:

- **One 228.** It is ProveIt's `candidate-k228`, delivered by Sources 117, 119, 120 and 121.
- **Two 227s that end the line.** Sources 118 and 119 each stop at 227, with different
  tables. Sources 117, 122 and 123 also pass through 227-state intermediates of their own.
- **Three 226s.** Sources 122 and 123 are **one construction**: identical source and state
  set, differing in a single row (`120/1`, two choices of an existing clear-one helper for
  the relocated break). Source 117 is a genuinely different construction.
- **One 225** (Source 124).

### How the savings are made

Counting states as engine + distinct interior source nodes − tag-shared roles:

| Table | Engine | Nodes | Shared |
| --- | ---: | ---: | ---: |
| K230 | 51 | 189 | 10 |
| 228 | 49 | 189 | 10 |
| 227 (Sources 118, 119) | 49 | 189 | 11 |
| 227 intermediates (Sources 117, 122) | 49 | 188 | 10 |
| every 226 | 49 | 188 | 11 |
| 225 | 49 | 188 | **12** |

- The two engine savings (228) are ProveIt's delayed erasure and loop-rotation fold.
- **The node saving is the same in every 226.** K230 state 65's 33-leaf subtree
  `(K114, K12)` is gone from all three 226 sources. It goes by the `85/65` source sharing,
  or by Source 117's 49-atom layout. No splice of the 226 sources gets below 211 distinct
  subtrees.
- The sharings re-host the roles of K175, the analogue of ProveIt's old 218.
  - Sources 118, 119, 122 and 123 split its contexts onto existing states.
  - Source 117 instead keeps one role in an explicit state and adds the fold 208 → 76.
- **Source 124's 225** adds the other line's fold to Source 117's 226. Four closed rotations
  (right 169/136, right 170/169, left 169/154, right 159/118, in K labels) expose helpers 159
  and 170. Zero-tagged state 229 then merges into one-tagged state 152. State 152 is also
  Source 117's own helper for its 208 → 76 fold. That use survives because an inductive
  invariant shows its left-moving arrival from `76/0` also has a 1 to its left.

**Correction.** Before Source 124 arrived, the intake reported that the two 226 folds could
not combine. It argued that state 152 (182 in fold241 labels) could not both be the merged
state and stay a helper, and a two-rotation search found no helper pair. Both points were
wrong: the shared helper keeps working under the left-bit invariant above, and the helpers
appear only after four rotations.

### Independent replays

The intake relabeled each distinct table into fold241's inherited labels. Five of them went
through the startup lockstep map or their K230-label versions. The fold241-labelled 225 is
the delivered legacy table, with its labels above 253 compacted.

Then each was checked with Source 103's checkers, adapted only to compute the case count from
the supplied source:

| Table | Finite screen | Startup | Unbounded runtime |
| --- | --- | --- | --- |
| 225 (124) | 0 of 6,656 failed | exact, 409,835 | `UNIVERSAL_MATHEMATICAL_PASS`, 1,608,136 rules |
| 226 (117) | 0 failed | exact | pass, 1,596,687 rules |
| 226 (122) | 0 failed | exact | pass, 1,615,284 rules |
| 226 (123) | 0 failed | exact | pass, 1,615,284 rules |
| 227 (118) | 0 failed | exact | pass, 1,613,581 rules |
| 227 (119) | 0 failed | exact | pass, 1,615,133 rules |
| 235 (115) | 0 of 8,386 failed | exact | pass, 8,386 cases, 2,269,055 rules |

Each rule count matches the package's own receipt.

**The Rocq endpoint of Source 123.** `K226F.CorrectDense226` claims
`Dense.halts dense_tm Dense.c0 ↔ StandardZFC ⊢TC ⊥` for its exact 226 table (`b58279b8…`),
closed under the global context, with an independent `coqchk`. It would be the first
kernel-checked machine below 230. The intake has **not** rebuilt it: it pins Rocq 9.1.0,
and only 9.2 is installed here.

## The intake's search below 225

The intake ran three searches, all bounded and without a result:

- **Folds on the 225 as delivered.** The plain and helper fold searches find none.
- **A beam search over rotation chains**, ranked by the number of half-matched pairs. It is
  not a usable guide: started from Source 117's 226 it did not rediscover the 225 within four
  rotations. Replaying the 225's own chain shows why. Its first two rotations are pure
  preparation and add no helper to the target pair, while the global count of half-matched
  pairs wanders (114, 114, 116, 108).
- **A decomposed search, paused.** For every tagged pair and each read bit, it records the
  shortest rotation chain that creates that helper, then composes the two chains. It
  explores levels 1–2 in full and level 3 only through rotations sharing a state with the
  previous one. Two runs started: a calibration from Source 117's 226, which must find the
  225, and the real one on the 225. **Both were paused at the user's request** after about
  two thirds of the first-level branches: 64 of 78 for the calibration, 67 of 76 for the 225.
  That was before their composition phase, so they produced neither a candidate nor a
  negative result.

No machine below 225 is known.

## Non-claims

No Lean or PA endpoint for any K-family table. Only Source 123's 226 claims a Rocq endpoint,
and it has not been replayed here. No minimality.

## Attribution

The theory K, its consistency proofs, the K source and the 230-state machine are Elliot
Glazer's. The constructions of Sources 116–124 are their own. ProveIt's 228 composition is
credited as on its page.
