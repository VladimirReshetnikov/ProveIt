# Intake 175: a 236-state machine, and the search below it

Placement `cc269f6062` imports two packages as **Sources 111–112** and retires their
ZIPs. The host now reconciles **112 sources**; the collection remains **290 reports**.
The [placement map](data/intake175-placement.json) accounts for all 526 members: 249
staged byte-identical (0 mismatches against a fresh extraction), 271 exact aliases and 6
archive-only (main reports, PDFs and delivery READMEs). The intake's own runs are in
[`data/intake175-fresh-replay.json`](data/intake175-fresh-replay.json).

## Source 111 — `ZFC_Sub237_Research_2026-10-19.zip` (prefix `111-sub237-`)

Arrival `ecb4df12d2`. **No machine below 237.** Its contributions:
- A fresh direct runtime replay of the 237 table, which agrees with the batch-173
  intake's: 2,261,369 rules.
- An independent all-tape checker for the 235 → 98 fold.
- An unbounded **source invariant** (product annotations, threshold 16) proving
  two forced-zero decrements and three unreachable instructions, with a theorem that
  two whole unreachable subtrees may be replaced freely. A source-restricted runtime
  interface verifies the 8,381 permitted guards of the unchanged 237.
- Eleven scoped search families, all with zero candidates:
  - seven binary families (empirical profiles, neutral helpers, staged and source-constrained helpers, shifted heads, all-tape shifted folds);
  - four audit families (tag toggles, tag + helper, offsets);
  - source searches: non-monotone reassociation with temporary growth and affine swaps (best 224 nodes), and an exhaustive don't-care substitution of 1,204,224 combinations (best 224).
  - A certified loop contraction of the source reaches 6,452 leaves but costs 202 internal nodes, one more than now.
- **E692**, a 692-bit, eight-equation packet (structural witness, an optimized Boolean
  formula, the unary binder reused as selector successor). Subject to the
  raw-EPSC/ZFC calibration, ZFC proves that its non-derivation of `N(d,d) = d` is
  equivalent to Con(ZFC). No state count is claimed.

Non-claims: no Lean/Rocq endpoint, no PA derivation and no lower bound. Negative searches
are finite and scoped.

## Source 112 — `ZFC236_Construction_2026-10-19.zip` (prefix `112-c236-`)

Arrival `0b5fec6980`; input is the 237 table of `ec480205a1`. **A 236-state machine**,
canonical `d4302309…` and inherited `ff059535…`, published by this intake as
[`candidate-rotated236`](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-rotated236/README.md):

1. **A node-neutral source rotation.** `(A,(B,C)) → ((A,B),C)` for closed chunks of
   245, 160 and 132 leaves. The middle node's decoder state 185 is reused for `(A,B)`,
   so only four decoder rows change (`177/0`, `177/1`, `185/0`, `185/1`) and the DAG
   keeps 224 nodes; depth goes from 48 to 49.
2. **A fold exposed by it.** 223 merges into 182 (rows `0 L 198`, `1 L 210`), using the
   bit to the left, which is 1 at 182 and 0 at 223. The four three-step blocks hold on
   every tape. The block for `182/1` uses the rotated row `177/1 → 212`.

Delivered evidence: source equivalence on 6,455 leaves and 8,386 guards; startup
409,835 steps; two local-fold checkers; direct runtime proofs of the rotated 237
(2,262,455 rules) and of the 236 (2,267,815 rules). Also **E688**, the 713-bit packet
minus a derived truth equation, with an infinite countermodel showing why the native
stack-tail equation must stay. Its finite search for 235 found nothing.

**Intake replays** (record above; checker [`candidate-rotated236/code/check236.py`](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-rotated236/code/check236.py)):
- The direct runtime proof of the 236 gives `UNIVERSAL_MATHEMATICAL_PASS`, 8,386 cases,
  **2,267,815** rules, 472 rows. It used Source 103's checker with only its source hash pin removed.
- The startup reaches the exact frame after 409,835 steps.
- The rotated source has the same control graph as the 237's, with 224 distinct
  subtrees.
- The rotation is exactly the four rows above.
- The fold invariant holds: 182 is entered only by `76/1 = 1 R 182`, and 223 only by
  `237/0 = 0 R 223`.
- All four blocks hold on every admitted 7-cell window.

Non-claims: no Lean/Rocq or PA endpoint for 236; no minimality.

## The intake's search below 236

The user asked for a smaller machine. Here is what was tried, with each result.

**1. Source-level leads of batch 173.**
- **NIP specialization** (Source 102). It removes 13 distinct DAG nodes and adds 13,
  three in the gate fragment and ten on its root path, for a net 0. The leaf kinds
  stay at 23. It cannot save a state under the decoder construction all candidates
  share: about one decoder state per distinct interior node, minus tag-shared roles,
  plus a fixed engine. That accounting is 237 = 49 + (201 − 13).
- **`rho3` deletion** (Source 108). Blocked on an open logical question. The native
  calculus has no primitive universal instantiation; it derives it using the equality
  rows, `rho3` among them.
- **Depth-39 source and broader associativity** (Source 105). Its capped beam could
  not pass through sources with more nodes.

**2. A 223-node source (new, source-only).** The 237 machine's source has no two
distinct nodes with equal control signature, so there is no free merge. A randomized
reassociation walk that may temporarily add nodes (Metropolis acceptance, cap 226,
Source 105's exact rotation library unchanged) found a **223-node equivalent source**:
- seed 11, restart 23;
- 1,345 rotations, 395 of them outside the all-closed rule;
- 6,455 leaves and 8,386 guards preserved, zero run 6, depth 52.

Source 105's independent checker replays every step: `EXACT_SOURCE_CONTROL_GRAPH_PASS`,
candidate SHA-256 `82480512…`. But only 69 of its 200 interior subtrees are original,
so it is far from the compiled decoder. A pull-back walk that stays at 223 nodes brought
the number of changed subtrees down from 131 to 73, still too many for a local recompile.
**No binary table is claimed.** A decoder for it would have to re-establish the
tag sharings, backward routes and three folds.

**3. Source 112's method, iterated.** A rotation compiler generalizing Source 112's
four-row edit was written: repurpose the inner child's state; left and right rotations.
On the 237 table it reproduces Source 112's rotated table byte for byte (`da0b3d1f…`),
and its profile plus `plain_folds` re-finds `BASE 182 223` with the published counters.
On the 236 table:
- **21 compilable rotations.** Source 112's fast fold search (`plain_folds`) on each.
- **Source 106's helper search** on the five rotations that pass both the finite source
  screen and the full profile, about 610–635 million helper checks each:
  **0 candidates.**
- **111 second-level rotations**, whose 28 clean tables also gave no plain folds. Their
  helper searches are recorded in the replay record.
- **One rotation, `R_163_225`, exposes four folds** merging 157 into 116 or 153. But the
  rotation alone fails 159 screen cases, and with any of the folds it fails exactly the
  same 159. The cause: the rotated subtree is entered with bit 0 instead of 1, so the
  tag-shared state 153 (subtrees 92 and 164) can no longer tell its roles apart. 153
  steps left into 157 to read that tag, and 157 is exactly the state the fold deletes.
  Repairing the tag would mean un-sharing 153, which costs back the state saved.
- The six rotations whose new node already exists save nothing: the inner node always
  has other parents.

These are bounded, scoped searches; their negative results are not lower bounds.

The intake's scripts are shipped as `code/intake175-*.py`. The search drivers import
Source 105's `exact_reassociate.py`, which is placed as
`code/105-con238-research-source_association-exact_reassociate.py`; copy it next to
them under its original name. `intake175-rotgen.py`, `intake175-sigclasses.py` and
`intake175-decoder_map.py` import `dag.py`, shipped as `intake175-dag.py`; copy it the
same way. The 223-node source and its checker certificate are
`data/intake175-source223.json` and `data/intake175-source223-certificate.json`.

## Attribution

Source 111's and Source 112's results are theirs. Source 112's 236 is credited to it,
with the reductions to 237 credited as before. The intake contributed the replays, the
223-node source, the rotation compiler and the recorded search.
