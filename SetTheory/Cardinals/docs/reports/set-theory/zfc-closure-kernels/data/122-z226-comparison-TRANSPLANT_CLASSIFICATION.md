# Eight historical state savings, 243 to 235, compared with K230

The labels below are the sparse inherited ProveIt labels in the 243–235
archives; K labels are the original dense 0–229 labels in the released K230.
The separate K halt 230 is temporarily renamed 254 in the local machine files.
This is a bijection of one terminal label and has no state-count effect.

| Historical saving | Mechanism | Relevant K mapping | Status in the new branch |
|---|---|---|---|
| 243→242: delete old 27 into 15 | Local compensated state folding; callers old18/0,47/0,65/0 are rerouted; old15/0 moves left into32 | kept old15→K11; old32→K26; old18→K14,47→K39,65→K56 | Already incorporated in released K230. The K table already has K11/0=0L26 and matching reroutes. No fresh saving is charged. |
| 242→241: delete old39 into17 | Local state fold with backward decoder routing | kept old17→K13; old106→K91; old37→K31 | Already incorporated in released K230. K13 rows are 0L91 and1L31. No fresh saving is charged. |
| 241→240: delete old90 into72 | Rotate the transfer loop at old142, then recover the old90/old72 distinction from preceding bits | old142→K121; old90→K79; old72→K63; old144→K123; old36→K30 | Transplanted and independently proved. Source changes K121 children from(31,63) to(63,13). Fold deletes79, sets63/0=0L123 and63/1=1L30. Local all-tape simulation has456 ordinary rows and exceptional lengths9,3,3,3. |
| 240→239: delete old218 | Closed source reassociation frees an internal node; repair a backward projection, then split old218's two entry contexts between179 and223 | old218→K175; old179→K150; newly freed old223 helper role→K65; old215→K173; old237→K184; old187→K155; old220→K176 | Transplanted after extra K-specific scheduling. Rotate K85/K65; repair175/0 through repurposed65. Unlike the old frontend, K150 had a right-1 caller201/1; right rotation202/201 makes that caller201/0. Its correct chunks are(149,150,151). Context split deletes175, represents left0 by65 andleft1 by150. Six all-tape identities are proved. The final thirteen-stage source schedule restores maximum zero run6 without adding a scanner state. |
| 239→238: delete old169 into80 | Coordinated helper reuse with a source/runtime guard | old169→K140; old80→K71; old91→K80; old106→K91; old167→K138; old147→K126 | Transplanted. Delete140 into71, set71/0=0L91 and80/1=1L138. Four local blocks require the extra implication old140/read1⇒right-neighbor1. The original predecessor invariant alone does not prove this; the direct unbounded K runtime and exact blank startup supply the required scope. |
| 238→237: delete old235 into98 | One neutral helper return change at old240/1 enables a fold of states with common read1 branch | old98→K85; old240→K186; old235 has no unchanged K subtree | No direct literal transplant. Old235 had children(old231,old16), corresponding to(180,12); no K state has this pair. K199 has(180,166), reflecting the changed theory frontend. An exact-table scan must rediscover an adapted fold; applying the old patch by numerical labels is invalid. |
| 237→236: delete old223 into182 | Rotate old177/185, then share two decoder states using the previous bit | old177→K148; old185→K154; old182→K152; projection role old223→K65; old198→K159; old210→K169 | Transplanted as the fourth new state saving. K148/154 is a matching source rotation. K152 initially had left0 via119/0; the additional left rotation174/119 repairs that tag to1. The final source layout preserves both helpers. Delete65 into152, set152/0=0L159 and152/1=1L169. All454 old rows are proved:450 one-step blocks and4 three-step blocks. |
| 236→235: delete old193 into74 | Seven closed source rotations align four existing continuations; three-step predecessor-bit fold | The final old193 children(190,213) would map to K(157,172); the repurposed old74 children(114,233) would map to K(99,182) | No direct literal transplant. Neither mapped child pair is a current K decoder node. Original243 state74 mapped to original K65 only before the boundary schedule repurposed both labels; our final65 is a projection helper that has already been deleted into152. The numerical ancestry therefore supplies no eligible final pair. An additional saving would require fresh source scheduling and invariants. |

## Accepted K230 to K226 construction

The new machine deletes original K labels79,140,175,65, in that order.
The other226 labels remain as sparse names in the explanatory table. A
separate bijection supplies the ordinary dense table with working states0–225,
start0, and terminal226. The exact accepted table hashes are:

| Representation | SHA-256 |
|---|---|
| Original K labels, terminal renamed254 | `0d6740bbc94a92c9696ed92732b1828bec89109f8ebb6859bbb9197e2076ec89` |
| Dense K226 labels, terminal226 | `789e9d1cf04567223823bfdda7d0b4922d7018718fc0daf67c6f5b0c6b4c9b26` |

Thus two of the historical eight savings were already included in K230,
four have been transplanted with the required K-specific source and callback
repairs, and two have no direct surviving decoder pair. This accounting does
not attribute the K230 frontend reduction to the new work.

The final source has5,121 expanded instruction leaves,211 distinct source
DAG nodes, maximum path depth41, and maximum zero run6. The direct unbounded
runtime replay proves6,656 guarded instruction cases over arbitrary natural
registers, arbitrary natural gap, and arbitrary spare blocks. It uses1,615,284
symbolic rules, has maximum412 symbolic rules per case and minimum13 actual
steps, and exercises all452 final transition rows. Exact blank startup reaches
the required common initial frame after409,835 actual steps. These are
separate certificates from the local folds.

## The additional CB1 callback repair

Two source rotations move the AX terminal break leaf from a path ending11
to a path ending1111. The source graph remains the same, but copying the
old fused binary action is insufficient: it clears only two trailing ones.
There is also a backward entry103/1 into the old52/1 action that a source-only
rotation does not update.

The exact repair uses an existing duplicate of that action,18/1=0L27:

```
103 1 0 L 18
229 1 0 L 103
```

The original callback103→52→27 becomes103→18→27 with identical tape,
head, and endpoint after two steps. The relocated leaf uses
229→103→18→27→40→4, clearing the four trailing ones and their preceding
zero. State103 retains its three-one suffix. An independently recomputed
inductive bit invariant proves the predecessor patterns011 at103 and0111
at229 on every initial binary tape from state0. This repair adds no state.
The portable machine builder includes exact positive block certificates and
a negative control rejecting the stale two-one leaf action.

## Alternative K-specific local saving, kept as discovery work

After the K boundary transformation, state65 has left bit0 and state187 has
left bit1. Existing states136 and205 distinguish these contexts. Deleting187
into65 and setting65/0=0L136,65/1=1L205 yields four exact three-step blocks.
The generic symbolic checker proves all454 old rows:450 one-step blocks and4
three-step blocks. The proof quantifies over every initial binary tape, every
integer head position, and unrestricted surrounding cells.

This alternative saving was found by a scan of the exact K-derived table.
Its stage2 source has maximum zero run7. The final source repair needed to
restore maximum zero run6 changes helper205, so the accepted branch uses the
65→152 fold instead. No additional saving from65/187 is counted in K226.
The local65/187 certificate alone does not prove an executable source runtime.

## Proof boundaries

The pure local folds quantify over every initial binary tape from K start0;
this is stronger than the blank-input goal. The source transformations require
separate register-program equivalence and binary runtime proofs. The guarded
140-fold requires an extra runtime fact. Neither a shared ancestor, disjoint
literal edits, nor bounded trace agreement replaces those obligations.

The machine builder and checkers are ordinary mathematical certificates using
the Python standard library. They do not claim a new proof-assistant kernel
check of K226. The full runtime and source replay are separate from the
conditional140 explanation; the accepted exact-machine runtime theorem does
not depend on extrapolating a finite test or merely asserting that guard.

The existing K230 consistency interpretation and theorem are attributed to the
K230 authors. These transplants change the implementation of that inherited
proof search. They do not supply a new axiom system or establish unconditional
nonhalting. The exact-machine theorem remains relative to the inherited
logical calibration and the audited local/source/runtime transfers.
