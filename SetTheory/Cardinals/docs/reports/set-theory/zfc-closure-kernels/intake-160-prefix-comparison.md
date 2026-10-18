# Pinned comparison: source57 prefix252 / rejected250 versus source58 exact prefix250

This is a source review, independent of the new machine's separate global proof review. Paths below are relative to the respective recovered packages. Source57's twelve bounded replay jobs passed; new250 verification results are recorded by its own reviewer. No Lean endpoint is asserted here.

| Feature | Source57 final prefix252 | Source57 rejected250 | Source58 new prefix250 |
|---|---|---|---|
| Canonical SHA256 | `fd09cc6c76b04e1f3eb34c5d6fec5f14bd3ef564767aae70023bb988599f3bc7` | See old-label hash below | `0626819c4842f224001e7685366d8061897a7bc9470c015129a1d1cf22efb36e` |
| Original-label SHA256 | `b91dc16e60c26780a3006072347c15ea058fa0fab6c0b4b5493967cab11c6234` | `4a33ea1c25bc8f6dea6525172fdb5e54854ffd77e1f6c7eb8415fc50d3960efe` | `fd455304bad82a6da7ab83149352d0b1db27557582c4cc6312de003c96ff4e43` |
| Main change | Phase-sensitive positive prefix decrement plus MP0 | Fold97→1 and112→3 | Share increment/decrement carry; remove43,59,85; add255 |
| Source program | Modified MP0,6441 leaves8366 guards | Earlier modified prefix program | Original6460 leaves8391 guards |
| Positive CD entry / exit |43 /63 forr0,48 otherwise | Invalid claimed equivalence |95 /48 for everyr |
| Zero CD exit | Original3 | Wrong-PC witness |112, deliberately new continuation |
| Increment spare effect | Preserves block count | Irrelevant to witnessed failure | Appends one value-one spare |
| Left-context requirement | Leading nearest-first `1^k00`,k≥1 | Claimed too broadly | Arbitrary finite left context |
| File requirement | Final startup exactly9 blocks | Witness has9 blocks,no spare | At least10 blocks; first9 primary |
| Bootstrap |25612 steps,gap43,all zero | No valid equivalence |585431 steps,gap228,dirty N1,D4,L2,210 spares |

## Why the new local contracts avoid the old obstruction

Source57 first seeks right to the selected mark, then scans backwards to a distinguished phase delimiter before shifting the prefix. Its correctness therefore needs a left-phase premise. Source58 enters carry state95 at the file origin (`code/regenerate.py`, state30/1 patch); it crosses each preceding block once and never scans the arbitrary left context before the local endpoint. The positive selected case stops at the shifted left boundary in state48 after `2*width(pre)+4` steps. The whole tape gains exactly one one at the old origin; all following values and spares are preserved.

The zero case reads the first valid block of the nonempty suffix to distinguish a marked zero from the end of the entire file. It restores the complete file and stops at the old left boundary in state112 after `2*width(pre)+7` steps. This is not the old return state3. The later112/131 scan changes the phase bits00→01 before48, and the instruction-level verifier must execute it literally. The nonempty-spare requirement is structural, not a finite bound on spare values; arbitrary finite spare values are allowed.

Increment follows the unchanged73/83 seeker, uses the same carry, and ends at the old boundary in48 after `2*width(file)+7` steps. It appends `011`, a block of value1. This is why the new global invariant uses a nonempty spare suffix and why old fixed-nine-block claims cannot be imported.

## Exact mutation and initializer

Relative to the pinned original permutation252 table, source58 changes:

```text
30/1  -> 0 R 95
75/0  -> 1 R 255
75/1  -> 1 L 63
97/0  -> 1 R 83
97/1  -> 1 L 131
109/0 -> 0 R 75
131/0 -> 0 L 48
255/0 -> 1 L 97
255/1 -> 1 L 131
```

This is seven changed retained rows plus two new-state rows, with43,59,85 removed. It retains both97 and112, unlike the rejected prototype. The exact source58 original source pin is `a3f06a2059dd786ad385079106454efb84b87d3c`; canonical start0 corresponds to old97, canonical halt250 to old254.

On75 reading0 at coordinatex, the final three-step gadget ends in131 atx−1 with bits11 if the next bit was0, and in112 atx−1 with bits01 if it was1. These two identities hold for arbitrary exterior tape. The only incoming edge to255 is75/0, which writes1 just left of255; the only incoming edge to97 is255/0, which returns to that written1. Thus every recurrent97 visit reads1, leaving97/0 available only for the initial blank step. This is an unbounded induction on transitions, not an inference from a long blank simulation.

## Reuse and remaining boundaries

The original6460-leaf program is unchanged in source58, so its existing source calibration and dirty-start theorem can be reused after proving the new binary-to-source simulation. MP0 source-bisimulation and altered proof blocks are not needed for this machine. The claimed bootstrap's logical vector `(1,0,0,0,4,0,0,0,2)` has T=W=H=X=Y=0, so the existing dirty-program theorem accepts arbitrary numeric N,D,L there. The 210 spares are finite and nonempty.

The predecessor counterexample uses a different table and an empty spare suffix excluded by the new invariant. More importantly, the exact contracts and control exits themselves have changed. Do not describe source58 as a repaired version of the same two-state fold or infer its soundness solely by avoiding that test. Its own complete tape contracts, instruction transport, literal startup and metatheoretic calibration remain the required chain.

Formalization plan: exact finite table and row bindings; universal three-step pulse/initializer invariant; unbounded file carry/rollback/return contracts; marking transport; strengthened root-frame invariant with arbitrary nonempty spares; actual all-instruction simulation and bootstrap; exact-table external consistency theorem. PA-internalized equivalence remains the user's stronger target and requires its own proof.
