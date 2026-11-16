# The scheduler with the no-push modus ponens (PA194N)

[PA194N](../../docs/pa194N_conpa_2026-11-13/README.md) is a 194-state candidate whose
controller differs from the controller of the primary PA194 table in one command. On a store
`⟪t, w, d, h⟫` with `b = d + x`, a successful modus ponens returns `⟪b, w, b, 0⟫`; the primary
controller returns `⟪b, cantor 0 w, b, 0⟫`. SHIFT (which halts when `t + h = 1`), AX, the
failing MP, the fetch and decoding of commands, and the numerical calculus are the same.
The source program is different (3,654 instruction sites instead of 3,673), so the
arithmetic half of the proof for the primary table does not apply to it as it stands.

This directory supplies that half at the level of commands. It defines the scheduler with
the no-push MP by PRA codes and proves, in every candidate-PRA model `M` whose arithmetic
reduct satisfies `𝗜𝚺₁`:

```lean
theorem haltsN_iff_provable : (∃ k : M, F haltAfterN ![k] = 1) ↔ TargetProvable (1 : M)
theorem haltsN_iff_primary :
    (∃ k : M, F haltAfterN ![k] = 1) ↔ ∃ k : M, F haltAfter ![k] = 1
```

`TargetProvable` is provability in the numerical calculus
([`pa194-target-proof-leaves`](../pa194-target-proof-leaves/README.md)), and `haltAfter` is
the halt bit of the modeled scheduler of the primary table. By
`PA194ModeledSchedulerSemanticIFF.scheduler_iff_pa_refutation` of
[`pa194/ipra/native-endpoint`](../../pa194/ipra/native-endpoint/README.md), the right-hand
side of `haltsN_iff_primary` holds exactly when arithmetic has an internal refutation. The
module that states this composition, and the corresponding sentence of iPRA, is not in the
repository yet: its imports are not all compiled on the machine where this directory was
written.

**What this is not.** The scheduler is a definition: the store step `cstepCodeN`, the step
`stepN` on packed states `⟪n, l, t, w, d, h⟫`, its iteration `runN` from the initial state of
the primary scheduler, and the halt bit of a SHIFT that finds `t + h = 1`. Nothing here
connects it with the literal PA194N table or with the source program of the packet. The
description of the MP command is taken from the packet's README and from the protocol table of
`docs/pa194hs_conpa_2026-11-13/report/main.tex`; it has not been checked against the packet's
source graph. A statement about the machine needs that connection, in the way
[`pa194/ipra/machine-code`](../../pa194/ipra/machine-code/README.md) supplies it for the
primary table.

## Modules

| Module | Content |
| --- | --- |
| `PA194NScheduler` | `cstepCodeN`, `stepN`, `runN`, `haltAfterN`. `semN`: the command semantics of [`pa194-command-controllers`](../pa194-command-controllers/README.md) with `push = false`; `stepN_eq`: the step code is `ConPA.Ctl.sstep semN`. `G_of_provable`: a target proof gives a command word (`targetProof_sound` with the closure lemmas of `ConPA.Ctl`). `cstepN_sound`, `runN_sound`: top, cache and stack entries stay provable along a run. `haltsN_iff_provable`, `haltsN_iff_primary`. |

## How the two directions go

*From a proof to a halt.* A target proof of `r` is turned into a command word that leaves
`r` on top of the empty stack, by induction along the proof inside the model. The word for
modus ponens cannot be the one used for the primary controller: there the zero pushed by the
successful MP is what the last SHIFT of the word removes. Here the word first pushes a zero
below its two premises. The scheduler then reaches the word and runs it
(`ConPA.Ctl.derivation_halts`).

*From a halt to a proof.* Every command preserves the invariant that the top, the cache and
all stack entries are provable in the numerical calculus (`SoundStore` of
`pa194-machine-store-invariant`); for the no-push MP the stack is unchanged, so the invariant
needs only that the consequent is provable. A halting SHIFT has `t + h = 1`, so one of the
two provable numbers is `1`.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194n-scheduler/check.sh [--out DIR]
```

compiles the module with every standalone module it imports (`check_bridge.py` of
`pa194-model-fairness`, about 270 modules in a fresh directory), one `lean` process at a
time, and checks that `PA194NScheduler` prints five axiom reports. They are `propext`,
`Classical.choice`, `Quot.sound`.
