# Schedulers for the command controllers

The delivered candidates of the PA194 family use four command protocols (the table is in
[`pa194-command-controllers`](../pa194-command-controllers/README.md)): the primary one, the
no-push modus ponens of PA194N, the cached result with the halting test `h = 1` of PA194C
and PA194CS, and the no-push modus ponens with the test `h = 1` of PA194H and PA194HS. They
also use two layouts of the AX command: ten stack entries with the gate on top, and the
eleven entries of PA194AX11, where the gate is pushed and the command has a fourth field. A
candidate with another controller has another source program, so the arithmetic half of the
proof for the primary table does not apply to it as it stands.

This directory supplies that half at the level of commands, for all these controllers at
once. For every kind `k : MPKind` of successful MP (`push`, `top`, `cache`), every choice
`ct : Bool` of the halting test and every AX layout `a : Bool` (`true` for eleven entries) it
defines a scheduler by PRA codes and proves, in every candidate-PRA model `M` whose
arithmetic reduct satisfies `𝗜𝚺₁`:

```lean
theorem halts_iff_provable (k : MPKind) (ct a : Bool) :
    (∃ n : M, F (haltAfterK k ct a) ![n] = 1) ↔ TargetProvable (1 : M)
theorem halts_iff_primary (k : MPKind) (ct a : Bool) :
    (∃ n : M, F (haltAfterK k ct a) ![n] = 1) ↔ ∃ n : M, F haltAfter ![n] = 1
```

`TargetProvable` is provability in the numerical calculus
([`pa194-target-proof-leaves`](../pa194-target-proof-leaves/README.md)), and `haltAfter` is
the halt bit of the modeled scheduler of the primary table. With the ten-entry layout the
four protocols are `haltAfterK .push false false` (primary), `haltAfterK .top false false`
(PA194N), `haltAfterK .cache true false` (PA194C, PA194CS) and `haltAfterK .top true false`
(PA194H, PA194HS). The controller that the PA194AX11 packet describes (no-push modus ponens,
test `t + h = 1`, eleven entries) is `haltAfterK .top false true`.

`PA194ControllerSchedulerPA` composes this with
`PA194ModeledSchedulerSemanticIFF.scheduler_iff_pa_refutation` of
[`pa194/ipra/native-endpoint`](../../pa194/ipra/native-endpoint/README.md):

```lean
theorem scheduler_iff_pa_refutation (k : MPKind) (ct a : Bool) :
    (∃ n : M, F (haltAfterK k ct a) ![n] = 1) ↔ Provable (𝗣𝗔 : ArithmeticTheory) (^⊥ : M)
theorem consistency_iff_scheduler_nonhalt (k : MPKind) (ct a : Bool) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentenceK k ct a
```

The second statement is a derivation in the repository's iPRA proof system;
`haltSentenceK k ct a` says that the halt bit `haltAfterK k ct a` is `1` at some time.

**What this is not.** A scheduler here is a definition: the store step `cstepCodeK k a`, the
step `stepK k a` on packed states `⟪n, l, t, w, d, h⟫`, its iteration `runK k a` from the
initial state of the primary scheduler, and the halt bit `haltAtK ct`. Nothing connects it
with a
literal table or with the source program of a packet, and the rules of the controllers are
taken from the text of the packets; they have not been checked against the packets' source
graphs. A statement about a machine needs that connection, in the way
[`pa194/ipra/machine-code`](../../pa194/ipra/machine-code/README.md) supplies it for the
primary table. The candidates that also change the axiom emitter or the coding of formulas
are not covered: their numerical calculus is not `TargetProvable`.

## Modules

| Module | Content |
| --- | --- |
| `PA194ControllerScheduler` | `cstepCodeK`, `stepK`, `runK`, `haltAtK`, `haltAfterK`. `semK k ct a`: the command semantics of `ConPA.Ctl`; `stepK_eq`: the step code is `ConPA.Ctl.sstep (semK k ct a)`. `G_of_provable`: a target proof gives a command word (`targetProof_sound` with the closure lemmas of `ConPA.Ctl`). `cstepK_sound`, `runK_sound`: top, cache and stack entries stay provable along a run. `halts_iff_provable`, `halts_iff_primary`. |
| `PA194ControllerSchedulerPA` | `scheduler_iff_pa_refutation`; `haltSentenceK` and `consistency_iff_scheduler_nonhalt`, by the transfers of `ConPAISigma1Directions`. |

## How the two directions go

*From a proof to a halt.* A target proof of `r` is turned into a command word that leaves
`r` on top of the empty stack, by induction along the proof inside the model; the words
depend on the controller only in the rule for modus ponens and in the final test
(see `pa194-command-controllers`). The scheduler then reaches the word and runs it
(`ConPA.Ctl.derivation_halts`).

*From a halt to a proof.* Every command preserves the invariant that the top, the cache and
all stack entries are provable in the numerical calculus (`SoundStore` of
`pa194-machine-store-invariant`). A successful MP puts the consequent, which is provable by
the rule of the calculus, in the top or in the cache, and pushes at most a zero. An AX
pushes provable formulas; in the eleven-entry layout these include its gate, which is
provable when the guard allows it and is `0` otherwise. A halting SHIFT has `t + h = 1` or
`h = 1`, so one of the provable numbers is `1`.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-controller-schedulers/check.sh [--out DIR]
```

compiles both modules with every standalone module they import (`check_bridge.py` of
`pa194-model-fairness`), one `lean` process at a time, and checks the number of axiom
reports: five in `PA194ControllerScheduler`, four in `PA194ControllerSchedulerPA`. They are
`propext`, `Classical.choice`, `Quot.sound`.
