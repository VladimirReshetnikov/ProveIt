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
primary table. The same holds for the schedulers with a variant emitter below.

## Variant axiom emitters

Other candidates change entries of the AX command. Five of these changes are independent of
each other, of the command protocol and of the AX layout; `Emitter` of
`PA194EmitterSchedulerCore` has one field for each, with default `false`. With `A` the label
argument of the command, `D = d + x`, `H = h + y`, `W(D,H) = U(D, E(H,D) → 1)`, and
`V = V(H,D,A)`, `Q = Q(H,D,A)` the two parts of the gate of the primary table:

| Field | Entry | Primary | Variant |
| --- | --- | --- | --- |
| `gd` | separate diagonal | `Γ(A)` | `Γ(D)` |
| `q` | sixth head | `U(D,A) → (U(D,A→H) → U(D,H))` | `U(D,A→H) → (U(D,A) → U(D,H))` |
| `x` | fifth head | `W(D,H) → 1` | `W(D,H) → A` |
| `ga` | generalization | `U(d, h)` | `U(A, h)` |
| `bundled` | gate, diagonal | `¬(V → Q)`, `Γ` pushed | `¬(Γ(A) → (V → Q))`, no `Γ` pushed |

With `bundled`, AX pushes seven leaves instead of eight (nine stack entries when the gate is
the top). This is the emitter of the original PA195, from which the primary table was
obtained by separating the diagonal.

For every emitter `e`, with `k`, `ct` and `a` as above:

```lean
theorem halts_iff_provable (e : Emitter) (k : MPKind) (ct a : Bool) :
    (∃ n : M, F (haltAfterE e k ct a) ![n] = 1) ↔ TargetProvable (1 : M)
theorem halts_iff_primary (e : Emitter) (k : MPKind) (ct a : Bool) :
    (∃ n : M, F (haltAfterE e k ct a) ![n] = 1) ↔ ∃ n : M, F haltAfter ![n] = 1
theorem scheduler_iff_pa_refutation (e : Emitter) (k : MPKind) (ct a : Bool) :
    (∃ n : M, F (haltAfterE e k ct a) ![n] = 1) ↔ Provable (𝗣𝗔 : ArithmeticTheory) (^⊥ : M)
theorem consistency_iff_scheduler_nonhalt (e : Emitter) (k : MPKind) (ct a : Bool) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentenceE e k ct a
```

The first two are in `PA194EmitterScheduler`, the last two in `PA194EmitterSchedulerPA`.
The numerical calculus is not changed: every scheduler is compared with `TargetProvable`,
the calculus of the primary table.

*Soundness.* Every entry of a variant AX is provable in that calculus: the exchanged sixth
head by the exchange law `(a → (b → c)) → (b → (a → c))` of the implication basis
(`PA194ModelPropositional.imp_exchange`), `W → A` from the fifth head and explosion, and
`U(A, h)` by generalization of the provable cache `h`, and the bundled gate `¬(Γ → X)` from
`Γ(A)` and the gate `¬X` of the primary table.

*Completeness.* The formulas that a scheduler computes are closed under modus ponens and
contain the restricted row, so the generic derivation `M6.Logic.RestrictedImplication`
applies to them (`rulesG`) and its exchange law gives the sixth head back. The fifth head
is `W → A` at `A = 1`. `Γ(B)` is the diagonal entry of an AX with `D = A = B`. The
generalization word of `pa194-command-controllers` uses an AX whose label argument equals
the register `d`, so it computes `U(i, a)` with either binder. From a bundled gate
`¬(Γ → X)`, the gate `¬X` follows by `X → (Γ → X)`, and `Γ` follows by Peirce's law and
explosion `1 → Γ`, which the first head and `K` supply (`G_explosion`). Every `Γ(B)` is in
the gate with the arguments `(B + 1, B + 1, B)`, whose guard `B ≠ B + 1` holds.

The table lists the emitter, the kind of MP, the halting test and the layout that the
proof documents of the packets under `docs/` state for some candidates. The table follows
the displayed command equations of those documents; it has not been compared with the
packets' source graphs or tables.

| Candidate | Document | `gd` | `q` | `x` | `ga` | `bundled` | `k` | `ct` | `a` |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| PA194Q | `pa194q_conpa_2026-11-13/report/calibration_q.tex` | | ✓ | | | | `cache` | ✓ | |
| PA194DHS | `pa194dhs_conpa_2026-11-13/report/proof_dhs.tex` | ✓ | | | | | `top` | ✓ | |
| PA194G | `PA194B_PA194G_research_2026-11-14/generalizer/proof.tex` | | ✓ | | ✓ | | `top` | | |
| PA194GH | `pa194gh_research_2026-11-14/machines/PA194GH/proof.tex` | | ✓ | | ✓ | | `top` | ✓ | |
| GD | `pa194_gd_research_2026-11-14/report/gd_calibration.tex` | ✓ | | | ✓ | | `top` | | |
| GDH, GDHS | the same | ✓ | | | ✓ | | `top` | ✓ | |
| PA194AX11G | `pa194_ax11g_research_2026-11-14/proof/ax11g.tex` | | ✓ | | ✓ | | `top` | | ✓ |
| PA194AX11GH | `pa194_ax11gh_research_2026-11-14/proof/ax11gh_preservation.tex` | | ✓ | | ✓ | | `top` | ✓ | ✓ |
| PA194AX11GDH | `pa194_ax11gdh_research_2026-11-15/proof/ax11gdh_preservation.tex` | ✓ | | | ✓ | | `top` | ✓ | ✓ |
| PA194H5X | `pa194_witness_research_2026-11-15/report/implementation_proof.tex` | | | ✓ | ✓ | | `top` | ✓ | ✓ |
| original PA195 | `pa195_conpa_2026-11-13/report/sections/pa_calibration.tex`, `pa195/build_verify.py` | | | | | ✓ | `push` | | |
| PA195DC | `pa195_diagonal_combined_2026-11-13/report/sections/commands.tex` | | | | | ✓ | `cache` | ✓ | |
| composite, nine entries | `PA195_ConPA_research_2026-11-14/independent_verification/composite_command_audit.tex` | | | | | ✓ | `cache` | ✓ | |
| composite, ten entries (195C) | the same | | | | | | `cache` | ✓ | |

The scheduler for the original PA195 is `haltAfterE { bundled := true } .push false false`
(for its AX the table follows the free-algebra identity that the packet's
`build_verify.py` checks: stack `[h₆, …, h₁, ρ, U(d,h), t]`, top `¬(Γ(A) → (V → Q))`). The
scheduler for PA194AX11GH is
`haltAfterE { q := true, ga := true } .top true true`. The emitter with exchanged sixth
head is also used by PA194QH, PA194QN, PA194QNS and PA194AX11QH, and `Γ(D)` by PA194D;
their command protocols have not been matched against their packets here.

All these schedulers fetch and decode commands as the modeled scheduler of the primary
table does (the pair `(n, l)` and its seed, from the same initial state). For the original
PA195 the packet says that its scheduler is the one of PA196 with the AX block replaced; it
has not been checked here that this is the same enumeration of commands. The comparison
with `TargetProvable` does not depend on the enumeration, but a proof about the literal
table has to match it.

Not covered: PA194JH5X, which also replaces the first head; the fused head of the FW
candidates; the gate of PA196, which bundles equality vacuity instead of the diagonal and
belongs to another calculus; and the candidates with another coefficient of the formula
constructors.

## Modules

| Module | Content |
| --- | --- |
| `PA194EmitterSchedulerCore` | `Emitter`; the codes `head6Q`, `head5X`, `bundledGate`, `axStackCodeE`, `axTopCodeE`, `stepE`, `runE`, `haltAfterE`. Only codes; imports `PA194ControllerSchedulerCore`. |
| `PA194EmitterScheduler` | `baseLeaf`, `leafE`, `genLE`, `axStackE`, `axTopE` and their model lemmas; `semE e k ct a`, `stepE_eq`; `G_base`, `rulesG`, `G_head6`, `G_head5`, `G_explosion`, `G_gate`, `G_diagonal`, `G_of_provable`; `leafE_provable`, `axTopE_provable`, `axE_preserves`, `runE_sound`; `halts_iff_provable`, `halts_iff_primary`. |
| `PA194EmitterSchedulerPA` | `scheduler_iff_pa_refutation`; `haltSentenceE` and `consistency_iff_scheduler_nonhalt`. |
| `PA194ControllerSchedulerCore` | The PRA code definitions for the scheduler step, its iteration, and its halt test, independent of the fairness and PA-interpretation proofs. |
| `PA194ControllerScheduler` | `cstepCodeK`, `haltAfterK`; imports the shared core. `semK k ct a`: the command semantics of `ConPA.Ctl`; `stepK_eq`: the step code is `ConPA.Ctl.sstep (semK k ct a)`. `G_of_provable`: a target proof gives a command word (`targetProof_sound` with the closure lemmas of `ConPA.Ctl`). `cstepK_sound`, `runK_sound`: top, cache and stack entries stay provable along a run. `halts_iff_provable`, `halts_iff_primary`. |
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

compiles all six modules with every standalone module they import (`check_bridge.py` of
`pa194-model-fairness`), one `lean` process at a time, and checks the number of axiom
reports: three in each `…Core` module, five in `PA194ControllerScheduler` and in
`PA194EmitterScheduler`, and four in `PA194ControllerSchedulerPA` and in
`PA194EmitterSchedulerPA`. They are `propext`, `Classical.choice`, `Quot.sound`.

For a staged replay of the lightweight core against already checked providers, run
`./check-core.sh PROVIDER-LEANPATH-FILE FRESH-OUTPUT` from this directory.
