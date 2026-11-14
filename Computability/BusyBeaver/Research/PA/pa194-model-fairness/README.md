# The scheduler finds every derivation, in models of IΣ₁

This directory proves, in an arbitrary model `V` of `𝗜𝚺₁`, the step of the direction
`¬Halt(M₁₉₄) → Con(PA)` that lies between the numerical calculus and the scheduler:

> if the separate-diagonal numerical calculus derives the contradiction code `1`, then the
> command scheduler meets a halting SHIFT.

Derivations, command words, candidate numbers and running times are elements of `V` and may
be nonstandard. The ordinary-number versions of these arguments are
[`pa194-derivation-compiler`](../pa194-derivation-compiler/README.md) (a derivation compiles
into a command word) and [`pa194-scheduler-fairness`](../pa194-scheduler-fairness/README.md)
(the scheduler reaches the word); they do not cover nonstandard derivations.

**Status.** The modules below are checked. They are stated for an abstract command semantics
`Sem V` and an abstract run `Run V S`. The instantiation with the modeled PA194 scheduler of
[`pa194-scheduler-iteration`](../pa194-scheduler-iteration/README.md) and with
`TargetProvable` of [`pa194-target-proof-leaves`](../pa194-target-proof-leaves/README.md) is
not in this directory yet. Nothing here concerns the physical 194-state table, the
translation of PA proofs into the calculus, or either consistency implication by itself.

## Modules

| Module | Content |
| --- | --- |
| `ConPACommandWords` | `Sem V`: a `𝚺₁` store step with its three defining equations (SHIFT, MP, AX). `tstep`, `texec`: the tracked executor of a word on a state `⟪σ, δ, f⟫` (store, stack height above the start, flag running/halted/underflow). `seqApp`: concatenation, `texec_seqApp`. |
| `ConPACommandFrame` | `follows_exec`: a run that does not underflow is the same on every base stack. `Good S W r`: from the empty store, `W` halts or leaves `r` on top of the empty stack; `G S r := ∃ W, Good S W r`, a `𝚺₁` predicate; `good_run`: a good word computes `r` over every stack and height. |
| `ConPACommandGadgets` | The words POP, PUSH, DISCARD and the window lemma for an AX followed by SHIFTs (`ax_shifts`, `ax_all`, `ax_nine`). |
| `ConPACommandClosure` | `G S` is closed under the rules: `G_leaf` (the eight leaf formulas of an AX, for `d ≤ D`), `G_axT` (the guarded gate), `G_gen`, `G_mp`. |
| `ConPAScheduler` | `encC`, `ptr`: the continuation pointer of a word. `sstep`, `shalt`: the scheduler step and its halting test. `run_inv`: started at the pointer of `W`, the scheduler executes `W`; `word_halts`. |
| `ConPASchedulerHalts` | `drain`, `reach`: every later candidate is reached. `derivation_halts : G S 1 → ∃ k, shalt (R.run k ⟪2, 0, σ⟫)`. |

## Why a tracked executor

The word for a modus ponens runs the word of one premise on a stack that already holds the
other premise, so the induction over a derivation needs each word to work on every base
stack. "For every stack" is a universal quantifier, and "there is a word such that for every
stack ..." is not a `𝚺₁` property, so it cannot be the invariant of a `𝚺₁` induction along a
derivation. The tracked executor replaces it: it runs the word once, on the empty stack,
counts the height `δ` above the starting level, and raises the underflow flag when a SHIFT
would read below that level. "The tracked run does not underflow and ends in `⟪r, 0, 0, 0⟫`
at height `0`" is a `𝚺₁` (in fact `𝚫₁`) property of the word, and the frame lemma
`follows_exec`, proved by one `𝚺₁` induction along the word, transfers it to every stack.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/pa194-model-fairness/check.sh
```

The script compiles the modules against the root Lake workspace, one `lean` process at a
time, and fails on `sorry`. The printed axiom reports are `propext`, `Classical.choice`,
`Quot.sound`.
