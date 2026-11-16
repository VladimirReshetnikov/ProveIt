# Command words for the four controllers, in models of IΣ₁

The candidate machines of the PA194 family run words over three commands, SHIFT, MP and AX,
on a store `⟪t, w, d, h⟫`. They do not all use the same controller. With `b = d + x` and a
successful modus ponens (`I(t, b) = h`), the delivered packets describe four protocols:

| Protocol | Successful MP returns | SHIFT halts when | `Sem.mp` | `Sem.cacheTest` |
| --- | --- | --- | --- | --- |
| primary PA194 | `⟪b, cantor 0 w, b, 0⟫` | `t + h = 1` | `push` | `false` |
| PA194N | `⟪b, w, b, 0⟫` | `t + h = 1` | `top` | `false` |
| PA194C, PA194CS | `⟪0, w, 0, b⟫` | `h = 1` | `cache` | `true` |
| PA194H, PA194HS | `⟪b, w, b, 0⟫` | `h = 1` | `top` | `true` |

(The table is the one of `docs/pa194hs_conpa_2026-11-13/report/main.tex`; the rules of the
third row are those of `docs/pa194c_conpa_2026-11-13/reference/cached/composite_command_audit.tex`.)
A SHIFT that does not halt, the failing MP (`⟪0, w, b, 0⟫`) and AX are the same in all four.

[`pa194-model-fairness`](../pa194-model-fairness/README.md) proves, in an arbitrary model `V`
of `𝗜𝚺₁`, that the scheduler of the primary protocol meets a halting SHIFT whenever some
command word computes the contradiction code `1`, and that the formulas computed by command
words are closed under the rules of the numerical calculus. This directory is that theory
with the controller as a parameter: the fields `mp : MPKind` and `cacheTest : Bool` of `Sem`.
The theorems hold for all six combinations of the two fields, in particular for the four
protocols above.

The modules started as copies of the six abstract modules of `pa194-model-fairness`, in the
namespace `ConPA.Ctl`; the originals are kept unchanged because the proof for the primary
table is compiled against them. The differences are:

- `Sem.Halts t h` is the halting test, written `k * t + h = 1` with `k = 1` or `k = 0`
  (`Sem.k`), so that one formula defines the tracked step for both tests. `mpStore` is the
  store after a successful MP and `Sem.up` the number of stack entries it adds; the tracked
  executor `tstep` uses both, and `follows_mp` is the case of the frame lemma.
- With the test `h = 1`, a SHIFT halts on a `1` in the cache whatever the top is. POP ends
  with a SHIFT that has the kept top in the cache, so `pop_run` needs the top to be different
  from `1`, and `pop_halt` says that it halts otherwise. The words for leaves, the gate and
  generalization keep tops that are never `1`, so their runs are the same for both tests.
- `G_mp` has one word for each kind of MP. With `push`, the zero pushed by the successful MP
  is removed by the last SHIFT of the word. With `top`, the word first pushes a zero below
  the two premises, and that reserved zero is removed instead. With `cache`, the consequent
  is in the cache after the MP, and a single SHIFT moves it to the top over the reserved
  zero. In each case the last SHIFT may halt, which happens exactly when the test sees the
  code `1`; a halt counts as success in `Good`.
- The scheduler's halting predicate `shalt` uses `Sem.Halts`. To detect a computed `1`, the
  final word ends with `TEST`: one SHIFT for the test `t + h = 1`, and POP for the test
  `h = 1`.

## Modules

| Module | Content |
| --- | --- |
| `ConPACtlWords` | `MPKind`, `mpStore`, `Sem V` with the fields `mp` and `cacheTest`, `Sem.Halts`; `tstep`, `texec`; concatenation of words. |
| `ConPACtlFrame` | `follows_exec`, `Good S W r`, `G S r`, `good_run`. |
| `ConPACtlGadgets` | `not_halts`; POP, PUSH, DISCARD; `ax_shifts`, `ax_all`, `ax_nine`. PUSH and DISCARD use only the failing MP. |
| `ConPACtlClosure` | `G_leaf`, `G_axT`, `G_gen`, `G_mp`. |
| `ConPACtlScheduler` | `encC`, `ptr`, `sstep`, `shalt`, `run_inv`, `word_halts`. |
| `ConPACtlSchedulerHalts` | `TEST`, `drain`, `reach`, `derivation_halts : G S 1 → ∃ k, shalt S (R.run k ⟪2, 0, σ⟫)`. |

[`pa194-controller-schedulers`](../pa194-controller-schedulers/README.md) instantiates the
theory with PRA codes for every controller.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-command-controllers/check.sh [--out DIR]
```

compiles the six modules with `check_bridge.py` of `pa194-model-fairness`, one `lean` process
at a time, against the root Lake workspace (Foundation and `BusyBeaver.ZFC.ArithmeticCantor`
must be built there), and checks the number of axiom reports: five in `ConPACtlClosure` and
four in `ConPACtlSchedulerHalts`. They are `propext`, `Classical.choice`, `Quot.sound`.
