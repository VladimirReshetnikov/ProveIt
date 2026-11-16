# Command words for the command controllers, in models of IΣ₁

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
A SHIFT that does not halt and the failing MP (`⟪0, w, b, 0⟫`) are the same in all four.

AX has two layouts, selected by the field `Sem.ax11`. In the ten-entry layout
(`ax11 = false`, all the protocols above) it leaves its gate `G` on top, pushes the eight
leaves, the generalization `U(d, h)` and the old top, and clears `d`:
`⟪G, [q₁, …, q₈, U(d, h), t; w], 0, 0⟫`; a command of the stream has three fields. In the
eleven-entry layout of PA194AX11 (`ax11 = true`,
`docs/pa194_ax11_research_2026-11-14/proof/ax11_preservation.tex`) it also pushes the gate,
leaves the top `0` and sets `d` to a fourth field `z` of the command:
`⟪0, [G, q₁, …, q₈, U(d, h), t; w], z, 0⟫`.

[`pa194-model-fairness`](../pa194-model-fairness/README.md) proves, in an arbitrary model `V`
of `𝗜𝚺₁`, that the scheduler of the primary protocol meets a halting SHIFT whenever some
command word computes the contradiction code `1`, and that the formulas computed by command
words are closed under the rules of the numerical calculus. This directory is that theory
with the controller as a parameter: the fields `mp : MPKind`, `cacheTest : Bool` and
`ax11 : Bool` of `Sem`. The theorems hold for all twelve combinations of the three fields,
in particular for the four protocols above in either AX layout.

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
- A command is `⟪tag, y, x, z⟫` in both layouts, and the words use `z = 0`. `Sem.n` is the
  number of entries AX pushes (ten or eleven). `itemsL` is the list of entries and `topL` the
  top after AX; `ax_shifts` is stated for a split of `itemsL`, and POP, PUSH and DISCARD use
  `Sem.n + 1`, `Sem.n - 1` and `Sem.n` SHIFTs, so the same words serve both layouts.
  `select_run` (AX, some SHIFTs, POPs of the rest) gives the leaves and the gate: in the
  eleven-entry layout the gate is the first stack entry and two SHIFTs bring it to the top.
- The seed of a command has a fourth field in the eleven-entry layout: `encCL`, `ptrL`,
  `nextLL` and `cmdL` take the layout as an argument.

## Modules

| Module | Content |
| --- | --- |
| `ConPACtlWords` | `MPKind`, `mpStore`, `Sem V` with the fields `mp`, `cacheTest` and `ax11`, `Sem.Halts`, `Sem.n`; `tstep`, `texec`; concatenation of words. |
| `ConPACtlFrame` | `follows_exec`, `Good S W r`, `G S r`, `good_run`. |
| `ConPACtlGadgets` | `not_halts`; `itemsL`, `topL`; POP, PUSH, DISCARD; `ax_shifts`, `ax_all`, `ax_nine`. PUSH and DISCARD use only the failing MP. |
| `ConPACtlClosure` | `select_run`; `G_leaf`, `G_axT`, `G_gen`, `G_mp`. |
| `ConPACtlScheduler` | `encCL`, `ptrL`, `nextLL`, `cmdL`; `sstep`, `shalt`, `run_inv`, `word_halts`. |
| `ConPACtlSchedulerHalts` | `TEST`, `drain`, `reach`, `derivation_halts : G S 1 → ∃ k, shalt S (R.run k ⟪2, 0, σ⟫)`. |

[`pa194-controller-schedulers`](../pa194-controller-schedulers/README.md) instantiates the
theory with PRA codes for every controller.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-command-controllers/check.sh [--out DIR]
```

compiles the six modules with `check_bridge.py` of `pa194-model-fairness`, one `lean` process
at a time, against the root Lake workspace (Foundation and `BusyBeaver.ZFC.ArithmeticCantor`
must be built there), and checks the number of axiom reports: five in `ConPACtlClosure` and
four in `ConPACtlSchedulerHalts`. They are `propext`, `Classical.choice`, `Quot.sound`.
