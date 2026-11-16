# Command words for more than one controller, in models of IΣ₁

The candidate machines of the PA194 family run words over three commands, SHIFT, MP and AX,
on a store `⟪t, w, d, h⟫`. They do not all use the same controller. With `b = d + x` and a
successful modus ponens (`I(t, b) = h`), the delivered packets describe four protocols:

| Protocol | Successful MP returns | SHIFT halts when |
| --- | --- | --- |
| primary PA194 | `⟪b, cantor 0 w, b, 0⟫` | `t + h = 1` |
| PA194N | `⟪b, w, b, 0⟫` | `t + h = 1` |
| PA194C, PA194CS | `⟪0, w, 0, b⟫` | `h = 1` |
| PA194H, PA194HS | `⟪b, w, b, 0⟫` | `h = 1` |

(The table is the one of `docs/pa194hs_conpa_2026-11-13/report/main.tex`.)

[`pa194-model-fairness`](../pa194-model-fairness/README.md) proves, in an arbitrary model `V`
of `𝗜𝚺₁`, that the scheduler of the primary protocol meets a halting SHIFT whenever some
command word computes the contradiction code `1`, and that the formulas computed by command
words are closed under the rules of the numerical calculus. This directory is that theory
with the controller as a parameter. **So far the parameter covers the first two rows**: the
field `push : Bool` of `Sem` says whether a successful MP pushes a zero. The halting test
`h = 1` and the MP that returns its result in the cache are not covered.

The modules are copies of the six abstract modules of `pa194-model-fairness` under new names
and in the namespace `ConPA.Ctl`; the originals are kept unchanged because the proof for the
primary table is compiled against them. The differences are:

- `Sem.push`, `Sem.up` (the number of stack entries a successful MP adds) and `Sem.mpW` (the
  stack after it); the tracked executor `tstep` raises the tracked height by `Sem.up`;
- `sameTop_mp` in the frame lemma `follows_step`;
- `G_mp`. With the push, the word is the one of `pa194-model-fairness`: the zero that the
  successful MP pushes is removed by the last SHIFT of the word. Without the push, the word
  first pushes a zero below the two premises, and that reserved zero is what the last SHIFT
  removes. `mpsuf2_tail` is the common part of the two runs.

## Modules

| Module | Content |
| --- | --- |
| `ConPACtlWords` | `Sem V` with the field `push`; `tstep`, `texec`; concatenation of words. |
| `ConPACtlFrame` | `follows_exec`, `Good S W r`, `G S r`, `good_run`. |
| `ConPACtlGadgets` | POP, PUSH, DISCARD; `ax_shifts`, `ax_all`, `ax_nine`. These use only the failing MP, which is the same in both protocols. |
| `ConPACtlClosure` | `G_leaf`, `G_axT`, `G_gen`, `G_mp` for both values of `push`. |
| `ConPACtlScheduler` | `encC`, `ptr`, `sstep`, `shalt`, `run_inv`, `word_halts`. |
| `ConPACtlSchedulerHalts` | `drain`, `reach`, `derivation_halts : G S 1 → ∃ k, shalt (R.run k ⟪2, 0, σ⟫)`. |

[`pa194n-scheduler`](../pa194n-scheduler/README.md) instantiates the theory with
`push = false`.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-command-controllers/check.sh [--out DIR]
```

compiles the six modules with `check_bridge.py` of `pa194-model-fairness`, one `lean` process
at a time, against the root Lake workspace (Foundation and `BusyBeaver.ZFC.ArithmeticCantor`
must be built there), and checks the number of axiom reports: five in `ConPACtlClosure` and
four in `ConPACtlSchedulerHalts`.
