# A phase invariant and 503 focused fold diagnostics

The checked 252-state machine and its complete original logical frontend are
unchanged. This separate experiment finds six impossible **source-program
guards** from the zero-register start, then revisits only the 503 earlier
uniform-fold recipes whose first checker rejection used one of those guards.
Every recipe is still rejected by the bounded symbolic checker. These are
checker stops, not 503 mathematical counterexamples or a state lower bound.
No new blank bootstrap or Lean invariant proof is asserted.

## Finite control with unbounded register values

The literal `Prog254.v` decoder has 6,460 leaves and 8,391 conditional cases.
The projection records the decoded leaf and nine register abstractions. Each
register mask is a subset of `{0, 1, >=2}`, rather than a bounded sample of
natural values. `None` denotes an unreachable leaf.

The control projection follows `RegisterPath.step`: the next operation acts
on `consume P d`, exactly the leaf path read by the zero-padded decoder.
`incPath` preserves path length and every zero produced by carrying; it does
not simply truncate a suffix of ones. Break and continue strip the prescribed
number of zeros and ones. The next zero-padded walk selects the successor
leaf. Thus arbitrarily many register-program iterations are represented by
cycles of this finite control graph. This analysis has no run-fuel cutoff.
Trailing-zero normalization is unnecessary for its exact control successors.

Increment maps `0` to `1`, and positive values to `>=2`. Positive decrement
maps `1` to `0`, and `>=2` to `{1, >=2}`. A zero branch filters its tested
register to `{0}`. Other registers stay unchanged; joins take componentwise
unions. These rules overapproximate every natural-valued execution. Starting
at the leaf selected by the empty PC with all nine registers zero, the
monotone worklist terminates because every leaf/register component can gain
only three bits. Correlations are forgotten, so possible does not imply
reachable.

The worklist stabilizes after 37,238 pops. Its final masks include the initial
state and are closed under all 8,384 feasible nonhalting transfer cases; the
remaining feasible case is halt. There are 6,456 possible leaves and 8,385
possible guards. The six exclusions are:

| Case | Decoded path | Exclusion |
| --- | --- | --- |
| 8202 | `111010010110001100` | Positive `CD 6`, while logical register 6 is zero. |
| 8203 | `1110100101100011010` | Unreachable `CI 5` body. |
| 8204 | `1110100101100011011` | Unreachable `CC 2` body. |
| 8358 | `111111000` | Positive `CD 1`, while logical register 1 is zero. |
| 8359 | `1111110010` | Unreachable `CI 6` body. |
| 8360 | `1111110011` | Unreachable `CC 2` body. |

These are two impossible positive-decrement guards and four unreachable
instruction leaves. The two zero-decrement guards remain included. The
claim concerns the source register program from `zeroRoot`, not arbitrary
register files or arbitrary prepared binary frames.

An independent Python audit checked all 8,391 control successors against a
direct Bool-list transcription of `RegisterPath`, the initial inclusion, and
every final-mask transfer obligation. The ordinary invariant argument is by
induction on source-program steps. It has not been formalized in Lean, and
cannot replace the existing unconditional `Covered` premise merely by
deleting six cases.

## The focused negative screen

Among the earlier full-contract uniform folds, 503 first rejections fall in
the six excluded guards: 247 recipes deleting old state 23, 248 deleting 113,
six deleting 34, and two deleting 204. The new diagnostic skips **only** those
six guards. Every other case retains its original arbitrary-value affine
contract, including the guard on the same physical decrement register.
The 55 register-box support rows, blank start 64 and dispatch rows remain
unchanged. The frozen 504-row table is read only; each local fold has 502 rows.

All 8,385 retained baseline cases pass. The 503 recipes require 519 new
candidate checks before rejection: 252 unsupported box operations, 231 fuel
cutoffs, 17 unknown affine-run lengths, and three unexpected-terminal lookup
stops. Fuel
is 1,000 symbolic steps. The first rejected cases are 8236, 8271 and 8390,
all `CC 2` operations. No provisional survivor reaches the mandatory full
8,385-case recheck, and no mutated table receives a blank run. Unsupported
abstractions and finite fuel can reject useful alternate simulations.

## Different continuations need a semantic relation

Three literal probes start from prepared frames whose register vectors obey
the computed masks. Their entire left exterior, all nine primary registers,
and all spare blocks `[0,1,0]` are inspected. The first clean dispatch frames
have these outcomes:

| Fold | Moves | Result |
| --- | ---: | --- |
| `113 -> 23` | 484 | Different PC; logical register 2 (the formula stack) increased by one. |
| `34 -> 68` | 504 | Expected PC; the formula stack increased by one. |
| `204 -> 252` | 34 | Identical primary registers and spares; different clean PC. |

The last fold illustrates a real limitation of exact-PC comparison. The
expected canonical PC is `11111111`; the returned PC is `1111110111`.
Their next source operations are `CD 6` and `CD 7`, respectively. Logical
register 7 is known zero at the original phase.

The subsequent comparison runs the **original register program** from those
two PCs. It does not continue the mutated binary machine, which may revisit
its altered decoder site. Write `tw = R1`, `p1 = R4 = n > 0`, `s1 = R6 = k`,
and `s2 = R7 = 0`, as in `L2Lib254.enc`. The expected residual moves `k` from
`s1` into `p1`, then reaches the main join. The alternate residual first copies
the initial `p1` into `tw` and `s1`, then restores `p1`. At the join, both have
`p1 = n+k` and `s1 = 0`, but the expected residual leaves `tw` unchanged while
the alternate has `tw+n`. The phase requires `n>0`, so this is a change to a
semantic formula field, not only disposable scratch. Exact traces for `n=1`
and `k=0,1,2` record that loop calculation.

This rules out the simple identity-on-registers reidentification of these
original residuals. It neither proves inequivalence of the whole mutated
machine nor rules out a different global relation. The packet supplies no
surviving candidate or new simulation theorem.

## Reproduction and evidence

Run from the repository root, without Lean or network access:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/permutation252_phase_analysis.py --output-prefix /tmp/permutation252-phase
python3 -B Computability/BusyBeaver/Research/ZFC/permutation252_continuations.py --output /tmp/permutation252-continuations.json
```

The records are
[phase masks](results/permutation252-phase-analysis.json),
[all 503 checker outcomes](results/permutation252-phase-fold-search.json), and
[literal probes and original residual traces](results/permutation252-continuations.json).
They retain source identities and independent audit scope. Attribution remains
Mira-Cult's machine, Jeff's verification, Wade's compiler, mira-emmy's public
253 reduction and the ProveIt register-permutation candidate. None changes the
separate [checked 252-state ZF endpoint](binary_perm252.md).

