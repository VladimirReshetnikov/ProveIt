# The printed CTS simulator needs its counter initialization

The Neary–Woods clockwise-machine simulator does **not** remain correct
after replacing its least-power-of-two counter by an arbitrary counter
at least the tape length. Requiring a larger counter to be dyadic is
also insufficient for the unchanged tables. This note gives small,
fully executed counterexamples to those two proposed relaxations.

This is an obstruction to reusing the printed simulation theorem with
a weaker initialization. It does not establish a universal necessity
theorem about all possible counters or simulators, and it does not
refute any existing Diophantine compiler. In particular, a spurious
CTS halt activation is not claimed to provide a complete tag-system
accepting witness or a false polynomial zero.

The [source](clockwise_cts_counter_initialization_obstruction.py) and
[receipt](clockwise_cts_counter_initialization_obstruction.json) use the
already checked literal sparse tables in the
[metadata packet](neary_woods_u15_tag_metadata.md). They compare two
different executors: individual bit deletions/appends, and an exact
acceleration that skips only intervening zero deletions.

## 1. Why the proof uses the counter value

In [the primary paper](https://dna.hamilton.ie/assets/dw/NearyWoodsBCRI-04-06.pdf),
Section3.1, equations(3)–(4) initialize the counter to the least dyadic
integer at least the tape length. Tables1.1–1.2 halve the surviving
counter and use its parity to select the next stage. On the prescribed
trajectory, the first odd surviving counter has value one. That
identification is not valid for arbitrary initial counter values.
Table2.1 simultaneously isolates the first tape symbol; Table3.1 relies
on every other tape symbol having been marked. Extra halving passes
also change the phase of counter objects, so surplus dyadic capacity
cannot simply be treated as harmless padding.

The examples below establish the failure directly from the tables,
without assuming that the primary proof extends to other counters.

## 2. A nondyadic counter produces a false halt activation

Use three clockwise states, with state1 initial and state3 halting:

| State | Read0 | Read1 |
|---|---|---|
| 1 | write0, enter2 | write1, enter3 |
| 2 | write0, remain2 | write1, remain2 |

There are no transitions from state3. Start on the circular binary tape
`01`, reading its first symbol. The clockwise machine takes the first
row's read0 transition and then remains in state2 forever. This is an
exact invariant, independent of any finite run limit.

The primary CTS has z=151, p=302 and designated halt activation
h=30·3+20=110. Let S_i denote the state object of length302 with its
single one at offset30i+20, T_0,T_1 the tape objects with ones at
offsets1,2, and mu the length151 counter object with its one at offset0.
Start the CTS marker at zero on

    S_1 T_0 T_1 mu^3.

The counter3 exceeds tape length2 but is not dyadic. The first stage
already takes the odd-counter branch, before either tape symbol has
been marked. In the first simulated transition stage both original
tape symbols therefore execute state1 transition appendants:

| CTS step before deletion | Appendant index | Effect |
|---:|---:|---|
| 3383 | 61 | append T_0 S_2 |
| 3686 | 62 | append T_1 S_3 |
| 4294 | 66 | erase a remaining prime-counter object |
| 5516 | 80 | activate the first S_2 |
| 6150 | 110 | activate S_3 |

At the S_2 cut, the exact cyclic order is
`S_2 T_1 S_3 mu mu T_0`. Thus the simulator has created a second
state object, and it reaches its designated halt activation although
the clockwise machine never enters its halt state. The receipt records
all one-events through this first S_2 cut, including appendant lengths.
All step numbers count deletions from zero; a listed activation occurs
immediately before its one is deleted.

Seven additional finite tests use tape `0^(2^j)1` and counter `3·2^j`,
for j=0,...,6. Each clockwise run still enters state2 on its first step
and never halts, whereas the corresponding literal CTS run reaches
activation110. These are seven verified instances, not a claimed
parametric theorem about every j.

## 3. An oversized dyadic counter also breaks the trajectory

Keep the same machine and tape but initialize counter4. The correct
least dyadic counter is2. The first transition is now isolated
correctly, but an extra pass leaves a prime-counter object where the
transition stage expects only marked counter objects. Specifically,
at step17894 it selects the unassigned, empty appendant76. At the first
S_2 activation, step18804, the complete object order is

    S_2 T_1 mu mu mu T_0.

The tape action is correct at this cut, but the counter has become3.
Continuing the same literal CTS run, its word becomes empty after
29777 deletions, without activating h. The actual clockwise machine
continues forever in state2. This certifies a malformed simulation
trajectory; no separate assertion about the fixed-halt tag bridge is
made. Larger dyadic counters8 and16 similarly leave7 and15 counters
at their first S_2 cuts and reach the empty word after54239 and107391
deletions respectively.

For comparison, the prescribed counter2 gives the valid first cut
`S_2 T_1 mu mu T_0` at step9140. Its bounded trace does not halt or
empty. The infinite correctness claim for this valid initialization
comes from the primary simulation theorem, not from that finite check.

The checker compares both executors on counters2,3,4,8,16 and checks
every reported event, cut and terminal status. Its first-divergence
evidence rules out dropping the counter's dyadic/minimal initialization
requirements merely by citing the existing tables. A changed simulator
or a separately proved, more restricted initialization family would
need a new argument.

```sh
python3 clockwise_cts_counter_initialization_obstruction.py
```

Author writer and fresh default passed. Substrates' independent full
proof/source/fresh-default review passed without findings. That review
reopened the primary tables, separately assembled all91 nonempty Q3
appendants, and used a bytearray/cursor executor for12 traces totaling
3,087,260 individual bit steps. All five first-S_2 cuts and prefix logs,
and all seven nondyadic-family endpoints, agreed with the receipt.

Root's final full proof/source review and fresh default replay also passed.
The claims remain confined to these exact CTS trajectories and to the
failure of the two stated initialization relaxations.
