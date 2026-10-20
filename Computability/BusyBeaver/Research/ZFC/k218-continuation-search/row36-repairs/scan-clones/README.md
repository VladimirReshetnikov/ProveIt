# A bootstrap marker exists, but eight direct scan clones do not solve 217

The first blank-bootstrap visit to `36/0` is locally distinguishable from the
first actually reached `CD8` zero case. There is also an exact unary-scan reuse
lemma that repairs that bootstrap corner. Repurposing the eight eligible
noninitial scan states, however, produces seven concrete wrong source frames
and one bounded failure. This is a failed construction family, not a state
lower bound or an exclusion of other modified-source calibrations.

## The observed contexts

On both accepted K218 allocations, the first blank-bootstrap visit is at
step 78, state 36, head 4, with the complete one-cell set `{-3,-2}`. Relative
to the head its support is `{-7,-6}`: both immediate neighbors are zero.
The delete-301 core has exactly the same prefix. On the accepted initialized
seed, its first `CD8` zero operation instead reaches `36/0` at step 459,
head 140, with both neighbors one.

The [context recorder](inspect_contexts.py) separately records both accepted
initializations and these core prefixes. The accepted initializations have
five `36/0` visits with right neighbor zero, at steps 78, 159, 305, 470 and
1495; later recorded visits have right neighbor one. These are exact finite
observations. They are not a proof that every subsequent runtime visit has
a particular neighbor. The construction below does not assume such an invariant.

## An exact local lemma

Keep the delete-301 core's three decoder changes:

```text
87/0 = 0 R 88
88/0 = 0 L 51
51/0 = 0 R 122
```

Choose a distinct existing state `X` with `X/1 = 1 R X`, and additionally set

```text
36/0 = 0 R X
X/0  = 0 R 16
```

Suppose the head starts on zero in state 36 and the tape to its right begins
`1^n 0`, for any natural `n`, including zero. Both this replacement and the
accepted K218 path through old state 51 take exactly `n+2` steps to state 16
at the same head position. Every tape cell is unchanged: one step enters the
scan, `n` self-loop steps preserve the ones, and the final step preserves the
zero. The rest of the tape is arbitrary. This proves the conditional local
whole-tape equality for all unary lengths without finite sampling.

The literal table has eleven preserving right-one scan states. State 0 is the
initial state, and 36 or 51 would conflict with the two rows just fixed. The
eight remaining states are exactly `22,25,32,33,48,55,60,64`. All eight also
retain the original first 78 blank steps and repair the first bootstrap corner:
after step 80 they agree exactly with accepted K218 at state 16, head 6,
complete support `{-3,-2}`. This says nothing about their complete blank startup.

## Their existing roles cause the failure

[scan_clones.py](scan_clones.py) begins at the exact accepted initialized seed
and compares the full successive source frames against a fresh accepted-K218
trace. It changes only the five listed retained rows and deletes state 301.
Each run is bounded by 30,000 physical steps and twenty complete source frames.
All eight preserve the first `CD8` zero endpoint. The next reachable operations
expose the reused helpers' conflicting roles:

| Reused state | Result | Physical steps | Complete source frames |
| --- | --- | ---: | ---: |
| 22 | `CD0` incorrectly takes its zero exit | 2,474 | 2 |
| 25 | `CD0` incorrectly takes its zero exit | 2,518 | 2 |
| 32 | `CD0` incorrectly takes its zero exit | 2,490 | 2 |
| 33 | `CD0` incorrectly takes its zero exit | 2,482 | 2 |
| 48 | Decrements logical register 4 instead of 0 | 2,496 | 2 |
| 55 | Fourth operation, `CI6`, has a wrong register file | 6,690 | 4 |
| 60 | Fourth operation, `CI6`, has a wrong register file | 6,686 | 4 |
| 64 | Step bound; only the first two frames have returned | 30,000 | 2 |

The state-64 result is explicitly incomplete: it is not a cycle, divergence,
or impossibility proof. The seven wrong complete frames refute the unchanged
accepted source-interface contract for those seven tables. None is promoted
as a correctly calibrated 217-state machine.

## State 33 has no nearby distinguishing marker

Two uses of state 33/read-zero are actually reached in its modified initialized
run: the new scan role at step 461 and the preexisting `CD0` role at step 1703.
Both have head 142. Their entire tapes differ at only two cells: the old role
has a one at absolute −4, while the new role instead has a one at −1. All other
cells agree. Thus the radius-142 windows and the complete right half-tapes agree.

A deterministic context test starting at these configurations cannot distinguish
them until it reaches one of those distant cells; every preceding read, write,
state and relative movement agrees by induction. This is an exact obstruction
to a nearby-marker repair for this particular state reuse, not a claim about
all helper states or arbitrary long control-prefix inspections.

## Evidence and reproduction

All nine actual traces (baseline plus eight clones) are retained compressed in
[evidence](evidence/), along with lossless JSON results and full tape contexts.
The original scratch context comparator is preserved under [history](history/).
The first context recorder counted a detected zero-ray iteration as an executed
step (86 rather than 85); its exact source/result are retained there. The narrow
successor corrects that reporting field. The candidate traces and clone outcomes
were unaffected.

A separate [literal replay](replay.py) checks all **82,256** retained physical
transitions, the full endpoint tapes, all twenty baseline source effects, the
state-33 context identity, and another **720** transitions for the eight repaired
bootstrap corners plus the original control. Its [actual result](replay-result.json)
passed. Both implementations are by `drop_contract`; distinct code does not
constitute independent authorship.

From the repository root, with fresh output paths:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k218-continuation-search/row36-repairs/scan-clones/replay.py \
  --repo . --output /tmp/k217-scan-clone-replay-fresh.json
python3 -B Computability/BusyBeaver/Research/ZFC/k218-continuation-search/row36-repairs/scan-clones/scan_clones.py \
  --repo . --output /tmp/k217-scan-clone-discovery-fresh
python3 -B Computability/BusyBeaver/Research/ZFC/k218-continuation-search/row36-repairs/scan-clones/inspect_contexts.py \
  --repo . --output /tmp/k217-q36-contexts-fresh
```

The baseline tables, source and complete seed are the maintained
[primary K218](../../../candidate-k218/README.md) and
[contextual K218](../../../candidate-k218/alternatives/contextual/README.md).
Source 146 supplied the delete-301 core idea and its register-file distinction;
this local clone lemma, eight-candidate diagnostic and context comparison are
new work by `drop_contract`, following root's proposed bootstrap-context test.
No supplied wrapper, full runtime suite, proof compiler or broad action search
was run for this packet.
