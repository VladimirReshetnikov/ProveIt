# Machine reduction experiments at the checked 252-state baseline

These experiments found no 251-state consistency machine. They investigate
the literal permutation252 table at ProveIt commit
`fab89c5d26b81cd2ccab2ee5d213ff23725c7726`, rather than assuming that negative
experiments on the older public253 table transfer to it.

## Exhaustive arbitrary-row fusions

Choose any pair of working states, merge them, and synthesize both rows of
the retained state freely. Every incoming target of the removed state is
redirected, and the initial state is redirected if necessary. There are
31,626 unordered state pairs and 1,008 possible actions for each new row:
two writes, two moves, and 251 remaining working targets plus the halt target.
Thus each census covers 32,134,040,064 recipes under its bounded acceptance
criterion. Choosing the other retained label gives an isomorphic recipe.

The input is a deterministic, one-head, binary, bi-infinite blank-tape
machine. The 252 working states exclude the terminal state. The supplied
old-label table has initial label 64 and terminal label 254. Preparation
renames initial 64 to 0 and the terminal to 252 without changing any behavior.

For a radius r, a finite fixed point computes possible pairs consisting of
the control state and the 2r+1 tape cells centered on the head. It starts at
the actual blank configuration. Each shift admits both values of the newly
exposed exterior cell, so induction covers the entire infinite run, without
a simulation-time cutoff. These are possible windows, not assertions that
every admitted window actually occurs.

For each admitted window at either merged state, the original and fully
modified machine must match after positive numbers of moves, at most 64 on
each side. Matching preserves the head and all known tape cells and maps
only the removed control label to the retained label. Neither prefix may
read beyond its known window. Two terminal outcomes may match regardless
of final tape contents. Unchanged states have immediate one-step matches.
This gives a sound positive-progress block certificate for blank-tape
halting equivalence if a recipe passes.

The census uses exact partial evaluation. When one proposed row is tested,
the other is unknown. A trace requesting the unknown row is unresolved;
a failure reached before that request rejects every completion. Remaining
action pairs receive simultaneous checking against both modified rows.
There is no assumption that separately valid detours compose.

Radius six found zero certificates. Its closed abstraction contains 330,625
state/window pairs. The run evaluated 426,101,486 partial contexts, then
222,986 complete recipes in 7,433,103 complete-context checks. The result is
exhaustive for this local criterion in the stated fusion family. It is not
a state lower bound or a proof of semantic inequivalence for rejected tables.

Radius eight likewise found zero certificates. Its fixed point contains
3,789,234 state/window pairs. It evaluated 4,379,321,106 partial contexts,
then 253,524 complete recipes in 101,691,837 complete-context checks. The
full per-pair ledgers of both runs are in `results/`. The compiled search is
deterministic. The original eager and new lazy implementations produce
identical full radius-six ledgers and all identical functional aggregates.
The lazy change only delays constructing an original trace until its first
use; it does not change the trace, pruning rule, iteration order, or domain.
The final portable radius-six replay reproduces every saved ledger byte.
An independent Python checker validates all 7,577,444 successor obligations
of the radius-eight fixed point and its actual initial state. The inherited
small-machine differential suite also passes for the lazy C++ variant:
all 7,936 recipes agree with unpruned Python enumeration, including 3,768
positive certificates.

## Joint decoder reassociation and register permutation

Source27 supplied closed-block decoder rotations for public253. Here all
238 single rotations are reapplied jointly with the exact physical register
permutation underlying permutation252. The order matters: remove state 5
by redirecting it to 64 before permuting selector-entry targets.

The baseline is reconstructed exactly. All 8,391 conditional affine
instruction cases pass, and a literal 82,552-step blank run reaches the
entire published root frame. That frame includes nine zero registers,
all 65 spare blocks, the single nonzero spare at index 8, and blank exterior.
The four inherited register-box contracts retain their original 55 support
rows. This Python use of the contracts is not a new Lean kernel check.

Among the 238 rotations, 153 pass all affine cases, 59 exceed the declared
shape bound, and 26 encounter a bounded checker failure. The implemented
runtime-state retention rule gives at least 252 working states for every
passing table. Five attain 252: options 0, 233, 235, 236, and 237. The option-0
table also reaches exactly the baseline's complete frame after 82,552 steps.
It improves neither the working-state count nor that startup duration.

Failures include unsupported symbolic operations and finite fuel cutoffs;
they do not prove that a different simulation relation is impossible. The
state-retention rule is sufficient and deliberately conservative. A table
with a reported retention count above 251 is not proved incapable of further
semantic minimization.

A further stochastic search composes multiple closed-block rotations and
uses exact literal graph reachability as its cost. Any proposed graph with
at most 251 states would still require the complete affine and blank-frame
checks before promotion. Seeds, actual iteration counts, accepted mutations,
and graph-size histograms are recorded. The two runs tested 20,000 and
46,413 proposals, with 603 and 1,278 accepted mutations respectively; their
seeds were 20261017 and 20261018. Both retained a best graph size of 252.

## Reproduce

Python 3.11+ and a C++17 compiler are sufficient. There is no network access,
proof-assistant invocation, or dependency installation in these commands.
Executables and large regenerated window files remain in temporary storage.

```sh
python3 code/reproduce.py --quick
python3 code/reproduce.py --radius 6 8
python3 code/reproduce.py --radius 6 --compare-eager
python3 code/joint_rotation_search.py --runtime-only --seconds 1000000 \
  --output /tmp/zfc252-single-rotations.json
python3 code/joint_rotation_search.py --single 0 --seconds 1000000 \
  --output /tmp/zfc252-rotation0.json
```

The default `reproduce.py` invocation checks the exact table fingerprint,
baseline affine cases, full bootstrap, radius-six abstraction against an
independent sparse Python implementation, and the full radius-six fusion
ledger. `--radius 6 8` also reproduces the larger census. It compares all
functional counts and every TSV byte with the supplied results. Elapsed time
is excluded from comparisons.

To repeat a stochastic run on a host with a different speed, use its saved
seed and actual iteration count, with a generous `--seconds` bound. The
reported wall-time-limited run is not advertised as exhausting all rotation
compositions.

## Attribution and proof boundary

Mira-Cult supplied the original machine and calculus; Jeff supplied its
verification; Andrew James Wade supplied the compiler framework; mira-emmy
supplied public253. ProveIt supplied the register-permutation252 candidate
and its checked endpoint. The source27 emitter and affine checker, and the
incoming finite-window fusion algorithm, are explicitly inherited.

The new work is the joint252 rotation experiment, the two new252 fusion
censuses, the compact independent abstraction implementation, and the lazy
construction of context traces. There is no claim to have invented the
baseline table, the earlier source27 rotation, or the finite-window
block-simulation method. Exact source pins and file hashes are recorded in
`PROVENANCE.json`. Existing licenses are retained.

No 251-state candidate, new consistency calibration, PA formalization, or
new complete Lean build is claimed by this packet. Its negative results
identify an exhausted finite search family; a useful next reduction must
leave that family, strengthen the accepted relation, or use more global
program transformations.
