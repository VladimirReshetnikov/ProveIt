# Bounded state-reduction experiments

This folder records the additional reduction work for the three delivered
194-state machines. **No 193-state candidate passed these searches.**
These are finite searches of explicit transformation families. None is a
lower-bound theorem for PA-consistency machines, or a substitute for the
machine/refutation proof in iPRA.

## Reproduce

Python 3 and a C++17 compiler suffice. From the package root:

```sh
python3 -B research/state_reduction/replay.py --output /tmp/pa194-search-replay
```

This compiles the included C++ sources, checks input hashes, reruns the
coarse and literal-envelope quotient searches for all three new tables,
and repeats the 83/190 helper-row experiment. It requires no network access.
The default reuses the hash-bound literal envelopes, whose complete
regeneration logs and receipts are included. To reconstruct the envelopes
from symbolic literal execution as well, add `--regenerate-contexts`.
To repeat the separate fixed-source experiments, add `--fixed-rotations`.
The latter also reproduces the expected failure of the naive 19/29 rotation.

Execution times depend on the host. The searches themselves take seconds
to tens of seconds; full literal-envelope regeneration takes several minutes.

## 1. Quotients of the new machines

Inputs are the exact native tables for `GD_SF`, `GDH_SF`, and `GDHS_SF`,
with their unchanged source programs. Each has 194 working controls.
For each table, the following transformations were searched using
radius-six windows (thirteen tape cells):

| Family | Exhausted finite choices | Local bounds |
|---|---:|---|
| Joint return quotient | All 18,721 unordered control pairs | Up to 100 new transitions reproduce one old transition; the merged state may be revisited |
| Positive stuttering quotient | All 18,721 unordered control pairs | A positive new trace of length at most 128 meets a positive old trace of length at most 12 |
| Incoming-edge deletion | All 193 non-start controls | Replace every incoming action, using endpoints within 24 old and 256 new transitions |

Each transformation must preserve the complete observed window and head
position at its matched endpoint. The edge-deletion search forbids a
replacement detour from crossing another concurrently modified incoming
row. These restrictions make the families precise and account for some of
their incompleteness.

Every search was first run on the finite-window closure from the blank
initial window, allowing either new boundary bit at every shift. It was
then run on a separately generated source envelope. The latter includes
all source-instruction branches over symbolic register values, the
interiors of accelerated unary scans and arbitrary finite register-list
scans, and every state of exact blank initialization. Independent affine
and list parameters are deliberately decoupled: the result is an
overapproximation, not a sample of register values. The collector uses the
independent literal table engine, not an arithmetic-box oracle.

The source-envelope argument and its generator remain executable
mathematical evidence. They are not a new kernel-checked Lean theorem.
Negative search results need no claim that their context sets are exact;
they exclude only the declared certificate families with those contexts.

The regenerated literal envelopes have these sizes:

| Machine | Source sites | Source outcomes | Radius-six windows |
|---|---:|---:|---:|
| GD_SF | 3,654 | 4,755 | 50,132 |
| GDH_SF | 3,653 | 4,754 | 50,189 |
| GDHS_SF | 3,650 | 4,750 | 50,304 |

`frontier/summary.json` records the nine coarse runs.
`frontier/refined_summary.json` records the nine literal-envelope runs.
Their input hashes, context counts, precise trial counts, and raw search
logs are included. The two pair families test 112,326 machine/pair/family
instances per envelope regime; the deletion family tests 579 controls per
regime. No hit was returned.

## 2. A merge with one additional helper-row change

In the supplied `PA194LCG` machine, native controls 83 and 190 share the
read-one action `0 L 42`. On reading zero, their actions are respectively
`0 R 93` and `0 R 99`. Their source histories distinguish them at the third
cell to the left, while the intervening two cells are ones.

The new experiment removes 190 in favor of 83 and retains the common
read-one action. It chooses the merged read-zero action freely from all
772 write/direction/working-target actions, and additionally permits one
other non-arithmetic row to change. Possible helper rows are collected
from the unmodified-helper orbits of **all 256** radius-five windows with
the required preceding bits and read-zero center. This covers the possible
first encounter with a changed helper row; a solution that never encounters
its helper is checked separately as a no-helper solution.

For each candidate, every one of the 256 windows must reach the appropriate
old endpoint, with the entire window unchanged, within 80 transitions.
The search tried **18,318,203** joint action choices and found none.
The 23 protected arithmetic controls, the start control, and the merged
control itself are excluded as helper rows. Targets are surviving working
controls. The unrestricted exterior bits make this a deliberately stronger
local requirement than some source-specific invariant might justify.

This extends earlier 83/190 tests that held every surviving helper row
fixed. It does not exclude a construction that changes two helper rows,
changes the common read-one action, uses a larger window or time bound,
or exploits stronger source-history restrictions.

## 3. Fixed-source association experiments

The separate fixed-core exploration mapped 86 decoder controls to named
source subtrees. It found 14 single rotations outside the AX emitter that
preserve the complete resolved 3,673-instruction graph. All 2,915 nonempty
subsets whose modified control pairs are disjoint were examined for an
additional last-bit contextual fold, retaining the existing seven AX
folds. None produced such a fold.

These are **source-preserving candidates**, not 14 verified physical
implementations. Existing fixed-core history folds can depend on precisely
the addresses that reassociation changes. In particular the naive 19/29
rotation preserves the resolved program but fails the symbolic physical
contract at source site 50, on the zero branch of logical register 1
(physical register 2), after 70 completed contracts. The same experimental
rotation already occurs in the supplied corpus. It is retained here as a
reproduced rejection, not promoted as a new machine. This is why preservation
of the opcode word or even the resolved source graph is insufficient by
itself.

The files in `fixed_rotations/` preserve both the preliminary finite search
and its explicit failure. They supply no additional delivered machine.

## Attribution

The three generic quotient search engines, literal-envelope collector,
and independent symbolic runtime are reused from
`docs/incoming/pa194_loop_return_2026-11-14.zip` at pinned ProveIt commit
`e6a84f8dd2702f5f8c7db3ca53a8cbacb1d89f4f`. Their licenses are retained in
`frontier/reference/`. The baseline compiler, source mapping, and symbolic
contract checker come from the primary PA194 packet and James Chang's
imported PA196 development. `PROVENANCE.json` gives the exact source paths.
The fresh applications, helper-row synthesis, and documented fixed-source
combination experiment are the work added in this package.
