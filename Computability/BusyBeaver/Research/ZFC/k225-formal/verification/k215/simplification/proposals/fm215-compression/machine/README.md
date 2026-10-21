# FM215: a four-row predecessor-selector variant

This packet constructs a materially distinct 215-working-state binary machine
whose correctness transfers from the exact formally verified primary K215 by
a short whole-tape simulation. It does not supply a 214-state construction.

The base repository is pinned at `b6c7087477e51c017003bd729e712c8969733223`.
The parent is `candidate-k215/k215.native.tm`, SHA-256
`9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`.
The parent is included unchanged as `tables/00.tm`; all inherited numerical
calculus, ZFC calibration, original compiler and exact-parent formal proof
remain contributions of the upstream development. This packet adds the
four-row transformation, its local simulation proof and executable evidence.

## Exact patch and count

| Native row | Primary K215 | FM215 |
|---|---|---|
| 124 / 0 | 0 R 62 | 0 L 127 |
| 127 / 0 | 0 R 14 | 0 R 8 |
| 127 / 1 | 1 R 138 | 1 R 109 |
| 110 / 0 | 0 R 127 | 0 R 124 |

All other rows are unchanged. The two old decoder roles 124 and 127 now share
physical control 124; physical control 127 is reused as an origin selector.
Both controls still exist, so this merger saves no physical state.

`fm215.native.tm` has 215 working labels, start 0, dispatcher 84, separate halt
254, and 430 rows. `fm215.tm` has working labels 0 through 214, start 0,
dispatcher 83 and halt 215. `canonicalization.json` supplies the exact
renaming. The convention is one two-way infinite zero-initialized binary tape
and L/R moves only; the halt is excluded from the working-state count.

Native SHA-256: `3ece1233f11d33375425221c5bcedba941e073763912990eabf321197772dce5`.

Dense SHA-256: `1b602d3b37887060ce2d992cf3036f540e8ccff5d37ab06c80f19f1edd38cbc6`.

## Ordinary mathematical proof

Let a configuration consist of control q, head h and an arbitrary complete
binary tape t. Let phi(127)=124 and phi(q)=q for every other old control.
The relation between old and new boundary configurations preserves h and t
exactly and applies phi only to q.

The old machine has exactly one incoming row to old 124, namely
104/1 = 1 R 124, and exactly one incoming row to old 127, namely
110/0 = 0 R 127. Neither is the initial control. Consequently every old run
from control 0, on every initial tape, satisfies the invariant

* q=124 implies t(h-1)=1;
* q=127 implies t(h-1)=0.

This is a one-step induction: the last transition into the control writes
the specified marker immediately to the left. It requires no source-code
well-formedness, register invariant, arithmetic assumption, or startup
analysis.

On current symbol 1, both old controls take 1 R 138. Their merged control 124
does exactly the same. On current symbol 0, new 124 takes 0 L 127. If the old
control was 124, the predecessor marker is 1, and the new continuation is

124 -> 127 -> 109 -> 62.

If the old control was 127, the marker is 0, and the continuation is

124 -> 127 -> 8 -> 14.

The literal provider rows are 109/0=0 R 62 and 8/0=0 R 14. In both cases
the three-step block leaves the entire tape unchanged and moves the head
one cell right, exactly as the old one-step transition. No exterior cell
is read or written. At all other old controls, the new machine takes the
same single step modulo phi; the changed row 110/0 is exactly the necessary
target redirection. The overwritten rows of new 127 are helper rows rather
than boundary representatives of old 127.

Induct on the old run. Each old step has an exact new simulation of length
one or three. For the first t old transitions, let z(t) count visits to
old 124/0 or old 127/0. The corresponding new clock is exactly

tau(t) = t + 2 z(t), with t <= tau(t) <= 3t.

The simulation segments never halt internally. Their endpoints agree on
whether the control is halt 254, since phi fixes the halt and maps no
working state to it. Positive segment lengths imply tau(t) is unbounded
when the old run is infinite. Hence both finite halting and infinite
nonhalting correspond. This proves, for every initial tape at control 0,

Halts(FM215,tape) iff Halts(K215,tape).

Specializing to the blank tape and composing with the inherited exact K215
theorem gives the ordinary ZFC-formalizable statement

ZFC proves: not Halts(FM215,blank) iff Con(ZFC).

The companion Lean proof has been kernel checked: it proves this all-tape
halting equivalence from state 0 for every integer head position and every
complete Boolean tape. Its reported axiom dependencies are `propext` and
`Quot.sound`. The exact 430-row parent and new tables are separately bound
to the literal definitions by a complete finite check. The repository's
native/dense/zipper endpoint bridge is not separately kernel compiled in
that companion; composing with the inherited ZFC endpoint uses the stated
ordinary representation argument. The ordinary proof above does not infer
unbounded correctness from finite simulation.

## Why this variant is particularly simple to formalize

There are two one-step incoming-edge facts, two three-step blocks, one
control-map equation, and a reusable positive simulation theorem. No extra
case such as the existing conditional-marker variant's two-step 189/1 to
156/1 origin needs to be reconstructed. The new proof can import the old
K215 endpoint and add a small verified adapter. This shortens the additional
proof of this variant; it does not erase the dependency closure of the
original K215 proof.

## Actual validation

`verify_fm215.py` checks the exact four-row patch and incoming-edge facts,
all 1,712 relevant three-cell local split cases, whole-tape framing,
positive one/three-step clocks, state count and exact dense renaming.
It synchronizes every step of the complete parent 95,714-step blank prefix
with the new run. There are 63 stretched visits, hence FM215 takes 95,840
steps to the identical complete calibrated tape: native dispatcher 84,
head -8 and 95 one-cells, all other cells zero. The complete list of one
positions is in `fm215_checks.json`; the inherited parent endpoint gives
registers [4,0,0,0,0,0,0,0,0], gap one and forty unit spares.

The current-tree comparison in `novelty_current_tree.json` reads all 622
`.tm` paths in the pinned ZFC tree. It finds 321 complete graph-reachable
215-state tables representing 84 rooted transition graphs. FM215 matches
none, even when global left/right reflection is allowed. Every input has
its exact current Git blob ID and SHA-256 recorded. This is an explicit
finite corpus comparison, not a claim about all unpublished constructions.

## Reproduction

Python 3.10 or newer suffices for the construction and finite certificate.

```sh
python3 -B verify_fm215.py
python3 -B build_fm215.py --output /tmp/fm215-new-reconstruction
python3 -B verify_novelty.py --repo /path/to/pinned/ProveIt
node search_markers.mjs /tmp/fm215-marker-search.json
node search_full_windows.mjs /tmp/fm215-full-window-search.json
python3 -B research/verify_trial214_counterexample.py
```

The reconstruction output directory must not already exist. Novelty needs
the pinned checkout; an optional `--cached-repo` may supply identical Git
blobs, never unmatched historical bytes. Both searches use standard Node.js
only. Exact upstream paths, Git blob IDs and file hashes for the fourteen
inherited table inputs are in `source_index.json`; inherited attribution
and licensing text is retained in `inherited_notices/`.

## Search toward 214: scope and limits

The search inputs are the exact primary K215, thirteen current alternatives
and FM215. It computes an inductive radius-three window invariant from
control 0 and arbitrary initial tapes. Each seven-bit window shifts under
the literal transition, with both possible fresh exterior bits admitted.
The least fixed point is an overapproximation of all concrete reachable
windows; an absent window is therefore unreachable. The abstraction loses
long-range tape correlations and is not complete.

The adjacent-marker search covers either current symbol and either original move
direction. It identifies 415 pairs of controls whose other rows agree and
whose differing rows are distinguished by opposite adjacent origin bits.
For every pair it tries both choices of retained control, both writes,
both directions, and all 214 surviving target controls: 710,480 proposed
replacement rows. Every incoming edge to the removed control is redirected.
Symbolic execution checks restoration of every inspected tape cell and the
exact mapped old endpoint. It branches on every unknown exterior cell;
limits are 32 transitions, eight inspected cells and 200 symbolic nodes.
No proposal passes both origin cases. A limit exit is unresolved, not a
counterexample or impossibility proof. The earlier 190,032 read-zero,
right-moving attempts are a subset and are not added to the final count.

A separate three-step helper resynthesis search tests 88,395 pair/helper
combinations. It allows both helper rows to change, requires the new
selector blocks to have the exact old effects, and preserves each old
helper use by a two-step equality for every symbol admitted by the window
invariant. It finds no candidate in this explicitly constrained family.

These searches do not range over changed source programs, global role
reallocations, richer tape invariants, arbitrary multi-row compiler
rewrites, or unrestricted longer simulation relations. They establish
neither a 215-state lower bound nor that no 214-state machine exists.

### Broader seven-bit-window search

`search_full_windows.mjs` drops the immediate origin-bit restriction and
uses every seven-bit window admitted by the radius-three invariant. It
considers pairs with one common row and disjoint nonempty sets of allowed
read-bit windows; the differing row can write either bit and move either
way. Across the same fifteen tables this identifies 1,029 pairs. Trying
both retained controls and every replacement row gives 1,761,648 attempts.
The required effect is still one exact old transition, with the entire
inspected tape restored to its correct endpoint value. Each symbolic
attempt has bounds of 32 transitions, thirteen total inspected cells and
200 nodes, starting with seven known cells. There are no accepted folds.
The complete Node.js rerun is recorded in `full_window_search_results.json`.

The 710,480 adjacent-marker attempts are an earlier, narrower family;
the two row-search totals must not be added. The 88,395 helper-resynthesis
tests are a separate explicitly constrained family. Neither search
exhausts all 214-state machines or all possible proof relations. The
reported exit categories (`cells`, `steps`, `halt`) indicate why this
specific local proof failed; bound exits do not establish semantic error.

### A concrete rejected 214-state fold

Four retained-control choices in the broader search survive the first two
representative windows but fail later required windows. One comes from
the commands120 alternative. Its old states 78 and 210 have the same
read-one row, `0 L 302`; their read-zero rows are `0 R 26` and `0 R 201`.
The tempting quotient deletes 210, redirects its incoming edges to 78,
and sets 78/0 to `0 R 201`. The resulting literal table has 214 working
controls and is retained only under `research/trial214.native.tm`.

`research/verify_trial214_counterexample.py` independently rejects its
uniform runtime contract on a concrete valid frame: source ordinal 25,
address `1101001000`, command CD3, all nine registers zero, one zero spare
and zero gap. The parent returns to native dispatcher 84 after 610 steps
with the required successor address `110100101`. The trial returns after
594 steps with a wrong address: the one at tape position 8 is missing and
an extra one appears at position 11. All other tape cells agree, and the
head is zero in both cases. The complete initial and final tapes and exact
table hashes are in `research/trial214_counterexample.json`.

This concrete example refutes this trial's claimed uniform primitive
simulation. It does not prove anything about whether the trial's blank
run is equivalent to Con(ZFC). The accepted contribution of this packet
remains FM215 and its all-tape delta theorem; no certified 214-state
candidate is supplied.
