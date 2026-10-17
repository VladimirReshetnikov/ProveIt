# Incoming-edge synthesis on the public 253-state machine

## Result

No 252-state blank-tape machine was obtained. A new bounded family, allowing
the incoming transitions of a deleted state to change their write symbols,
movement directions, and destinations independently, produced no complete
deletion certificate. The experiment did find 43 certified local transition
alternatives across 11 source rows. Combining these into 64 intermediate
253-state machines and recomputing abstract reachability did not produce a
complete deletion certificate either.

| Experiment | Abstract configurations | Nonstart deletion targets | Source rows tested | Transition alternatives checked | Complete deletion certificates |
|---|---:|---:|---:|---:|---:|
| Radius 6, 128 steps per side | 335,369 | 252 | 263 | 266,156 | 0 |
| Radius 7, 128 steps per side | 1,129,505 | 252 | 263 | 266,156 | 0 |
| 64 certified partial-rewrite variants, radius 6 | 335,305–336,777 per variant | Same deletion target as each variant | 64 | 64,768 | 0 |

The combined count is **597,080 transition-alternative checks**, not 597,080
distinct whole machines. The two radii examine the same replacement family
under different finite abstractions. The start-state deletion is excluded:
the initial state remains compact state 0 throughout this experiment.

The negative outcome is a failure to obtain a certificate in the stated
separable, bounded family. It does not imply semantic invalidity of every
rejected candidate, and it establishes no lower bound on arbitrary machines.

## Exact input and attribution

The input is the existing public 253-state machine attributed to mira-emmy,
derived from Mira-Cult's original machine, Jeff's verification, and Andrew
James Wade's framework. It is not a new machine produced by this experiment.

- Source commit: `0d544f2a2e3c18f12278441a74b7879f31cbe856`.
- Primary URL: <https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/machine/zfc_253.tm>.
- SHA-256: `84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`.
- Convention: 253 working states, 506 binary transition rows, blank symbol 0,
  start state 0, separate terminal 253, bi-infinite tape.
- Snapshot inspected: ProveIt commit `426592ce97e52d309bfb8f0132411556650b7ac1`.
- Snapshot input path: `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/04-machine-machines-zfc_253.tm`.

The reachable-window abstraction follows the definition already used in
ProveIt's `Computability/BusyBeaver/Research/ZFC/audit_tm.py`: after each move,
allow either value for the newly exposed cell. The implementation here is
standalone and imports no executable code from the source repository.

The new family differs from that repository's public253 radius-4/radius-5
uniform state folds and old107 incoming-target recipes. In particular,
replacement transitions may change direction and write symbol, and distinct
incoming rows can use distinct replacement states. It does not mutate the
logical axiom rows, change the register program, assume a prepared input, or
use a fixed finite run as an equivalence proof.

## Certificate argument

Let `p` be a nonstart state and `I` the set of incoming transition pairs
`(s,b)` whose old destination is `p`, excluding rows of `p` itself. For each
pair in `I`, choose a new `(write, move, destination)` triple whose destination
is not `p`. All other rows outside `p` stay fixed.

For each abstractly reachable window at each changed pair, the checker
requires a common configuration of the original and replacement block after
strictly positive numbers of steps on both sides, at most 128. The original
block uses the original table. The replacement block uses its new first row,
then unchanged old rows, and stops before entering `p`, executing another row
in `I`, or reading beyond the known window. It can match the configuration
just before another modified row would execute. All writes occur inside the
known window. Matching control, head, and every known tape cell therefore
means matching the whole tape, for every exterior tape. Two terminal outcomes
may match regardless of final head or tape because only halting is preserved.

The finite abstraction includes every actual original blank-run window, by
induction on concrete steps. Initially the machines are in the same blank
configuration. At an unchanged row they take the same single step. At a
changed row, its certificate advances each machine to the same configuration
after positive finite progress. Iterate at these common configurations.
Determinism and positive progress imply that either both runs halt or both
continue forever. The original run's reachability invariant remains valid at
every common endpoint. This is a mathematical correctness argument for the
criterion; neither this Python implementation nor this theorem is verified
in a proof assistant.

Because replacement blocks do not execute any other changed row, the
per-row synthesis choices are independent. A single incoming row with no
certified replacement obstructs deletion in this family. The search examines
all 1,012 triples for that row: 2 writes, 2 moves, and 253 remaining working or
terminal destinations. It stops examining a deletion when such a row is found.

For the staged experiment, partial rewrites are first independently replayed
against the original machine. Their certificates also avoid other modified
rows, so each chosen combination preserves blank halting. The second-stage
search recomputes the reachable windows of that intermediate machine and
tries to remove the same state through its remaining incoming rows.

## A compact certified 253-state variant

One positive local result is supplied as a literal portable machine,
`zfc_253_direction_rewrite.tm`. It changes exactly this row, in compact public
labels:

```text
old: 131 1 0 L 20
new: 131 1 0 R 22
```

The variant has 253 working states and SHA-256
`7c2f4cc99706e62330281385605b77001dd0c223bde399501179c055bee0e4f6`.
It is equivalent to the public machine for blank-tape halting. This is a
same-count rewrite, adding two steps whenever that row is simulated; it is
not a state-count or running-time improvement. It removes one incoming edge
to state 20, leaving that state and its other callers in place.

This witness needs only radius 2. The 3,530 abstract configurations prove
that whenever state 131 reads 1, at least one of the two cells immediately to
its left is 1. Of the 32 possible five-cell patterns, 12 meet this guard:

| Guard relative to the original head | Original steps | Variant steps | Common state and head |
|---|---:|---:|---|
| Cell -1 is 1 | 2 | 4 | State 22, head -2 |
| Cell -1 is 0 and cell -2 is 1 | 3 | 5 | State 22, head -3 |

The other cells are arbitrary. The two runs write the same original head cell
to 0 and preserve all other tape cells. They therefore have exactly the same
whole tape at the displayed common endpoint. In the second case, the final
head is one cell beyond the known window; neither run has read or written
that exterior cell. There is no appeal to a finite blank-tape simulation.

`direction_rewrite_certificate.json` is 1,306 bytes and contains the two
guarded block identities and the relevant hashes/census. The fully standalone
`verify_direction_variant.py` imports no code from either search. It parses
both tables, checks that their exact difference is the single advertised
row, recomputes the finite invariant, and replays the 12 local cases. Its
successful result is retained as `direction_rewrite_verified.json`.

```sh
python verify_direction_variant.py /path/to/zfc_253.tm zfc_253_direction_rewrite.tm direction_rewrite_certificate.json --output direction_rewrite_verified.json
```

The supplied mathematical block argument turns those finite checks into
blank-tape halting equivalence. The verifier is Python, not a proof-assistant
kernel; the variant's ZFC consistency calibration transfers through the
baseline's established calibration and this equivalence argument.

## Diagnostic outcome

| First stopping cause of rejected replacement block | Radius 6 | Radius 7 | Staged radius 6 |
|---|---:|---:|---:|
| Exits known window without matching | 253,793 | 252,046 | 58,208 |
| Reaches another changed row without matching | 10,843 | 12,590 | 6,224 |
| Unmatched terminal outcome | 1,477 | 1,477 | 336 |

There were no first rejections caused by exhausting the 128-step fuel. Thus
simply increasing that fuel cannot help at these recorded first-failure
windows. A wider window, a stronger invariant, or a method that solves
dependencies between modified rows can still help. A window exit is not a
counterexample to halting equivalence.

The partial rewrites affect compact deletion targets 16, 18, 20, 36, 59, and
60. The independent products have 1, 32, 14, 1, 15, and 1 variants respectively.
All retain 253 states. Full witness lists are kept in the compressed ledgers;
the short JSON files retain every target's first obstructing row and outcome
counts.

## Reproduction

Python 3.10 or newer; no external packages. From this directory, replace
`/path/to/zfc_253.tm` with the exact input table above:

```sh
python edge_replacement_search.py /path/to/zfc_253.tm --radius 6 --steps 128 --output incoming_synthesis_r6_s128.json
python edge_replacement_search.py /path/to/zfc_253.tm --radius 7 --steps 128 --output incoming_synthesis_r7_s128.json
python staged_replacement_search.py /path/to/zfc_253.tm incoming_synthesis_r6_s128.json --output staged_synthesis_r6_s128.json
python verify_edge_evidence.py /path/to/zfc_253.tm incoming_synthesis_r6_s128.json --output incoming_synthesis_r6_verified.json
python -m unittest test_edge_replacement.py -v
```

Do not use Python's `-O` option: assertions enforce checked contracts. The
result files contain hashes of the literal input, implementing scripts, and
decompressed ledgers. Wall times are informational and depend on the host.

The uncompressed ledger SHA-256 values are:

| Ledger | SHA-256 |
|---|---|
| Radius 6 | `e463bbcdf499eb2c812c421bb88581092439fe26ae4cf3080f490f247988ecf0` |
| Radius 7 | `a0839812685b690fc95d7ff17645925b5a7e23afe3d5c84e082dbe7da5b172f2` |
| Staged radius 6 | `45e2e98d41ffd0b5304d453ea2cb51021f0b4d11bd14fbbde36f5bdbaffc16fc` |

`verify_edge_evidence.py` uses an independent literal set-of-integers tape
interpreter; it does not call the search's local trace, row checker, or
certificate checker. It replays the positive and negative ledger witnesses
and checks that each tested row has the complete set of 1,012 alternatives.
It shares table parsing and the abstract reachability computation with the
search, so it is not a fully independent implementation of every component.
The retained radius-6 replay verified all 266,113 negative bounded witnesses,
all 43 positive transition alternatives comprising 9,984 local window
witnesses, and the completeness of all 263 tested alternative sets.

The nine tests exercise a known direction-changing deletion, rejection of
changed whole-tape contents, the barrier at other modified rows, exclusion
of the removed state, strict progress, missing window evidence, forged step
counts, inclusion of a concrete blank run in the abstraction, and rejection
of incomplete tables.

## Promising next work

The remaining bottleneck is chiefly spatial context and interaction between
modified rows. An appropriate next search would solve strongly connected
sets of edge replacements jointly, using finite block certificates with
positive progress. Another possibility is a regular-language invariant over
the whole PC/marker gap, supporting a literal rewrite of a scan routine. Each
approach needs an invariant soundness proof and a whole-tape simulation;
failing these bounded local certificates does not settle either approach.
