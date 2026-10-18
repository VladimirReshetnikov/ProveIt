# Context-reduction investigation against the incoming 246-state table

## Outcome

This investigation has not produced a verified machine below 246 working
states. Its positive results are narrower: exact counterexamples to shortening
the zero-run return scanner, independently inferred universal marking exits for
several safe entry reroutes, and reproducible search programs with explicitly
bounded scopes. These results must not be described as a lower bound on state
complexity, nor as a refutation of every altered machine's eventual behavior.

The reference table is the original-label table inside
`docs/incoming/zfc-context246-20261018.zip` at ProveIt revision
`8cdc55ff9281b0aaba49bf74b0b225d57f12b893`. Its SHA-256 is
`303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.
The copied reference package is under `baseline/zfc-context246/`.

## A concrete obstacle: temporary PC words need the ninth zero

The source program's leaf paths have at most seven consecutive zero bits.
That fact does not justify shortening the left-return scanner: intermediate
control phases create longer runs. The following completely finite witness
uses source path `111010010010000000`, a zero decrement of logical register 1
(physical register 2), all nine primary registers zero, one spare register of
value zero, initial head 0 and header 40.

* Removing state 74 and changing `58/0` to `(0,L,84)` produces a false dispatch
  in state 96 at head 11 after 185 transitions. Coordinates 10 through 19 then
  contain `1 00000000 1`. The new scanner mistakes the internal PC one at 10
  for the left marker.
* Removing states 58 and 74 and changing `41/0` to `(0,L,84)` produces the same
  false marker at head 11 after 73 transitions, already on a seven-zero run.
* The unmodified 246-state table performs the specified zero-decrement
  instruction correctly in 386 transitions on this input.

`sentinel_counterexamples.py` reproduces the two complete finite false-marker
prefixes and writes `sentinel-counterexamples.json`, including every one-cell
at both the initial and final configurations. The inherited affine checker also
rejects the two proposals, and thresholds six through two fail as well.
The finite false marker defeats the proposed unchanged-frame simulation; it
does not prove that the altered blank-start machines halt or that no different
global interpretation could exist.

## State 2: a useful local fold that does not extend to a deletion

Replacing the target of `20/1` by state 4 preserves all nine marking operations.
The exact marking exit for physical register 0 becomes state 6; the other eight
marking exits already have that state. The local symbolic induction checker
derives these exits rather than assuming a state-number substitution.

However, state 2 has four external incoming rows. The full 8,391 guarded
instruction checks give these separately valid target sets among states
`4,6,9,13,19,29,41,58,74`:

| Incoming row | Individually accepted replacement targets |
| --- | --- |
| `20/0` | none |
| `20/1` | `4,6,9` |
| `42/1` | all nine listed states |
| `143/1` | `4,6,9,13,19,29,41,58` |

Thus simply merging state 2 into state 4 fails in the whole instruction
semantics despite its correct marking calculation. A further family removes
state 2, sends the latter three incoming rows to state 4, and tries every write
bit, movement direction, and remaining working-state target for `20/0`.
None of those 980 recipes is accepted by the affine checker.

## Completed search families

### Uniform folds with inferred macro exits

`fold_search.py` checks 671 uniform substitutions sharing at least one exact
read-branch action after target substitution. It protects deletion of the
fixed loop interfaces `48,63,73,83,95,109,112,131,96`. It proves the four block
identities, composes the three full register operations, derives all nine
marking exit states from the candidate's rows, and uses those actual exits in
the full 8,391 guarded affine instruction checks. No recipe passes. The record
is `fold-search-uniformNone.json`.

This is a bounded mathematical checker, not a proof-assistant kernel. An
unsupported symbolic rule or fuel exhaustion is a checker rejection, not a
proof of semantic inequivalence.

### All pairs, including mixed transition rows

`make_merge_cases.py` and `merge_search.cpp` test all
`4 * binomial(246,2) = 120,540` pair recipes. One state is retained, all targets
of the removed state are redirected to it, and each of its two read rows is
chosen independently from either original state. This includes both uniform
directions and both mixed-row possibilities. It does not exclude macro or
dispatcher states.

The finite test set has all 8,391 guarded program sites, primary values from
`(3*i+1) mod 5` with the selected decrement value changed to 0 or 2, and spare
values `[0,2]`. The baseline literally executes all cases, uses all 492
state/read pairs, and takes at most 558 transitions per case. Candidate tests
allow 20,000 transitions and head coordinates from -64 through 447. Sixty-three
recipes pass the short coverage probes; all fail a remaining finite case.
`merge-search-summary.json` records zero full survivors.

### Merges allowing a changed register assignment

`make_conjugacy_cases.py` and `conjugacy_search.cpp` investigate the same 120,540
pair recipes while permitting a different logical-to-physical register map.
For each logical register, a short increment site is run against all nine
possible physical increment effects. The nine inferred effects must form a
bijection. All 8,391 finite guarded instruction cases must then agree with that
same bijection, including decrement guards at the newly assigned locations.

There are 73,000 recipes for which all nine increment effects are inferred,
and 71,161 inferred bijections. None passes all finite guarded instruction
cases. This does not enumerate every possible compiler or all independently
retargeted permutations; it tests precisely the stated pair-merge family.
The record is `conjugacy-search-summary.json`.

### Two incoming actions, with exact lazy branching

`make_twoaction_states.py` uses exactly the 42 literal/unary-induction rows in
the inherited macro certificates. It protects every source and target of those
rows and the dispatcher/start interfaces. Forty-six remaining states have two
external incoming rows and are eligible for deletion.

`twoaction_search.cpp` gives each of the two incoming rows 984 choices: either
write symbol, either move direction, and any retained working state or the
halt label. Thus there are 968,256 complete action assignments per deleted
state, or 44,539,776 assignments over the 46-state family.

The executor stops before reading an unassigned row, branches over its possible
actions, and restarts the original fixture. A failed trace before a second
unassigned row rejects every completion of that partial assignment for this
finite screen. Each state checks the identity
`pruned assignments + survivors = 968256`. The affected-case gate allows 2,000
transitions; any survivor must pass all 8,391 literal fixtures with 20,000
transitions per case. Exact whole-configuration cycle detection uses direct tape
comparison, not hash equality. Bounds and assignment counts are in
`twoaction-search-summary.json`. The completed run partitions all 44,539,776
assignments and has zero finite survivors. It takes 124.884 seconds in the
recorded environment. The 2,000-step gate and finite register values are
material restrictions on the conclusion.

## Reproduce

Use Python 3 and a C++17 compiler. Assertions in the Python proof checkers must
remain enabled. Run from this directory with the reference package in place:

```sh
python3 -B sentinel_counterexamples.py
python3 -B fold_search.py
python3 -B edge_search.py 2
python3 -B repair_state2.py
python3 -B make_merge_cases.py
g++ -O3 -std=c++17 merge_search.cpp -o merge_search
./merge_search merge-cases.txt
python3 -B make_conjugacy_cases.py
g++ -O3 -std=c++17 conjugacy_search.cpp -o conjugacy_search
./conjugacy_search conjugacy-cases.txt
python3 -B make_twoaction_states.py
g++ -O3 -std=c++17 twoaction_search.cpp -o twoaction_search
./twoaction_search merge-cases.txt twoaction-states.txt
```

No search conclusion here infers nonhalting from a long finite execution.
No newly verified sub-246 table, blank initializer, ZFC equivalence theorem,
or proof-assistant endpoint is supplied by this investigation.
