# State reduction experiments with exact proof boundaries

**No verified 214-state consistency machine is delivered here.** The strongest
positive result is a quantified increment-only contract for a literal
214-state skeleton. A separately replayed zero-decrement counterexample
rejects that skeleton's proposed uniform first-clean-redispatch primitive
simulation. Nothing here
decides whether its blank run has a different consistency calibration.

## Fast verification

Run with Python 3, assertions enabled, from this directory:

```sh
python3 verify.py
```

The default checks the finite inductive invariant, independently replays all
59 primitive counterexamples and their parent controls, binds the exact
214-state skeleton to its source and saved 1,900-case result, and independently
replays its zero-decrement obstruction. It does not rerun the synthesis search.

To recheck all unbounded increment contracts as well (about 90 seconds in the
original execution environment):

```sh
python3 verify.py --universal
```

This optional check uses the supplied, inherited symbolic mathematical
interpreter. It is **not** a Lean or Rocq kernel proof. The arbitrary unary
length and spare-list cases are justified by the interpreter's scan and
finite-list induction rules, rather than by sampling large integers.

## 1. A precisely bound 214-state research skeleton

The ordinary K215 dense table has SHA-256
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
The unchanged source has SHA-256
`17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`.

The edited table is `rejected_noappend214.native.tm`, deliberately named to
prevent its being mistaken for an accepted consistency machine. It has
214 listed working states and 428 rows, with start 0 and separate halt 254;
its native working labels are not consecutive. Only 212 working states are
graph reachable from start 0: native labels 97 and 113 become graph
unreachable after the edit. The failed first-clean-redispatch contract below prevents
either count from establishing a smaller consistency machine. Its SHA-256 is
`6a932ada11c231372072aef98290850a574a184a74861763ed7ff9366b6511e1`.

| Item | Native presentation | Dense K215 presentation |
|---|---|---|
| Changed old row | `66 0 1 R 198` | `66 0 1 R 189` |
| Replacement | `66 0 0 L 54` | `66 0 0 L 54` |
| Deleted working state | 198 | 189 |
| Dispatcher | 84 | 83 |
| Halt | 254 | 215 |

The supplied canonicalization is checked as an exact state bijection by
`bind_noappend_result.py`, including every original transition, not merely
these listed labels. The literal edited table is reconstructed byte for byte.

### Quantified positive result

For every one of the **1,900 CI occurrences** among the source's 4,751 leaves,
the altered table has the following whole-tape contract:

- The nine logical register values are arbitrary natural numbers.
- The initial dispatcher/header gap is arbitrary and nonnegative.
- The spare suffix is any nonempty finite list of natural numbers.
- The exterior tape is entirely zero.
- Execution increments the specified logical register, preserves the other
  eight, and reaches the correct continuation with its ordinary head/gap
  adjustment.
- The **entire spare suffix is unchanged**. In particular, no appended unit
  spare is needed for the increment contract itself.
- The affine execution duration is positive for every valuation.

`symbolic_noappend_increment.py` builds the exact edited table before
checking it. Its result, `noappend_increment_universal.json`, contains every
source ordinal, affine duration and head displacement. All 1,900 cases passed,
using **672,539 symbolic proof rules**. The least constant term in a duration
is **546**. This is a lower bound on certified durations, not a measured
maximum runtime. The binding check verifies that the case list is exactly
the source's complete CI-occurrence list, in order, with no duplicate or
omitted occurrence.

The result removes one unnecessarily rigid increment postcondition: the
high-level register simulation can permit an existential spare suffix, and
even exact preservation of the old suffix is possible in this experiment.
It does not remove the other semantic responsibility of the deleted state.

### Exact obstruction

At zero-based source index 2 (the third leaf), take `0100 / CD0`, all nine registers zero, spare list
`[0]`, and gap zero. The parent reaches its first clean dispatcher frame in
640 steps. Its counter-one positions relative to the head are `[1,2]`, and
all registers remain zero.

The skeleton reaches its first clean dispatcher frame in **3,966 steps**
with counter-one positions `[1,3,4,5]`, registers
`[0,0,0,0,0,1,0,0,2]`, spare list `[1]` and gap 2. These are wrong logical
outputs at the first clean redispatch, even under the relaxed spare-suffix
contract. This does not exclude a different existential simulation that
waits through additional redispatches and source operations.

`check_noappend_obstruction.py` generates the witness with the search
simulator and then replays both machines using the independent byte-array
simulator. The decoder, source effect, parent control and first-frame time
are all recomputed. The result is `noappend_obstruction.json`.

The physical reason is visible in the original dense rows:

```text
66  0  1 R 189
189 0  1 L 40
189 1  1 L 111
```

State 189 serves both the append path and the zero-decrement restoration
path. Preserving all increment contracts does not justify discarding its
read-one responsibility. A next successful design must separate or share
that restoration behavior while also providing a calibrated blank startup.

## 2. A spare-aware deletion screen and 59 audited counterexamples

The first screen uses 23 shortest opcode/register classes and three
value/spare/gap choices per class, for 69 concrete tests. It considers the
29 covered working states at labels at most 112 having exactly one external
incoming row. For each removed state, every remaining target, write bit and
move direction is considered: **24,824 candidate row replacements**.

The postcondition is checked at the **first subsequent clean dispatcher
frame**. It intentionally allows any legal nonempty spare suffix and any
legal nonnegative gap, while preserving the decoded nine logical registers
and continuation. This is more permissive than exact physical spare
preservation, but it does not permit skipping a clean redispatch and waiting
for a later one. The first screen has a 5,000-transition cap; 59 candidates
pass it. Its receipt is `existential_spare_results.json`.

All 59 survivors then fail when the source occurrences are inspected. The
refinement initially produces 50 wrong decoded outputs and nine timeouts.
Those nine are subsequently resolved as **literal configuration cycles**:
all have zero head displacement, begin at step 129, and return to the exact
same control, head and entire finite-support tape by steps 585--609. Their
periods are 456, 472, 476 or 480 transitions. Determinism proves divergence on
those specific valid primitive inputs; this conclusion is not based on the
earlier time limit.

`audit_spare_counterexamples.py` independently verifies all 59, including
each parent input/output control. It imports no search or simulator module;
its byte-array tape implementation and source-effect calculation are
separate. The array bounds are checked, and every untouched cell belongs to
the infinite zero exterior. Its receipt is `independent_spare_audit.json`.

Thus the **59 survivors** are rigorously refuted for the stated first-clean-
redispatch primitive contract: 50 by a wrong output at that first return and
nine by an exact cycle containing no clean redispatch. The wrong-output
witnesses alone do not refute a different later-redispatch existential
contract. The earlier 24,765
screen failures have not all been resolved beyond their bounded tests. Do
not describe this packet as a theorem excluding all 24,824 tables, all
reachable-state calibrations, or all 214-state machines.

The append helper at dense label 189 was also screened separately, since it
lies outside the first label range: all 856 incoming-row replacements fail
the 20,000-step relaxed short screen (`existential_append189_results.json`).
A targeted provider experiment first checks 852 redirects of `66/0` against
42 non-increment samples. Only `0 L96` survives that filter. Trying all 856
replacements for provider row `96/0`, with the 27 increment samples included,
finds no surviving sampled contract (`append_provider_results.json`). These
are bounded search records, not universal negative theorems.

## 3. New configuration maps explored for local quotients

Ordinary exact-tape state identification was checked as a control experiment:
46,010 ordered state pairs, with a 64-step positive replacement cap, produced
no hit. Two more flexible maps were then explored. Suppose all retained
incoming moves to the removed state q have direction d, where d is +1 or -1.
Map a configuration at q and head x to a surviving p with:

1. head x+h, where h is 0 or -2d; and
2. optionally, the bit at x-d complemented.

All other configurations map identically. Every incoming row to q can then
be changed locally: redirect it to p, add h to its move, and complement its
write exactly when the map complements the predecessor bit. Thus no extra
state is needed to realize this configuration map on incoming edges.

For a sound quotient it suffices to exhibit positive old and new execution
blocks joining at this map for every reachable q-context. The finite checker
requires both blocks to have length at most its cap, to read only inside the
known window, and to agree on the complete tape at the join. An old endpoint
at q is compared after the same head/marker transformation. This stronger
map is distinct from a same-head, same-tape fold.

The saved radius-five invariant contains **87,475 abstract configurations**.
It starts from the all-zero window at control 0 and allows both possible
entering exterior bits after every move. The independent list-of-bits audit
checks **174,886 nonhalting successor obligations**, plus 32 abstract halting
configurations. It proves an overapproximation of blank-run local contexts;
it does not claim that all included contexts are reachable.

| Quotient family | Choices checked | Positive block cap | Hits |
|---|---:|---:|---:|
| Head offset, unchanged tape | 40,232 | 48 old and 48 new steps | 0 |
| Predecessor-bit toggle, with/without head offset | 80,464 | 64 old and 64 new steps | 0 |

The head-offset search evaluates 58,672 window obligations before rejection;
the toggle search evaluates 81,269. Their receipts preserve the best partial
matches. Failure can reflect the overapproximate invariant, the finite
window, the block cap, or the fixed configuration-map family. It is not an
optimality proof.

### Why a successful certificate would be sufficient

The window invariant is inductive, so every actual blank-run context is
covered. Since every local path reads and writes only inside its window,
literal equality of the finite windows at a join is equality of the whole
tapes for every exterior extension. Retained states simulate in one step;
the removed state simulates in a positive finite block. The old index and
new index therefore both increase strictly along the concatenated joins.
No block can pass through a halt and continue. A finite old halting run
transfers to a finite new halting run, while an infinite old run induces an
infinite new run. Determinism then gives halting equivalence. This explains
the proof obligation; no successful quotient certificate was found here.

## Optional research replay

The following commands reproduce the saved search families. They are not
part of the default verification gate.

```sh
python3 search_elimination.py k215.tm --steps 64
python3 search_offset_elimination.py k215.tm --steps 128
python3 search_offset_joins.py k215.tm k215_window5.json --steps 48
python3 search_marker_quotients.py k215.tm k215_window5.json --steps 64
python3 search_existential_spares.py k215.tm reference/k215/sites215.json --limit 5000
python3 refine_spare_survivors.py k215.tm reference/k215/sites215.json existential_spare_results.json
python3 resolve_spare_timeouts.py k215.tm existential_spare_refined.json
python3 search_existential_spares.py k215.tm reference/k215/sites215.json --limit 20000 --max-state 214 --only-states 189 --out existential_append189_results.json
python3 search_append_provider.py k215.tm reference/k215/sites215.json
```

## Provenance and attribution

All reference bytes come from the user-owned ProveIt repository. The local
retrieval checkout was commit
`53269bcab1efc0f82d3022645bd7cf0c22d84959`. This does not introduce an older
semantic baseline: **all 16 vendored reference files, including the dense
table and inherited notices/licenses, are byte-identical at the report's
current pin** `56e487ce8fa4cf63ad169ffe0cd2944e9fc62dd3`.
`current-bindings.json` records each exact original repository path, local
path, Git blob SHA-1, SHA-256, and matching current-tree blob. No reference
file differs or is missing. The comparison used the root report's pinned
`repo-tree.json`; its SHA-256 is recorded as well. The fast verification
recomputes all local blob and SHA-256 bindings before the four finite checks.

The upstream symbolic runtime, independent runtime helper, legacy mapping,
canonicalization, native table and source are preserved under
`reference/k215`, together with its upstream `NOTICE.md` and `licenses`.
Their original authorship and license terms remain unchanged. The dense
table `k215.tm` comes from the same upstream candidate directory and is
covered by those inherited notices.

The finite invariant was generated by the existing GC215 research file
`alternatives/gc215/research/physical-search/local_invariants.py`, provided
unchanged as `reference/window_generator.py`, and independently audited here.
Its contribution notice and MIT No Attribution license are retained in
`reference/window-generator-notices`; inherited Wade/ProveIt notices are
also available under `reference/k215/licenses`. The quotient maps,
relaxed-spare search, independent byte-array counterexample audit, exact
binding checks and increment-only experiment are this packet's additions,
provided for incorporation under the repository's MIT No Attribution terms.
Absolute input paths in original receipts record execution provenance;
reproduction uses the included relative paths.
