# Dedicated-helper layouts: new 208-state machines

These are new literal layouts, all with **208 nonhalting states**. They do not
satisfy the requested numerical target below 208. Their elementary simulation
proofs may be useful starting points for subsequent allocation searches.

All labels below refer to the History package's native class A/B tables, with
state 172 retained by the inherited 209→208 reduction. A fresh helper is named
500. In each construction, remove state `q`, redirect its incoming edges to
`r`, and replace `r/b` by `b L 500`. Add both rows of state 500. No other row
changes, except for the global target renaming `q→r`. Thus the count is
`208 − 1 + 1 = 208`.

| Removed q | Retained r | Changed bit b | Helper 500/0 | Helper 500/1 | Local block lengths at q/r on b |
|---:|---:|---:|---|---|---|
|127|124|0|`0 R 8`|`1 R 59`|3 / 3|
|190|160|1|`0 R 86`|`1 R 193`|3 / 3|
|178|168|0|`0 R 154`|`1 R 176`|3 / 3|
|301|88|0|`0 R 122`|`1 R 500`|5 / 3|

The first row also permits helper target 109 or 125 in place of 59. The third
row permits 159 in place of 154 and 225 in place of 176, independently. Therefore
there are nine donor choices per baseline class, eighteen literal tables in
all. Canonical rooted serialization confirms that all eighteen graphs are
pairwise non-isomorphic and distinct from both original baselines. Opposite
representative choices are only state renamings of these tables.

## Elementary invariant proof

The following is the complete incoming-edge census for the eight states, in
both baselines. Every incoming edge moves right and writes the indicated tag:

| State | All incoming source-state/read pairs | Written bit |
|---:|---|---:|
|127|110/0|0|
|124|104/1|1|
|160|139/0|0|
|190|165/1|1|
|168|176/0, 178/0, 225/0|0|
|178|158/1|1|
|301|87/0|0|
|88|77/1|1|

None is the initial state. Consequently, whenever the old machine enters one
of these states, its immediately preceding tape cell has the stated bit. This
holds on every initial tape and requires only one predecessor step. The proof
does **not** depend on the radius-7 exploratory context machinery.

For the first three layouts, the replacement moves left to read this tag,
moves right to the selected donor, and executes the donor's matching original
row. All writes preserve the read symbol, all three moves end one cell right
of the original head, and the final state is the old target under the quotient.
The donors have the required rows:

- `8/0 = 0 R 14`, matching `127/0`;
- `59/0 = 109/0 = 125/0 = 0 R 62`, matching `124/0`;
- `86/1 = 1 R 99`, matching `160/1`;
- `193/1 = 1 R 52`, matching `190/1`;
- `154/0 = 159/0 = 0 R 166`, matching `168/0`;
- `176/0 = 225/0 = 0 R 168`, matching `178/0`.

The last construction uses the helper's self-loop. Starting at the retained
state 88 and head coordinate 0, its two blocks on scanned zero are:

- Original 301, with preceding zero: `88 --0L→ 500 --0R→ 122 --0L→ 137 --0R→ 30 --0R→ 45`.
- Original 88, with preceding one: `88 --0L→ 500 --1R→ 500 --0R→ 122`.

Both blocks preserve the whole tape, touch only coordinates -1 and 0 before
their endpoint, and finish at head coordinate 1. Their endpoints are exactly
the original `301/0 = 0 R 45` and `88/0 = 0 R 122` transitions.

For every pair, the unchanged other-symbol rows agree, so those cases use one
step. Every other old row commutes with the quotient in one step. All blocks
have positive length and no internal halt. Induction on finite old runs proves
simulation. Conversely, if a new run first halts by time S while the old run
has S nonhalting steps, those S old steps generate a new nonhalting prefix of
length at least S, a contradiction. Thus each construction preserves halting
on every initial tape. The argument is a direct bounded computation proof and
can be formalized in PA; no PA proof-assistant export is supplied here.

For the three 3-step constructions, the exact clock is
`Tnew = Told + 2*N(q,b) + 2*N(r,b)`. For the last construction it is
`Tnew = Told + 4*N(301,0) + 2*N(88,0)`.

## Artifacts and checks

The deliverable's standard-library-only `code/verify_helper_machines.py` is the
preferred proof replay. It independently audits the complete incoming census,
all two-cell blocks, ordinary-row commutation, literal table construction, and
the eighteen graph classes. Its receipt is
`evidence/new_helpers_independent.json`. It requires neither NumPy nor any
finite-window binary. The scripts below preserve the exploratory workflow.

- `augmented_A_*` and `augmented_B_*` contain the eighteen machines,
  primitive-site TSVs, exact symbolic local certificates, finite-runtime
  receipts, and fresh-context fold-search results.
- `augmented_results_A.json` and `augmented_results_B.json` summarize them.
- `machine_hashes.json` binds native and canonical transition graphs.
- `verify_direct_helpers.py` independently checks the radius-7 raw invariant's
  initial inclusion and transition closure, projects all possible two-cell
  patterns, checks the complete local blocks, and replays 5,084 primitive cases
  for one donor choice of each of the four constructions in both classes.
- `augmented_search.py` checks all nine donor choices per class with exhaustive
  symbolic branching over complete context covers, runs the 5,084-case finite
  canonical-frame checker, constructs fresh radius-7 contexts, and screens all
  ordinary one-row contextual folds on the resulting machine.

The finite primitive test is regression evidence; the incoming-census and
positive-block argument above is the mathematical equivalence proof. The exact
symbolic checker is ordinary auditable software, not a proof-assistant kernel.
A full arbitrary-natural runtime replay can further validate the literal tables
but is not needed for the old-to-new local halting equivalence.

## Search scope and result

`search_helper.cpp` exhausts 280 oriented pairs whose exceptional old rows are
pure right-moving transitions and whose other rows agree under the quotient.
For each pair it synthesizes both helper writes and targets. Targets may be
any retained original state, initial state 0, or the helper itself. Both helper
rows move right. This gives 48,455,680 choices per class. The rejection screen
uses sixteen sampled radius-7 patterns per state/read and bounded 127-step
whole-tape simulation on a 128-bit local tape. Eighteen choices survive per
class, representing the nine tables above and both representative orientations.
Every survivor is subsequently checked exactly as described above.

`second_fold.cpp` tests each first-helper survivor against every disjoint
second pair satisfying the same pure-transition/other-row condition, including
other-row equalities created by the first quotient. It tests the combined
machine against the original four states' one-step actions, so routes through
the first fold are included. All 4,832 oriented combinations per class are
rejected. Separately, every one of the eighteen new layouts has a fresh
radius-7 fixed point and a complete ordinary one-row contextual-fold screen;
all eighteen searches have zero sampled survivors.

These are restricted negative search results, not a lower bound on the state
complexity. In particular they do not rule out different helper geometry,
more extensive source changes, a richer simulation relation, or a correction
that only preserves the canonical computation.

## Context label correction

The sibling search's class-B `window7b.bin` uses state 211, matching the Research
package's B table. History B instead retains 172. The tables are identical after
renaming 211→172. `window7b_history.bin` performs that row-block renaming in the
characteristic vector; its initial inclusion and closure were independently
checked against the actual History B literal table. Early B exploratory logs
without this correction should be ignored; the `helpers_extended_B`,
`second_extended_B`, `augmented_B_*`, and verified-helper receipts use the
corrected context. Class A required no relabeling.

An additional helper-direction extension was interrupted before completion.
Its partial files are not a completed search result and establish no negative
claim. No search remains running in this branch.
