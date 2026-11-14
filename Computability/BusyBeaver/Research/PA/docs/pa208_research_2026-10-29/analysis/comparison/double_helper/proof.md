# Exact equivalence proof for the new helper layouts

## Convention and statement

Let M be either 208-state History baseline, in its native labels. Its initial
state is 0, its halt state is 254, and 500 is absent. A table row `(q,b)=(w,d,z)`
means: at state q reading b, write w, move one cell in direction d, and enter z.
The halt state is excluded from the state count.

For each row of the following table, form N by deleting q, redirecting every
old target q to r, replacing r/b by `(b,L,500)`, and adjoining the indicated
helper rows. All other rows are the old rows under target renaming.

|q|r|b|500/0|500/1|
|---:|---:|---:|---|---|
|127|124|0|0 R 8|1 R x, where x is 59, 109, or 125|
|190|160|1|0 R 86|1 R 193|
|178|168|0|0 R x, where x is 154 or 159|1 R y, where y is 176 or 225|
|301|88|0|0 R 122|1 R 500|

**Theorem.** Each of these nine constructions on each of the two baselines
has exactly 208 nonhalting states and halts on exactly the same initial tapes
as its baseline. Both implications have direct finite proofs formalizable in
PA. Consequently any PA-provable consistency calibration of the baseline
transfers to the new table. The theorem supplies no new formal PA proof
object and makes no claim of fewer than 208 states.

## Complete incoming census

All incoming transitions of the eight affected old states are:

|Target|Source/read|Write and move|
|---:|---|---|
|127|110/0|0 R|
|124|104/1|1 R|
|160|139/0|0 R|
|190|165/1|1 R|
|168|176/0,178/0,225/0|0 R in each case|
|178|158/1|1 R|
|301|87/0|0 R|
|88|77/1|1 R|

None is the initial state. Therefore every old visit to 127, 160, 168, or 301 has
zero immediately left of the head; every visit to 124, 190, 178, or 88 has one
there. This statement holds on arbitrary initial tapes. It follows directly
from the last transition and has no reachability-sampling premise.

## Exact local blocks

Let π map q to r and fix every other old state, including halt. At an old
visit to either affected state, represent its configuration by the same
entire tape and head position, with control state π(s).

For the first three families, the changed row moves left to 500. The helper
reads the known predecessor tag and returns right to a donor. The donor then
executes the required old exceptional row. The matching donor rows are:

|Affected old row|Matching donor row|
|---|---|
|127/0 = 0 R 14|8/0 = 0 R 14|
|124/0 = 0 R 62|59/0 =109/0 =125/0 =0 R 62|
|160/1 = 1 R 99|86/1 =1 R 99|
|190/1 = 1 R 52|193/1 =1 R 52|
|168/0 = 0 R 166|154/0 =159/0 =0 R 166|
|178/0 = 0 R 168|176/0 =225/0 =0 R 168|

All three writes preserve the symbol read. The head positions are
`0,-1,0,1`, and the endpoint state is π of the old target. Only cells -1 and 0
are read or written, so this is equality of the whole tape, with arbitrary
unspecified exterior.

For the last family, starting in state 88 at coordinate 0 while reading 0,
the two predecessor tags select these blocks:

- Old 301, predecessor 0: `88 --0L→ 500 --0R→ 122 --0L→ 137 --0R→ 30 --0R→ 45`.
- Old 88, predecessor 1: `88 --0L→ 500 --1R→ 500 --0R→ 122`.

The old endpoints are respectively `301/0 =0 R 45` and `88/0 =0 R 122`.
The displayed five- and three-step blocks preserve every read symbol,
touch only the same two cells, and finish at coordinate 1 with the required
state. No interior state is halt.

In each pair the other-symbol rows agree exactly; thus that case is matched
in one step. At all other old states, the new transition is exactly the old
transition under π, so it also matches in one step.

## Finite simulation and reflection

Induct on the length n of an old trajectory. Starting in state 0, the new
trajectory consists of the positive blocks just proved, with equal entire
tapes and heads at every old-step boundary. If an old step first reaches
halt, its matching endpoint is new halt. This proves preservation.

For reflection, suppose the new machine first reaches halt at time S.
If the old machine has not halted in its first S transitions, the same
induction constructs a new nonhalting prefix of length at least S, because
every block has positive length and no internal halt. This contradicts its
first halt at S. The old machine therefore halts within S steps. This is a
finite argument, not an appeal to an actually infinite execution.

For the first three families the exact clock, whenever the old machine
halts, is `Tnew = Told +2N(q,b)+2N(r,b)`. For the last it is
`Tnew = Told +4N(301,0)+2N(88,0)`. Thus `Told ≤ Tnew ≤5Told` uniformly.
The tape configurations, finite blocks, counting functions and induction
can all be encoded arithmetically in PA.

The state census follows directly from deleting one old state and adjoining
one fresh state: `208−1+1=208`. The standard-library checker
`code/verify_helper_machines.py` in the deliverable independently checks every
incoming edge, every local trace, whole-tape equality, all ordinary-row
commutations and the literal table construction. It also establishes that
all 18 new rooted transition graphs are pairwise non-isomorphic and distinct
from the two baselines. No finite-window context file is needed for this proof.
