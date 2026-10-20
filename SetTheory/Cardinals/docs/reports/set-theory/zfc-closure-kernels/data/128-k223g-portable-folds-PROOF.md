# Three folds from 226 to 223 states

Let the initial machine be `parent226.k.tm`, the G-source table after the
closed right rotation that restores maximum zero run six. Let the final
machine be `candidate223.k.tm`. Both start in state 0; 254 is the distinct
halt label. These are historical labels: the final table has exactly 223
working states and 446 rows.

**The local theorem is stronger than blank-tape equivalence.** For every
initial binary tape on the integers and every initial head position, the two
machines started in state 0 halt together. This theorem makes no assumption
about the source program, register frame, consistency of ZFC, or blank tape.
The separate source/runtime proof identifies the parent with proof search.

## Simulation principle

For a fold deleting state `v` into retained state `u`, let φ(v) = u and fix
every other state. At a simulation boundary the old and new configurations
have exactly the same head position and entire tape, and old state q is
represented by new state φ(q).

Every ordinary old row is copied with its target renamed by φ. For each
possible old branch in states u and v, a nonempty finite new block reaches
exactly the renamed old one-step endpoint. No block has an interior halt.
An inductive invariant of the **old** machine may exclude old branches or
supply known neighboring bits. The invariant is empty in start state 0, so
it restricts no initial tape.

Every infinite old computation gives infinitely many positive-length new
blocks. Every finite old halt gives a finite new halt. Determinism therefore
gives halting equivalence. Composition gives the theorem for all three folds.

## 1. State 191 into 157: predecessor-bit routing (226 → 225)

All incoming rows of state 157 are the zero rows of states 192, 200, 209,
216, and 221; all write 0 and move right. The only incoming row of state 191
is `(300, 1) → (1, R, 191)`. Hence state 157 has 0 immediately to its left,
and state 191 has 1 immediately to its left. Neither is the initial state.
These two facts alone form an inductive invariant.

Redirect targets 191 to 157, delete 191, and set:

- `(157, 0) → (0, L, 67)`;
- `(157, 1) → (1, L, 187)`.

The four possible old branches have the following positive new blocks;
the sequences include both entry and endpoint states.

| Old state | Read bit | New state sequence | New steps |
|---|---:|---|---:|
| 157 | 0 | 157, 67, 151, 90 | 3 |
| 157 | 1 | 157, 187, 186, 86 | 3 |
| 191 | 0 | 157, 67, 152, 159, 118, 155 | 5 |
| 191 | 1 | 157, 187, 76, 148, 173, 182 | 5 |

Each block visits only the old scanned cell and its predecessor, preserves
both, and finishes one cell right of the old head. Its endpoint is exactly
the appropriate old one-step endpoint, with the state label renamed.

## 2. State 303 into 118: reclaim an impossible branch (225 → 224)

In the intermediate 225-state table, the only incoming row of state 159 is
`(152, 0) → (0, L, 159)`. Therefore state 159 always has 0 one cell to its
right. The only incoming row of state 118 is
`(159, 1) → (1, R, 118)`. Therefore state 118 always scans 0.
The pair of assertions is inductive:

- state 159 implies tape(head + 1) = 0;
- state 118 implies tape(head) = 0.

The old rows are:

| State | Read | Action |
|---|---:|---|
| 118 | 0 | (0, R, 155) |
| 118 | 1 | (1, R, 173), impossible under the old invariant |
| 303 | 0 | (0, R, 155) |
| 303 | 1 | (1, R, 153) |

Delete state 303 and redirect its incoming targets to state 118. Keep
state 118's zero row and change its one row to `(1, R, 153)`. The three
possible old branches now agree with their mapped old endpoints in one
new step.

**The state-118 invariant is an invariant of the machine before this fold.**
The new machine uses its one row for old-state-303 computations, so it is
neither necessary nor correct to claim that the branch remains unreachable
afterwards. The proof checks old reachable boundaries and composes the
simulations; it does not reuse an obsolete invariant on the final machine.

## 3. State 302 into 159: identical rows (224 → 223)

After the second fold, states 159 and 302 have identical rows:

- read 0: `(0, R, 166)`;
- read 1: `(1, R, 118)`.

Redirect targets 302 to 159 and delete 302. This ordinary quotient agrees
in one step on all four old branches, for every tape and head, without any
invariant. Every declared working state of the final machine is reachable
from start state 0 in the directed transition graph.

## Independent certificate

`check_folds.py` imports only the Python standard library. It reads the two
literal tables and `folds.json` as data, verifies pinned hashes, checks total
binary table format, validates every invariant implication against every
old literal row, checks all ordinary renamed rows, and executes all eleven
exceptional blocks on finite known tape patches. Any unknown read is
rejected, so the infinite exterior is arbitrary and untouched. Each accepted
block has positive length; the longest has five steps. The bound of sixteen
steps limits eligible certificates but never permits unfinished blocks.

The checker verifies that the complete transformation equals the delivered
223-state table. Its receipt is `fold_certificate.json`. Three negative
controls are rejected in `negative_controls.json`: a false predecessor-bit
assertion; omission of the supporting state-159 invariant; and a wrong
replacement for the reclaimed one row.

Run `python3 check_folds.py --output fold_certificate.json` from any directory.
The default input paths are resolved relative to the checker itself.
