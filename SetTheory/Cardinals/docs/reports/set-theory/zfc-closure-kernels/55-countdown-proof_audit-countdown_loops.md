# Exact countdown summaries in the literal source program

Pinned ProveIt commit: `43026ff42f0939f09b9e95495248cfadcad38e38`.
Source: `upstream/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v`,
SHA-256 `1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746`.

## Unbounded theorem

Fix a decoded source leaf s containing `CD r`. Suppose its positive branch
follows a finite list B of instructions back to s, with these properties:

1. Every instruction in B is `CI i`, `CB k`, or `CC k`.
2. No increment in B selects r.
3. Following the actual path successor at every instruction reaches the
   next listed leaf; no other decrement or halt is encountered.

Let b be the length of B, L=b+1, and let c_i be the number of `CI i`
instructions in B, with c_r=0. Let n be the initial R_r. Then execution of
the original source program reaches the **zero successor of s** after
exactly `L*n+1` successful `RegisterPath.run` steps, with

`R'_r=0`, and `R'_i=R_i+c_i*n` for i different from r.

The source zero successor is computed from s's consumed leaf path. Its
exact PC does not depend on n or on the initial PC spelling, provided the
initial PC decodes to s. This last condition matters: the maintained source
consumes exactly the selected leaf depth, zero-padding or truncating the
incoming path before its arithmetic.

Proof: for n=0, the next instruction is the zero CD branch, which changes
no register and takes one successful step. For n=m+1, the positive CD first
decreases R_r to m. The body B has no data-dependent branch, never changes
R_r, adds c_i to every other R_i, and returns to the same head. These L
steps are nonhalting. Apply the induction hypothesis at m. The resulting
clock is `L + (L*m+1) = L*(m+1)+1`, and the register update is the asserted
sum. This is ordinary induction on an arbitrary natural n; no finite
register bound or execution fuel enters the theorem.

## Physical-PC and gap accounting

The binary frame normalizes trailing PC zeros into its affine gap. An
increment of an all-one consumed prefix (including the empty prefix)
normalizes to the empty PC and increases the gap parameter by one. This
physical overflow must be distinguished from exact `RegisterPath.incPath`,
which preserves all cleared carry-zero positions and does not have a gap
parameter.

Let gamma be the sum of physical overflow indicators around one positive
cycle and epsilon the indicator on the final zero branch. Under the
maintained frame arithmetic, the loop changes the gap parameter by
`gamma*n+epsilon`. All these indicators depend only on the fixed control
paths, so their sums follow from the same induction as the register effect.
The independent catalogue finds **gamma=0 for every one of the 1,433 loops**.
Consequently their gap update is constant and can be retained in a usual
affine-dispatch target. There is exactly one loop with epsilon=1; every
other zero exit has epsilon=0.

The exceptional loop is leaf 6457, path `111111110`, `CD 6`. Its positive
body is `CI 4`, then `CC 2`; its zero successor is the exact path
`00000000`, normalized to the empty PC, selecting leaf 0. It changes
`R4` to `R4+old(R6)`, clears `R6`, increases the physical gap parameter by
one, and takes `3*old(R6)+1` successful source steps.

## Affine-matrix use

Write the current symbolic register vector as `A*x+b`, where x is the
initial primary vector. Applying one summary replaces row r by zero and,
for each i different from r, replaces row i by

`A_i + c_i*A_r`, and `b_i + c_i*b_r`,

using the **old** row r and old b_r throughout. The zeroed row's constant
is also zero. All reachable values remain natural by the source theorem.
The source clock increases by `L*(A_r*x+b_r)+1`, which is positive for
every represented natural input. This is a variable-length source block,
even when its endpoint is described by a finite matrix certificate.

An existing binary checker whose ledger represents only `x+delta` must
not accept a generic matrix endpoint as if it were a constant offset.
A sound sufficient conversion is to substitute all initial coordinates
proved singleton by the entry invariant and require every coefficient of
every remaining non-singleton coordinate to equal the corresponding
identity-matrix coefficient. The residual constant is then delta. Mere
agreement on sampled inputs is insufficient. This sufficient conversion
may miss further reductions justified by relational input invariants.

There is a direct sufficient extension using the supplied closed DBM
certificate. If `D[i,j]+D[j,i]=0`, its two inequalities force
`x_i-x_j=D[i,j]`. Partition variables (including the constant zero variable)
by these equalities, choose a representative in each class (zero itself
for its class), and write
`x_i=z_class+p_i` with the certified integer potential p_i. For an output
row difference `v=(A-I)_row`, its variable part vanishes when the sum of
v_i over each class not containing zero is zero. Its remaining constant
offset is `b_row + sum_i(v_i*p_i)`, with the zero-containing class evaluated
at its fixed representative value zero. Substitution proves this rule; it
uses only exact equalities certified by the DBM. Merely bounded differences
do not permit this cancellation. Entry guard equalities may be incorporated
only after sound constraint intersection and closure.

Several summaries can be composed before this conversion. For example,
copy-and-restore fragments may first destroy the identity-matrix form and
later restore it while leaving only constant offsets under the entry
singleton constraints. This is the specific opportunity that bounded
source-prefix enumeration could not exploit at an unknown countdown guard.
Actual binary comparison and positive binary progress are still required;
source summaries alone certify no deleted machine state.

## Literal examples

The following leaf indices are zero-based DFS source-site indices, not
binary machine states.

| Head | Positive cycle | Exact summary | Successful source steps |
|---|---|---|---|
| 2, path `0100`, `CD 0` | `CD 0`; leaf 3 `CI 8`; leaf 4 `CI 6`; leaf 5 `CC 3` | clear R0; add old R0 to R8 and R6; zero exit PC `011` | `4*old(R0)+1` |
| 6, path `01100`, `CD 6` | `CD 6`; leaf 7 `CI 0`; leaf 8 `CC 2` | clear R6; add old R6 to R0; zero exit PC `0111` | `3*old(R6)+1` |
| 114, path `111010010010010110`, `CD 7` | `CD 7`; four `CI 1`; `CC 2` | clear R7; add four times old R7 to R1 | `6*old(R7)+1` |
| 6287, path `111010010010111111110001100`, `CD 5` | `CD 5`; leaf 6288 `CC 1` | clear R5; preserve all other values | `2*old(R5)+1` |

All four displayed positive cycles and zero exits have zero gap increment.

## Independent finite audit

Run `python proof_audit/countdown_loops.py` from the package root. The
script parses the pinned Coq source directly and imports no frontier or
mutation-search script. Its exact successor uses list-style carry; its
physical successor uses last-zero truncation plus an overflow bit. It checks
both normalized PC agreement and decoded-site agreement on all **8,390
nonhalting control edges**, including guards not feasible from blank. The
single CH case has no successful source edge.

It finds precisely **1,433** loops satisfying the stated syntactic schema.
Their positive-cycle lengths are 2 (6 loops), 3 (972 loops), 4 (340 loops),
and 6 (115 loops). A cycle increments any one register at most four times.
The catalogue is in `countdown_loop_catalogue.json`; every entry records
its body sites, increments, clocks, exact/normalized zero-exit PCs and gap
effects.

As regression controls, direct concrete source execution from every loop
head with counter values 0, 1, 2 and 5, and varied other registers, agrees
with the closed form in **5,732 probes totaling 45,556 successful source
steps**. These finite controls test the implementation; the induction proof
above is the justification for unbounded counters. This audit is not a Lean
formalization, a binary simulation certificate, or a claim of a smaller
Turing machine.

## Clock convention at halt

`RegisterPath.step` executes CI/CD/CB/CC as one source step, while decoder
traversal contributes none. It returns `none` on CH; `RegisterPath.Halts`
means some successful run has **already reached** a CH leaf. Thus CH itself
adds zero successful run steps. The countdown theorem above counts only
successful steps and remains exact even if its zero successor is a CH leaf.
For a uniform positive-block halting theorem one may adjoin a fresh terminal
state and a single transition from each CH configuration to it. This adds
one terminal event to a halting-prefix clock and leaves the halting predicate
unchanged. Reference-frontier fields that count CH as their final event use
this latter convention.

Primary source:
https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RegisterPath.lean
