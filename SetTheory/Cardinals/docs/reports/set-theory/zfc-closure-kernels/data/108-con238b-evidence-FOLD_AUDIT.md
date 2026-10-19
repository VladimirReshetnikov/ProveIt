# Independent fold audit: Boundary239 to Combined238

## Exact new input and result

The predecessor is the **Boundary239** table, with inherited labels, from
`ZFC_239_State_Construction_2026-10-19/zfc239-research-20261019`:

- table SHA-256: `d061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719`;
- changed source SHA-256: `7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6`.

The new `candidate238_old.tm` has 238 working states and 476 binary transition
rows. Its SHA-256 is
`069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c`.
This file explicitly declares `#! start 95`. The predecessor old-label file
has no header; its documented start state is explicitly supplied as 95 by
the verifier. The separate halt state is 254 and dispatcher is 96.

Delete state 169, redirect its only incoming transition `147/0` to 80, and
change the retained transitions as follows:

| Row | Boundary239 | Combined238 |
|---|---|---|
| 80 / 0 | 0 R 25 | 0 L 106 |
| 91 / 1 | 0 L 50 | 1 L 167 |
| 147 / 0 | 0 R 169 | 0 R 80 |

All other retained rows agree exactly. The map `phi(169)=80`, with every
other label fixed, relates old and new configurations without changing
their heads or tapes.

The coordinated239 and companion239 archives contain the same delayed-erasure
table, not two independent state savings. Their construction is reused here
on the independently changed Boundary239 predecessor. Thus the newly achieved
count is 238, and this report must not claim that both identical 239 tables
contribute separately.

## Why the two reductions compose

Disjoint edited rows alone do not prove that optimizations compose. Changed
control paths could supply a different tape context to a previously safe
helper. Accordingly, the local verifier reads the complete Boundary239
table and proves the exact local simulation against that table. The guard
verifier reads the changed Boundary239 source and proves the remaining tape
context premise throughout its own instruction-frame family.

Let `t[h+i]` be the bit at offset `i` from the old head. The following old
configuration predicate is initially true at state 95, on every tape:

| Old state | Required offsets |
|---|---|
| 67 | -1 = 0 |
| 80 | -2 = 0, -1 = 1 |
| 91 | -3 = 0, -2 = 1, -1 = 1 |
| 169 | -1 = 0 |

It is preserved by every predecessor transition. The proof is a direct
incoming-row calculation. State 67 has predecessors `52/0` and `124/0`,
both writing zero and moving right. State 80 has predecessor `67/1`, writing
one and moving right. State 91 has predecessor `80/1`, writing one and moving
right. State 169 has predecessor `147/0`, writing zero and moving right.
The verifier checks this inventory indirectly and exhaustively by checking
every row whose target carries a predicate; it does not assume that the
Boundary239 selectors leave the predecessor structure intact.

The only extra condition is:

> Whenever Boundary239 reaches state 169 reading one, the cell immediately
> to the right is also one.

This statement is not inferred from finite profiling. It is established
on the exact finite blank initialization and every arbitrary-parameter
instruction frame by `verify_guard238.py`.

## Four symbolic local identities

The independent local checker assigns a distinct symbolic original bit to
every unspecified tape cell. Both runs access only the fixed cells listed
below; unknown exterior cells are never read. Their final finite write maps
are compared with identical symbolic defaults, establishing whole-tape
equality for all exterior tapes.

| Old row | Fixed tape bits | Positive new state path |
|---|---|---|
| 80/0 | -1=1, 0=0 | 80,106,92,107,125,25 |
| 169/0 | -1=0, 0=0 | 80,106,93,57 |
| 169/1 | -1=0, 0=1, 1=1 | 80,91,167,151,173,56 |
| 91/1 | -3=0, -2=1, -1=1, 0=1 | 91,167,151,24,36,54,71,82,94,50 |

Each row of this table represents **one** old step. The corresponding new
durations are 5, 3, 5, and 9. In each case the endpoint has the mapped old
state, exactly the old head location, and exactly the old tape. None of
the intermediate states is a halt. The remaining 474 old transition rows
commute under the state map in one step, including the transition into the
halt state. Thus every old step has a positive new realization of length
between 1 and 9.

The mechanism is delayed erasure. The new `91/1` retains a one temporarily
while moving into existing states 167 and 151. These states distinguish
the old 91 caller, which has two ones to its left, from the mapped 169 caller,
which has a zero to its left. Both branches erase the intended original
one before synchronizing. No new state or tape symbol is introduced.

## Halting equivalence from local simulation

Suppose `C_0,C_1,...` is the predecessor execution. Let `k_i` be the certified
new block length for the old step from `C_i`; it lies in `{1,3,5,9}`. By
induction, the new execution at time `k_0+...+k_(n-1)` is `phi(C_n)` with the
entire old tape and head preserved. If the predecessor halts, the new run
halts at the corresponding cumulative time. If the predecessor runs
forever, the positive lengths make the cumulative times unbounded, and the
new run cannot halt between mapped checkpoints because the local blocks
exclude an interior halt. Determinism identifies this constructed trajectory
with the unique actual new trajectory. Therefore the two blank runs have
equivalent halting behavior.

The structural predicate is required at **old configurations** only. It need
not hold at new intermediate helper configurations, where the new branch
purposefully uses existing states in a second context.

## Complete blank initialization

The independent sparse verifier compares the two full tape supports before
and after every one of the 409,691 predecessor steps. It checks 409,692 mapped
checkpoints. The four exceptional visit counts, in the order 80/0,169/0,
169/1,91/1, are 18,12,6,3. Consequently the new initialization takes

`409691 + 4*18 + 2*12 + 4*6 + 8*3 = 409835`

steps. Both machines then reach inherited state 96, head -5, with the same
351 one-cells and all other cells zero. The complete support is retained in
`local238_receipt.json`.

## Quantified guard check

`verify_guard238.py` imports the unchanged affine/list engine with SHA-256
`c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145`
and its unchanged helper with SHA-256
`0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346`.
It performs independent finite structural validation and pins the exact
Boundary239 source, since the engine's historical validator pins the different
Rotation240 source. The instruction execution rules and expected endpoints
are unmodified.

The wrapper checks each state-169 entry before the original step function.
Its scan orientation must be rightward. When the read symbol is one, the
symbolic run beginning at the head must have an affine length whose constant
coefficient is at least two and whose other coefficients are all nonnegative.
This implies the right-neighbor-one condition for every natural assignment.

The wrapper also excludes hidden visits. Every checked one-block list
schema has no state-169 source or target in its explicit literal/unary trace;
no list lemma has entry state 169; and neither transition from state 169 is
a self-loop. Therefore an accelerated unary or list step cannot conceal a
state-169 visit whose guard was not checked.

The proof ranges over all 8,386 original guarded cases, nine independent
natural primary register values, an arbitrary natural extra gap, an arbitrary
first spare value, and an arbitrary finite remaining spare list. Neither
the discovered finite profiles nor the interval-based case exclusions are
used. The 4,000 symbolic-rule cap bounds proof construction, not any natural
input parameter or the machine's literal running time.

Fresh results are written to `guard238/guard238_receipt.json`, with per-case
data and all guard visits in the adjacent JSON files. Completion status must
be `BOUNDARY239_UNBOUNDED_NEXT_ONE_GUARD_PASS`; a historical receipt is not
substituted for a fresh run.

## Scope and source dependencies

These checks give an ordinary mathematical proof of the exact binary
reduction, formalizable in elementary finite-string and natural-number
reasoning within ZFC. They are not a new compiled Lean/Rocq endpoint.

The whole consistency equivalence also needs the predecessor's source
semantics, the source-control-flow equivalence between Boundary239 and the
calibrated Rotation240 program, and the clean-pointer/zero-padding join
argument. Those source obligations are audited elsewhere in the report.
The new local and guard proof does not establish the source equivalence by
itself. Once those dependencies are supplied, it transfers the predecessor's
halting/refutation equivalence to the exact 238-state table.

## Portable reproduction

The two verifiers accept explicit input and output paths and use Python's
standard library. They preserve all input files and archived receipts:

```sh
python3 -B verify_fold238_local.py \
  --baseline /path/to/zfc_boundary239_old.tm \
  --candidate /path/to/candidate238_old.tm \
  --output /path/to/replay/local238_receipt.json

python3 -B verify_guard238.py \
  --table /path/to/zfc_boundary239_old.tm \
  --sites /path/to/boundary239/sites_logical.json \
  --engine /path/to/validation/symbolic_runtime.py \
  --output-dir /path/to/replay/guard238
```

Run with assertions enabled, without `-O` or `PYTHONOPTIMIZE`. The engine's
unchanged `independent_runtime.py` must sit beside the supplied engine file.
