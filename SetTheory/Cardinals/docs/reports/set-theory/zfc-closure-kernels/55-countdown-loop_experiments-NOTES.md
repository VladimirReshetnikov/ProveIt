# Exact source countdown summaries and the remaining binary representation gap

## Result and definitive artifacts

No smaller machine was certified. This experiment adds exact, variable-length
source blocks to the earlier fixed-prefix comparison. It recognizes **1,433
actual countdown loops**, composes their full affine register matrices, and
tries to recover additional endpoints representable by the existing binary
checker. Neither singleton entry constraints nor the independently checked
relational DBM equalities produce an additional constant-offset endpoint.

The definitive runs, both made with the final version of
`affine_reference_loops.py`, are:

| Directory | Source endpoint conversion | Completed fold recipes | Candidate case checks | Survivors |
|---|---|---:|---:|---:|
| `final/` | Singleton entry coordinates | 55,471 | 127,788 | 0 |
| `dbm_projection/` | Exact equalities in the guarded source DBM | 55,471 | 127,788 | 0 |

Each directory contains `source_frontiers.json`, `results.json`, and
`journal.jsonl`. Both runs preserve **every** endpoint from the earlier
fixed-prefix search, then take the union with all admissible loop endpoints.
Their final endpoint sets equal the earlier fixed-prefix sets exactly, as
checked by canonical frame equality for each source case. Both journals are
byte-identical to the earlier fixed-prefix journal, SHA-256
`1167e5fb920c362b0e7b230936c1e9c496573fa4de206f78fc718a030c1cf1bc`.

These are repeated checks of the **same 55,471 distinct recipes**, not
110,942 new mutations. The earlier development directory `results/` predates
the explicit union with all fixed-prefix targets and should be omitted from
the distribution. Only the two definitive directories above are needed.

`selected_matrix_frontiers.json` exposes full affine endpoints for eleven
selected source cases, including endpoints that the current binary ledger
cannot express. It is an input to further research, not a certificate for a
smaller machine. `affine_reference_loops.py` also provides the small
`raw_targets` API described below.

## Exact summary and its proof obligation

A recognized head is an actual source leaf `CD r`. Its positive branch
decrements register r and traverses a fixed finite body consisting solely of
`CI i`, `CB k`, and `CC k`, returning to that same head. The body never
increments r. There is no data-dependent branch or halt in the body. Let
L be one plus its number of instructions and let m_i count its increments
of register i. For arbitrary natural input n = R_r, the original source
program reaches the head's zero successor with

    R'_r = 0,
    R'_i = R_i + m_i*n  (i != r),
    successful source steps = L*n + 1.

For n = 0 this is one zero-branch step. For n = k + 1, one positive cycle
takes L steps, decrements the counter to k, and adds m_i to each other
register; induction on k gives the formula. This proof covers unbounded
natural counter values. It does not rely on sampled executions.

The compiler retains all nine physical registers as ten-coefficient rows:
the first nine coefficients multiply the initial primary registers and the
last is a constant. On a summary it adds multiples of the **old** counter
row to the other rows and then sets the counter row to zero. The source
clock is another affine row and increases by L times the old counter row
plus one. Literal source instructions are composed exactly between loops.
The first source instruction is always taken according to its original
guard; summaries are applied only at subsequent loop heads. This preserves
the original macro's guarded starting point.

Every positive cycle in the catalogue has zero physical PC-gap growth. The
zero exit has a fixed gap increment: zero in 1,432 loops and one in a single
loop. This follows by summing actual control-path overflow indicators; it
is not inferred from a bounded execution. A loop with nonzero positive-cycle
gap growth would be rejected by this implementation.

All live accepted targets have at least one successful source step. A
compositional binary simulation must separately supply a positive number of
literal binary transitions to the exact endpoint. A source induction does
not supply this binary simulation. The positive-block argument in
`proof_audit/compositional_box_simulation.md` allows the source block length
to depend on the current natural register values: the lengths are finite
and positive on every represented input, so cumulative source and binary
progress cannot skip a finite halting event indefinitely.

The successful source-step clock stops on reaching a `CH` leaf. Executing
`CH` adds no successful `RegisterPath.run` step. The existing binary frontier
adapter instead counts one final edge to a fresh terminal event; this
augmented halting clock has the same halting predicate. Raw matrix records
explicitly distinguish `successful_source_steps_before_CH` from
`augmented_terminal_edge_steps`.

## Concrete source sites and matrix obstruction

Indices below are zero-based DFS **source leaf indices**, not binary TM
states. Logical registers map to physical primary positions as

    logical:   0 1 2 3 4 5 6 7 8
    physical:  6 2 0 4 3 7 8 5 1.

| Head and zero exit | Actual positive body | Exact effect and successful clock |
|---|---|---|
| Site 2, `0100`, `CD 0`; exit `011`, decoding to site 6 | Sites 3 `CI 8`, 4 `CI 6`, 5 `CC 3` | Clear R0; add old R0 to R8 and R6; `4*old(R0)+1` steps |
| Site 6, `01100`, `CD 6`; exit `0111`, site 9 | Sites 7 `CI 0`, 8 `CC 2` | Clear R6; add old R6 to R0; `3*old(R6)+1` steps |
| Site 6431, `1111101100`, `CD 5`; exit `111110111`, site 6433 | Site 6432 `CC 1` | Clear R5, preserve every other register; `2*old(R5)+1` steps |
| Site 6457, `111111110`, `CD 6`; exit exact `00000000`, normalized empty PC, site 0 | `CI 4`, `CC 2` | Clear R6; add old R6 to R4; `3*old(R6)+1` steps; gap increases by one |

The first two loops followed by site 9's `CI 0` compose to

    R0' = old(R0) + old(R6) + 1,
    R6' = 0,
    R8' = old(R8) + old(R0),
    steps = 7*old(R0) + 3*old(R6) + 3.

The remaining registers are unchanged. With the source entry assumptions
R6 = R8 = 0, this prepares the next proof candidate while preserving the
incremented enumeration counter. Its R8 output still depends on an
unbounded *different* input coordinate. It therefore cannot be represented
as nine independent constant offsets. A generic clear at site 6431 has the
same issue: physical register 7 becomes zero, so its change is minus an
unknown initial value, not a constant.

These are precise construction targets for the next binary proof extension.
A binary run that clears or transfers an unknown primary counter needs an
inductive binary loop lemma with this matrix endpoint (or an equally strong
value relation), an exact dispatch PC and gap, a valid existential spare
suffix, and positive binary progress. The current box ledger only represents
`initial_register + constant`; it cannot gain this operation merely by
relaxing a comparison or assuming a reset. The raw matrix API preserves the
exact targets needed to attempt such a lemma at actual source sites.

## Full frontier statistics

The source has 6,460 instruction sites and 8,391 guarded cases. The original
checked phase invariant excludes six guards, leaving 8,385 cases. Each run
checks the unchanged 252-state table on all 8,385 feasible cases before
examining mutations.

The literal-prefix cap is 64 instructions, and the subsequent matrix
enumeration allows 64 literal-instruction or summarized-loop hops per case.
Neither cap is reached. All 1,433 recognized loops occur in the resulting
enumeration. Its statistics, identical with and without DBM projection, are:

| Quantity | Count |
|---|---:|
| Applied countdown summaries, counted across case frontiers | 25,952 |
| Such applications with an unbounded upper counter value | 25,589 |
| Intermediate matrices that cannot be converted to constant offsets | 44,706 |
| Cases ending at an unknown guard outside the recognized loop schema | 8,383 |
| Cases reaching a halt frontier, including the original CH case | 2 |
| Additional constant-offset target frames | 0 |
| Additional conversions from DBM equalities | 0 |

The final live target counts per feasible case are:

| Targets | Cases | Targets | Cases |
|---:|---:|---:|---:|
| 0 | 1 | 7 | 18 |
| 1 | 3,529 | 8 | 47 |
| 2 | 2,337 | 9 | 26 |
| 3 | 1,562 | 10 | 6 |
| 4 | 591 | 11 | 6 |
| 5 | 134 | 12 | 6 |
| 6 | 116 | 13 | 6 |

The zero-target case is the halt case. Multiple source histories can yield
the same canonical frame; the table counts distinct endpoint frames.

## Guarded DBM projection

`dbm_projection/` reads the independently checked threshold-2 certificate
`proof_audit/relational_dbm_threshold2.json`, SHA-256
`699948cea89404e797e0f18df0c185cf272ac2a4fee0e19f13a7de6d622c6f61`.
Its variables are constant zero followed by the nine **logical** source
registers. The converter maps each physical entry constraint to the proper
logical coordinate, intersects all original coarse bounds (including the
selected zero/positive CD guard), and closes the difference constraints with
Floyd-Warshall. A negative diagonal would exclude an empty product; none of
the previously feasible cases is newly excluded.

For finite entries with D[i,j] + D[j,i] = 0, the source invariant proves
`x_i - x_j = D[i,j]`. These equalities determine classes with integer
potentials, `x_i = z_class + p_i`, where the class containing constant zero
uses representative zero. For each endpoint row, substitute these equations
in the difference from its identity row. If every coefficient sum in a
nonzero representative class vanishes, the row difference is the exact
constant offset `b + sum(v_i*p_i)`. Otherwise the endpoint remains a matrix
and is not submitted to the binary checker.

This rule uses only equalities justified on the guarded source zone; it
does not assert that arbitrary binary inputs satisfy them. The binary trace
checker deliberately retains its original, coarser independent bounds. A
trace valid on that larger set is valid on the source zone, where the
projected target is exact. This division is sound and does not infer an
unknown binary guard from a desired source result. The DBM extension made
zero additional conversions in this run.

## Mutation family and rejection evidence

The family is exactly the protected uniform-fold family from
`compiler_experiments/reference_block_folds.py`: 221 eligible deleted states,
each redirected uniformly to one of the other 251 working states. It retains
state 96 as the dispatch anchor and fixes all 55 protected state/symbol
transitions of the proved unary box routines. It does not enumerate arbitrary
251-state tables. Each binary case has a 1,000 symbolic-rule fuel cap.
The entire family completed within the 600-second wall budget (31.37 seconds
without DBM, 32.57 seconds with DBM on the recorded environment).

Both runs have the same first-failure histogram:

| Rejection reported by the checker | Recipes |
|---|---:|
| Symbolic fuel exhausted | 33,289 |
| Undetermined sequential guard | 18,001 |
| Unknown right-run length | 2,877 |
| No justified box operation | 1,122 |
| Terminal lookup without a matching source halt frontier | 182 |

No tested mutation matched a longer source block on any case before its
first rejection. These results establish a limitation of this search and
its proof interface, not semantic invalidity of every rejected table or a
lower bound on the smallest possible machine.

## Independent audit

`proof_audit/countdown_loops.py` parses the literal pinned Coq source without
importing the frontier or mutation scripts. It checks exact retained-carry
source PCs against normalized physical PCs on all **8,390 nonhalting control
edges**. Its 1,433-entry catalogue was compared field by field against this
experiment's catalogue: head, counter, body sites, all increment counts,
positive-cycle length and gap, zero-exit site, normalized PC and gap agree.

Cycle lengths are 2 (6 loops), 3 (972), 4 (340), and 6 (115). Finite
regression controls from every loop with counter values 0, 1, 2, and 5 check
5,732 probes totaling 45,556 successful source steps. The unbounded
justification is the induction in `proof_audit/countdown_loops.md`, not these
controls. That note also proves the matrix update, gap accounting, singleton
conversion, and DBM equality conversion. None of these notes is a Lean
kernel proof or a certificate for a smaller binary machine.

## Reproduction and artifact API

Run from the package root with Python 3.12; no external Python package is
needed:

```sh
python proof_audit/countdown_loops.py
python loop_experiments/affine_reference_loops.py --output loop_experiments/reproduced --hop-limit 64 --fuel 1000 --seconds 600
python loop_experiments/affine_reference_loops.py --output loop_experiments/reproduced_dbm --hop-limit 64 --fuel 1000 --seconds 600 --dbm-projection
```

For a small selected-case query that performs no binary mutation search:

```python
from loop_experiments.affine_reference_loops import raw_targets

frontiers = raw_targets([4, 7, 9, 11, 23, 27, 31, 50, 8345, 8354, 8355])
```

Those eleven cases are the supplied snapshot's scope. Each target reports
the exact normalized PC and gap, nine ten-coefficient affine rows, an affine
source clock with a strictly positive lower bound, the next decoded source
leaf, and its source instruction/loop history. Coefficients are ordered by
**physical** primary register, followed by the constant. Entry bounds and
the logical-to-physical map are included. All prior literal-prefix targets
are retained as a separate origin alongside the summarized-loop records.
No random choices occur; no seed is required.

The script imports the included `compiler_experiments/reference_block_folds.py`,
`binary_experiments/common.py`, `binary_experiments/multieffect.py`,
`binary_experiments/strict_affine.py`, and the included upstream source,
table and phase-analysis snapshots described in `compiler_experiments/NOTES.md`.
The DBM option additionally requires the checked DBM JSON above. The pinned
source is
`upstream/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v`, SHA-256
`1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746`,
from ProveIt commit `43026ff42f0939f09b9e95495248cfadcad38e38`.

The source-loop driver used for both final runs has SHA-256
`6decc28f220024fa9fbeefd7ebd0a7ae053bc9a2944826a87e40a49a496fcec4`.
Runtime seconds can vary on reproduction; the deterministic journals and
source endpoint sets are the substantive comparison artifacts.
