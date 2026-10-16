# A smaller public-backend compilation of the unchanged ZFC254 register program

This experiment rebrackets the same axiom-emission instruction word. It compiles
to **269 working states**, compared with the pinned public Wade reconstruction's
281. It does **not** beat the 254-state benchmark. No new binary-TM-to-ZFC theorem
or Lean verification of this experiment is claimed.

## Exact result

The input is the 219-node `Dag254.v` numeric program published in Jeff's
verification of Mira-Cult's machine. The axiom-emission subgraph has 114 nodes.
Expanding that subgraph, while treating its other subroutines as atomic calls,
gives a word of 185 calls over 18 helpers. Every helper has zero statically
escaping break and continue levels. Weighted Re-Pair with seed 341 and exponent
4 makes 26 shared pair productions and a residual word of length 77. Binary
encoding of that residual word costs 76 nodes, so the axiom subgraph costs
26 + 76 = **102 nodes**. The other 105 nodes stay in the program, for **207**
decision nodes. The unchanged public backend emits **62** framework states,
for **269** working states in total.

The independent checker verifies a complete finite bisimulation of exposed
register-operation sites. It has 4,533 pairs: 2,601 increment sites, 1,931
decrement sites, and one halt site. Both outcomes of every decrement are
checked. The two trees each unfold to 6,460 instruction sites. The maximum
number of contracted control-only steps is four on each side. Maximum decoder
path length changes from 96 to 97.

This certifies exact labelled control behavior at the **register-program**
level. Re-extracting all emitted decision edges also verifies that the compiler
consumed the intended new DAG. Neither check proves that the binary framework
simulates the register program on all unbounded tapes. That compiler proof
remains a distinct obligation.

## Portable reproduction

The only runtime requirement is Python 3.10 or later. No network access,
ProveIt checkout, Coq, Rocq, or Lean installation is needed. Run Python normally
(not with `-O`, which disables assertions in these audit scripts).

Arrange the supplied files as follows:

```text
rebracket_axioms.py
verify_rm_certificate.py
inputs/source_dag.json
inputs/backend/TMBuilder.py
inputs/backend/tm.py
inputs/backend/tmdb.py
inputs/backend/LICENSE.wade
```

Generate and verify:

```sh
python rebracket_axioms.py --inputs inputs --output results
python verify_rm_certificate.py \
  --source inputs/source_dag.json \
  --candidate results/rebracketed_dag.json \
  --certificate results/rm_bisimulation.json
```

The verifier independently implements path arithmetic using strings and
integers. It does not import or run the generator or backend. It checks the
source-data digest, every related instruction label, every successor pair,
the initial pair, and reachability of every certificate entry.

An optional `--repo /path/to/ProveIt` mode of the generator reads the original
pinned `Dag254.v` and the vendored backend instead of the portable inputs. The
verifier likewise accepts the pinned `Dag254.v` as `--source`.

## Output tables

`rebracketed_wade.tm` preserves Wade's named, partial-transition convention:
537 defined rows and a single missing row, `1.inc` reading `1`.

`rebracketed_wade_total.tm` numbers the working states 0 through 268 and the
terminal state 269, with 538 rows. Its start state is 0. The missing row is
filled by preserving the read symbol, moving right, and halting. This adds
no working state and preserves whether the computation halts; it adds one
final move when that formerly missing row is reached. `state_names.json`
records the exact renaming.

Key SHA-256 digests:

| Object | SHA-256 |
|---|---|
| Original `Dag254.v` | `538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3` |
| Portable extracted numeric data | `bb884eacd778c79f4cc672ea4136db91e7d4ad7eb70ead7cc2892aba56566db5` |
| 207-node candidate JSON | `55a7dcad13f4a226d079128afab68aa00cf2c047a196444c643d2b42859a37f2` |
| Register-machine certificate | `920df8e044536e0bfdc57fc592e6374cc82943a8599aef615df42ca802984003` |
| Named 269-state table | `6fbf3d909920c261ab789e430b6febc4c38099fd26250c1bd1f2e2cc92260560` |
| Total numeric 269-state table | `b40b90fdcf3a09475d3a2314dc3707bcf51a6302a3fdbba3c6afcde6ed1109de` |

## Provenance and license boundary

The ProveIt source pin is
`6594795e9db81637c30959e42b3bcfc9eb77722f`; the upstream busy-beaver pin is
`297ab8df7e5de329605c3875b4934643b371a5e3`.

Mira-Cult designed the 254-state machine and its searched theory. Jeff
(`jeff87654`) published the verification and the numeric 219-node register
program used here. The portable `source_dag.json` extracts only that finite
program's numeric edges and their identifying names; it does not redistribute
Jeff's Coq proof sources or relicense them.

Andrew James Wade's `TMBuilder.py`, `tm.py`, and `tmdb.py` are copied without
modification from the pinned imported generator and retain `LICENSE.wade`
(MIT No Attribution). The small compile/re-extraction interface in
`rebracket_axioms.py` is adapted from ProveIt's MIT-0 `recover_wade_dag.py`.
Backend SHA-256 pins appear in the script and generated evidence.

## Interpretation for a sub-254 search

If the framework remains at 62 states, a record improvement needs at most
191 decision states. This experiment reaches 207, so it needs **16 further
state savings** to reach 253. Equivalently, with this DAG fixed, a framework
of at most 46 states would suffice. The 254-state table has contextual folds
between its decoder and engine, so subtracting this experiment's 12 saved
nodes from 254 is not a valid state-count calculation.
