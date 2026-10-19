# Source restructuring and decoder co-design

This directory records the source work behind the successful **239-state**
candidate in `../candidate239/`. The final machine is
`../candidate239/zfc_boundary239.tm`; its proof and runtime certificates are
outside this directory. Several smaller tables retained here are deliberately
rejected intermediate experiments. Their state counts do not certify them.

## The useful idea

The inherited 240-state source has 6,455 instruction leaves and 225 distinct
binary source subtrees. Reassociating the closed program

```
PUSH ; (copy D ; (PUSH ; copy H))
```

to

```
(PUSH ; copy D) ; (PUSH ; copy H)
```

reuses an existing subtree and removes one distinct source node. However,
this introduces a seventh consecutive zero in some instruction paths, and
it changes a subtree used by a backward decoder route. An apparent 239-state table
reduction therefore fails actual source-runtime tests.

The successful chain repairs both effects. First, closed reassociations reduce
the offending path set to one. Two right reassociations across the final AX
break then remove the last long zero run. The resulting source still has 6,455
leaves, now has 224 distinct subtrees, and has maximum zero run 6 and maximum
path length 48. All ordered instruction labels and both branches of every
conditional instruction remain exactly the same in the finite source
control-flow graph.

The two final rotations use a slightly broader lemma than closed-chunk
associativity. If `P` and `Q` are syntactically closed, then

```
((P ; Q) ; break k)  =  (P ; (Q ; break k)).
```

The break leaf's relative path changes from `1` to `11`, adding no zero.
Since break depth counts zero ancestors, the external break target is
unchanged. The original search rule required all three chunks to be closed
and therefore excluded this case. The exact control-flow checker confirms
the full source equality independently of this explanatory lemma.

The second repair changes **which source programs share a decoder state**.
Write `p = PUSH`, `f = fn45`, and `i = increment R1`. The inherited decoder
shared `(p,i)` and `(f,i)` at state 218, using the preceding tape bit as a
tag. State 179 separately implemented `(f,f)`. The successful machine puts
`(p,i)` in explicit state 223 and shares `(f,i)` with `(f,f)` instead. The
new pair has a common first child, while an existing backward route through
state 215 selects its second child using the tag. The complete proof and
literal paths are in `../state_folds/fold239.tex` and
`../candidate239/incoming_and_blocks.json`.

## Results and limits

| Experiment | Distinct source nodes | Literal working states | Outcome |
| --- | ---: | ---: | --- |
| Inherited source | 225 | 240 | Input baseline |
| Direct closed reassociation | 224 | 239 | Rejected: 702 of 8,386 finite guards fail |
| Boundary-aware source, provisional decoder | 224 | 239 | Rejected: 690 finite guards fail |
| Boundary source, explicit `(p,i)` decoder | 224 | 240 | Repaired reference for the final fold |
| Boundary source, new `(f,f)/(f,i)` sharing | 224 | **239** | Final candidate; see quantified runtime and block certificates |
| Projection-only alternate source | 224 | 240 | Rejected: it loses a different inherited decoder projection |

The initial direct reassociation is **not a new discovery**. An equivalent
`obvious244` experiment, including a concrete runtime counterexample, already
appears in the inherited companion's `runtime/independent_runtime.py`, shipped
here unchanged under `../validation/`. The new contribution in this work is
the complete combination of zero-run repair, reassociation across the escaping
break, and a different contextual decoder sharing that produces the actual
239-state machine. No claim of exhaustive literature priority is made.

A final additional search tried to manufacture a free backward-route helper
while preserving the inherited q243/q220 projection. The search retained at
most 240 candidates at each of 20 levels and examined 930,448 generated
alternatives. It found no lower-state result within those search settings.
This is a bounded heuristic search result, not a lower-bound theorem. It is
superseded for the present goal by the successful change in sharing at
179/218.

## Reproduction

Run commands from the package root with Python 3. Standard-library scripts
need no package installation. Paths are relative to this package layout.

```sh
python source_encoding/analyze.py
python source_encoding/reassociation.py
python source_encoding/build_reassoc239.py
python source_encoding/finite_screen.py
python source_encoding/compile_boundary.py
python source_encoding/finite_screen.py source_encoding/boundary239_provisional2_old.tm source_encoding/boundary239_sites.json
python candidate239/build_candidate239.py
```

The two finite screens are expected to report failures: they exercise the
rejected intermediate machines. The final reconstruction must report `PASS`.
It independently checks the exact table construction, incoming tags, four
whole-tape fold cases, canonical renumbering, and the complete blank prefix.
The quantified runtime checker is a separate obligation and must also pass.
Run the assertion-based checkers without Python `-O` or `-OO`.

Two 240-state references occur in the final certificates. The authoritative
repaired reference in `../boundary240/boundary240_old.tm` has SHA-256
`19cd7f7863a681828fd026adbf8ce91c21e3ac7604439bc9d4603ba58661853e`;
the fold note gives a six-case direct certificate from that table. The explicit
`(p,i)` fork in `../candidate239/reference240_old.tm` has SHA-256
`fbe421d29a7104046a1ba62da0e5c7596e5969831e9e57503402a26d1f1825f4`;
the independent reconstruction factors the argument through this fork and
checks the four remaining merge cases. Both constructions give the same
final inherited-label table, SHA-256
`d061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719`.

Optional source searches are:

```sh
python source_encoding/beam_checkpoint.py 200 10
python source_encoding/loop_scan.py
python source_encoding/loop_context_scan.py
python source_encoding/semantic_scan.py
python source_encoding/projection_guarded_beam.py 240 20 225
```

`semantic_scan.py` is a small finite semantic fingerprint search and is not
an equivalence prover. The loop scan implements a proved arithmetic identity,
but its cost estimates count source DAG nodes, not fully compiled states.
The projection search similarly uses a conservative cost estimate and does
not certify a resulting machine by itself.

## Important artifacts

- `mapping.json` and `analyze.py`: source DAG and inherited decoder map.
- `beam_checkpoint.json`: replayable closed-reassociation checkpoint with one
  remaining seven-zero path.
- `boundary_success.json`: compact, complete final source DAG, preserving the
  original 225 source IDs and the order of all surviving search IDs.
- `boundary_compile_map.json`, `compile_boundary.py`: deterministic literal
  construction of the provisional decoder.
- `boundary239_provisional2_old.tm`: rejected but important exact intermediate;
  SHA-256 `a810ad476842b2e5bd49bafa6c89dc999cbfd8df72c17bc0866339ba7e27ecf4`.
- `boundary239_sites.json`: intermediate JSON formatting of the final source.
  The final source certificate uses the equivalent canonical bytes in
  `../candidate239/sites_logical.json`, SHA-256
  `7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6`.
- `projection_success_compact.json`: a source-only alternate result. The word
  “success” refers to its source search objective; it is not a valid TM result.
- `projection_guarded_negative.json`: settings and layer-by-layer counts for
  the final unsuccessful projection search.
- `source_search.tex`: a standalone mathematical note about the source and
  encoding argument.

The final candidate's canonical transition-table SHA-256 is
`666f5bf1370b6b44ff4e614e4b194bc5be6b4c621914842ad7e344d6570a544e`.
