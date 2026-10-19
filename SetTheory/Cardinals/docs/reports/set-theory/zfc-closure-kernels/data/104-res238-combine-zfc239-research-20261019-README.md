# A 239-state binary Turing machine for ZFC consistency

**Result:** the exact machine in `candidate239/zfc_boundary239.tm` has
239 working states, including blank-tape initialization, and an ordinary
mathematical proof of

\[
\mathrm{ZFC}\vdash
\bigl(\neg\operatorname{Halt}(M_{239})\leftrightarrow
\operatorname{Con}(\mathrm{ZFC})\bigr).
\]

The proof composes the pinned ProveIt source/calculus/theory calibration with
a complete source control-flow certificate, an unbounded whole-tape runtime
proof, an exact blank prefix, and a six-case state-fold proof. This archive
does **not** supply a new Lean/Rocq kernel theorem or a serialized PA derivation
for the 239-state table. Its mathematical proof and executable certificates
are meant for review and incorporation into the ProveIt research tree.
No assumption that ZFC is consistent is needed to state or prove the
biconditional. Actual nonhalting follows if ZFC is consistent.

## Start here

- `report.pdf`: the main mathematical report.
- `report.tex` and the root `.tex` fragments: its complete editable source.
- `candidate239/zfc_boundary239.tm`: the accepted, canonical machine.
- `state_folds/fold239.tex`: the direct six-block reduction proof.
- `formalism/extra/check_rotation_certificate.py`: the complete source checker.
- `source_interface/check_source_interface.py`: exact identification with the pinned calibrated Lean source and logical seed.
- `candidate239/universal_runtime.json`: the final unbounded runtime result.
- `research_status.json`: accepted and rejected artifacts, counts, and limits.
- `reproduce.py`: portable quick/full replay, using a temporary copy.

### Exact machine convention and identity

| Field | Value |
| --- | --- |
| Working states | 239, labeled 0 through 238 |
| Transition rows | 478, exactly two per working state |
| Tape | One tape indexed by the integers |
| Symbols / blank | 0 and 1 / 0 |
| Initial tape / head | All zero / position 0 |
| Start / dispatch | 0 / 84 |
| Separate halt outcome | 239; not counted as a working state |
| Moves | One cell left or right; no stationary moves |
| Free input or initialization | None |

The canonical file begins with `#! start 0`. Every remaining row has five
fields: current state, read bit, written bit, direction (`L` or `R`), next
state. The halt outcome has no outgoing rows. Its SHA-256 is:

```text
666f5bf1370b6b44ff4e614e4b194bc5be6b4c621914842ad7e344d6570a544e
```

The inherited-label table `candidate239/zfc_boundary239_old.tm` uses start
95, dispatch 96, and halt 254. It deliberately preserves the discovery file's
exact bytes and has **no start directive**; use the preceding convention.
Its SHA-256 is:

```text
d061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719
```

`candidate239/renumbering.json` gives the complete action-preserving bijection.
All working states are reachable in the directed transition graph. This
does not assert that all are visited by the actual blank-tape execution.

## What changes

The source is reparenthesized without changing any of its 6,455 instruction
occurrences, register operands, or control-flow successors. Thirteen stages
containing 25 rotations reduce the source DAG from 225 to 224 nodes. Maximum
path length falls from 51 to 48; maximum zero run remains six. The two final
rotations cross a trailing explicit break, a case excluded by a conservative
rule requiring all three rotated chunks to be closed.

That source saving initially disrupts a decoder context. A charged repair
produces the complete intermediate `boundary240/boundary240_old.tm`. The final
reduction splits old state 218 according to the bit immediately behind the
head, reuses its former helper 223 for one role, and merges its other role
with state 179. Three old control roles occupy two new states. Six exact
two-cell block identities prove halting equivalence for every binary initial
tape at the common start state. This changes the choice of shared decoder
programs rather than merely identifying two existing transition rows.

The final literal runtime check also independently passes all 8,386 guarded
instruction cases, using 2,247,513 symbolic rules. Registers and padding are
unbounded; the spare list is any nonempty finite list. Existing spare values
are retained, and increment appends a value-1 spare. Exact affine durations
have positive constant terms, with minimum 13. These are proof-construction
counts, not the running time of the machine's entire proof search.

Sparse and dense execution, including a separately relabeled run, agree on
the complete configuration after 409,691 blank-input transitions: canonical
dispatch 84, head -5, 351 one cells, logical registers
`(3,0,0,0,3,0,0,0,0)`, 167 spare values all equal to one, and an additional
gap of 117. `candidate239/blank_prefix.json` records every one-cell position.

## Reproduce the accepted result

Use Python **3.10 or later**, with assertions enabled. No Python packages are
required. Do not use `-O` or `-OO`.

From the extracted archive root:

```sh
python3 -B reproduce.py
```

This checks the manifest, then replays the source certificate, baseline
initialization, independent final construction and renumbering, exact Lean
source-data and seed identification, the six-block
fold, all 8,386 minimum-register fixtures, the baseline abstract source
invariant, and the finite container diagnostic. All mutations happen in a
temporary copy. A fixture pass is supplementary regression evidence; it
does not replace the unbounded proof.

For the full replay, including the three complete universal runtime checks:

```sh
python3 -B reproduce.py --full
```

The runtime checks took about three minutes each in the preparation
environment. The expected rule counts are 2,322,575 for the original 240-state
baseline, 2,252,241 for the repaired 240-state reference, and 2,247,513 for the
final 239-state machine. Every run covers all 8,386 guards and has minimum
constant duration 13. Timings and absolute paths in fresh records may differ.

Optional arguments retain the copied files/logs and write a compact record:

```sh
python3 -B reproduce.py --keep-work /tmp/zfc239-replay-new --record /tmp/zfc239-replay.json
```

`--keep-work` must name a directory that does not already exist. The manifest
checks included bytes; it is not a digital signature. The recorded quick
replay under `reproduction/` documents an actual run on the assembled bundle.

The essential standalone checks can also be invoked directly:

```sh
python3 -B formalism/extra/check_rotation_certificate.py
python3 -B candidate239/build_candidate239.py
python3 -B state_folds/certify_239_fold.py boundary240/boundary240_old.tm candidate239/zfc_boundary239_old.tm --output /tmp/zfc239-fold.json
python3 -B validation/check_literal_runtime.py --table candidate239/zfc_boundary239_old.tm --sites candidate239/sites_logical.json --states 239 --output /tmp/zfc239-runtime.json
```

Direct constructor commands rewrite their generated artifacts in place. Use
the replay driver to preserve the supplied records. The original
`validation/independent_runtime.py` is retained byte-for-byte for attribution
and imported as a library; its historical standalone CLI is not part of the
reproduction interface.

## Research and rejected candidates

| Directory | Contents and status |
| --- | --- |
| `candidate239/` | **Accepted final construction**, exact tables, startup, relabeling, runtime and fold records |
| `boundary240/` | Accepted repaired 240-state reference for the direct reduction |
| `baseline/rotation240/` | Exact pinned ProveIt 240-state inputs and original attribution/licenses |
| `baseline/dependencies/`, `baseline/source/` | Selected prior calibration, source and bootstrap references; not a rebuilt Lean dependency tree |
| `formalism/` | Source equivalence certificate, consistency proof, alternative-theory analysis and model filters |
| `source_interface/` | Independent extraction of all 6,455 source triples and the seed from pinned Lean definitions |
| `semantic_interface/` | Pinned register-path semantics and the audited correspondence for every source instruction |
| `validation/` | Unbounded affine/list runtime engine, full baseline run, restricted invariant run and literal checkers |
| `source_encoding/` | Reproducible source/compiler construction and explicitly rejected intermediate tables |
| `state_folds/` | The successful direct fold proof; bounded search code and negative results with a positive control |
| `scanner/` | Rejected scanner shortening and 99 finite counterexamples |
| `semantic/` | Sound baseline zero/nonzero invariant and separate heuristic signatures |

Two different 240-state tables occur during independent reconstruction:

- `boundary240/boundary240_old.tm`, SHA-256 `19cd7f7863a681828fd026adbf8ce91c21e3ac7604439bc9d4603ba58661853e`, is the universally verified repaired reference used by the authoritative **six-case direct fold**.
- `candidate239/reference240_old.tm`, SHA-256 `fbe421d29a7104046a1ba62da0e5c7596e5969831e9e57503402a26d1f1825f4`, is a factoring of the decoder repair used by the independent **four-case merge** in the constructor.

Both constructions emit the identical final `d061770f...` inherited table.
The source-only DAG file retains some historical node IDs; its array length
is not the reachable 224-node DAG count or the 239-state machine count.

Files named `reassoc239_old.tm` and `boundary239_provisional2_old.tm` are
**rejected intermediate compilations**, with respectively 702 and 690 failed
minimum-register cases. They are retained because they expose why the final
source and decoder changes are both necessary. A counterexample to their
intended runtime contract need not be reachable from blank input; no stronger
impossibility statement about those unrelated literal tables is claimed.

The finite-window C++ searches require a C++17 compiler. Exact optional
commands and bounded parameters are in `state_folds/fold_search.tex` and
`source_encoding/README.md`. Their negative results establish no lower bound
on the state count. The successful context split is outside the simpler
pair/block/deletion classes tested by those searches.

## Build the documents

From the archive root, with a standard TeX Live installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

`source_encoding/source_search.tex` is an additional standalone source and
decoder note; compile it from its own directory. Other `.tex` files are
report fragments, not separate documents. The supplied PDFs were rendered
to page images and visually checked.

## Provenance and incorporation

The baseline is pinned to ProveIt commit
`13ec39ed43148b1807f51ed6e6528e1c84659562`:

- [candidate-rotation240](https://github.com/VladimirReshetnikov/ProveIt/tree/13ec39ed43148b1807f51ed6e6528e1c84659562/Computability/BusyBeaver/Research/ZFC/candidate-rotation240)
- [Source consistency calibration](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/Computability/BusyBeaver/Research/ZFC/calibrated_rotation240.md)
- [Original m254 verification](https://github.com/jeff87654/busy-beaver/tree/zf-254/ZF/m254)
- [Busy Beaver Challenge overview](https://wiki.bbchallenge.org/wiki/Logical_independence)

The intended incorporation is as a new research directory, preserving the
existing ProveIt evidence. `ATTRIBUTION.md` distinguishes inherited work from
this submission. Original notices are included under `baseline/rotation240/`.
No minimum-state claim or exhaustive historical novelty claim is made.
