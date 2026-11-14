# The 195-state reassociation certificate

The primary construction is **195S**, a 195-working-state, binary, single-tape
machine started in native state 74 on the all-zero tape. Native state 254 is
the halt control. The dense presentation starts in state 0 and halts in 195.
The halt control is excluded from the count of 195 working states.

The machine uses the supplied separate-Gamma calculus without changing its
190-token AX macro word, its 3,673 source operations, or its resolved source
instruction map. A new association of the AX tree reduces the number of
distinct reader nodes from 68 to 67 while retaining six valid simultaneous
contextual folds:

\[
134 + 68 - 6 = 196,\qquad 134 + 67 - 6 = 195.
\]

The 134-state fixed part is shared with the corresponding compilation of the
supplied separate-Gamma grammar. All 195 working controls are reachable in
the pointed transition graph. This graph reachability statement does not
assert that every control is reached on the blank run.

## Rebuild and verification

Python 3 with its standard library is sufficient. From this directory:

```sh
python3 build_check.py
python3 build_check.py --combined
python3 rotation_witness.py
```

The first command writes `rebuilt_195S/`; the second writes the supplemental
Combined196-controller variant to `rebuilt_195C/`. Each output directory
contains native and dense transition tables, the dense-to-native map, the
complete resolved source program, the source addresses, and an exact JSON
verification receipt. `--output DIRECTORY` selects another destination.
The commands run certificate checks and do not rerun a stochastic search.
Before checking either new table, the builder regenerates the literal
supplied 196-state parent from its own grammar and folds, checks its exact
dense conjugacy, its full source-site receipt, its free-algebra emitter,
its primitive macro bindings and exterior source control flow, its raw and
folded symbolic contracts, and its entire startup tape. Both new-variant
receipts embed this parent-reproduction receipt. Run without Python `-O`;
the scripts reject that flag because the assertions are required.

| Check | Primary 195S | Supplemental 195C |
|---|---:|---:|
| Working controls | 195 | 195 |
| Raw binary AX reader nodes | 67 | 67 |
| Simultaneous contextual folds | 6 | 6 |
| Source operations | 3,673 | 3,649 |
| Symbolic source-step contracts | 4,780 | 4,749 |
| Maximum symbolic steps per contract | 452 | 461 |
| Sum of symbolic steps over all contracts | 1,442,472 | 1,470,557 |
| Exact blank startup transitions | 58,154 | 57,922 |

For startup, the checker requires equality of the entire finite-support tape,
the head position, and the clean source-entry control. For each instruction,
the symbolic checker requires the prescribed destination source address and
the prescribed effect on the complete symbolic register file. Its register
oracle uses the unchanged arithmetic-box contracts; the builder explicitly
checks the physical rows for all oracle box states against the reference.

The six folds, in raw compiler coordinates, are
`2011→2015`, `2018→2051`, `2020→2061`, `2024→2033`, `2026→2048`, and
`2054→2055`. `folds.json` contains their full two-action definitions.
The local check executes all four context/read-bit cases for each pair in
the **final simultaneously folded table**. The full symbolic check then
checks every source contract against that same table.

`rotation_witness.py` produces and replays a 371-move occurrence-level
associativity certificate: 186 right rotations take the baseline tree to a
right comb and 185 inverse rotations take that comb to the new tree. This
is a constructive proof between the two endpoint macro trees. It is not the
stochastic search trajectory, and intermediate trees are not claimed to
satisfy runtime scanner constraints. The builder separately checks equality
of the endpoint macro words, opcode/argument sequences, and all resolved
jump instructions.

## Files and provenance

`grammar.json` is the frozen new grammar. `baseline.grammar.json` is the
supplied separate-Gamma grammar. `compiler.py`, `symbolic_runtime.py`,
`support.py`, `verify_emitter.py`, and `reference/` are copied from the
`axioms/` directory of the incoming archive
`pa_consistency_comparison_and_new196_2026-11-13.zip`, at ProveIt commit
`906367250a7f96c923147b10df392294bced7be5`.

`separate196/` contains all eight original parent files, byte for byte:
the native and dense tables, the grammar, the folds, the dense labels,
the complete source-site receipt, the original runtime receipt, and the
original startup receipt. Its `provenance.json` gives the exact ZIP member
paths, their SHA-256 hashes, and the enclosing archive hash. The copied
`supplied_verify.py` is the original verifier for those parent files.

The new `build_check.py` and `rotation_witness.py` make this construction
self-contained. `build_check.py --combined` additionally applies the six
explicit controller transitions and two source substitutions documented in
that script. The primary 195S construction does not require those extra
Combined196 changes.

`novelty.json` compares both new graphs with the exhaustive pinned-source
census. Both are absent from all 401 canonical source graph classes,
including all six supplied 195-state diagnostic graph classes. The remaining
source graph is a disconnected synthetic six-state control and is excluded
from the 401 by construction; its size precludes equality to either new
machine. The primary native table has SHA-256
`dcad583f1731bc41117be63bf8f4f7e69ab58409c18bcb56cf906337a996afae`.
The supplemental native table has SHA-256
`8f34d9e5cc2e64ecc49bbc8581dc29b2ac0a84ad9187c4dd8b7597588ef22ea3`.

Files prefixed `discovery.195C` record the first verified discovery before
the original-controller variant was checked. They are retained as provenance;
`rebuilt_195S/` is the primary delivery.

## Mathematical scope

The finite checks establish a fully specified table, unchanged source
program, simultaneous reader-fold certificates, symbolic instruction
simulation under the documented arithmetic-box contracts, and exact blank
initialization. They provide the machine-specific part of transferring the
separate-Gamma source program's consistency theorem to the new table.

The mathematical proof that the source program's nonhalting is equivalent
over PA to `Con(PA)` is supplied in the accompanying research report. The
Python receipts are executable certificates and are not a newly completed
Lean formalization of that theorem. The report distinguishes the imported
Lean result, ordinary mathematical arguments, and the executable checks.

The copied ProveIt and James Chang licenses are included. Attribution and the
pin apply to all imported reference material.

`search/` contains the optional standalone discovery code, its numeric input
shapes, the exact run log, and the compact 28-candidate verification summary.
Only the selected machine and its original-controller counterpart are
included as new transition tables. `manifest.json` records the SHA-256 and
size of every delivered file in this directory, excluding itself.
