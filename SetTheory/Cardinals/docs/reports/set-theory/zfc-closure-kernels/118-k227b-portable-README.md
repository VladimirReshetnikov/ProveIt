# K230 reductions: portable 227-state verification packet

## Results

The smallest completed machine in this packet has **227 working states**,
start 0, and separate halt 227. Its canonical transition file is
`source_fold227_zerofix/candidate.canonical.tm`, SHA-256:

`0264f969f006304840f46f85d5eacb54b70bf968669299ff73c3e0c5221fe09a`

The complete intermediate 228-state machine is
`loop_delayed228/candidate.canonical.tm`, SHA-256:

`06726bd731f3a42e3ccd1c4189d80af74ba2d486e333045097480fcaa3313001`

The intermediate 229 machine is `delayed_erasure229/candidate.canonical.tm`,
SHA-256:

`08dff69bd527a65967608fafc9d1205a667a6f6087289c4b55452faccb042273`

All three have binary tape alphabet {0,1}, blank 0, one two-way tape, and only L/R
moves. The initial head is 0 on the all-zero tape. Halt has no transition rows
and is excluded from the working-state count.

The 227 proof covers 6,656 guarded cases and 1,613,581 symbolic rules, covers all
454 literal rows, and has exact startup 409,835. The 229 proof covers 6,660 guarded source cases and 1,612,207 symbolic rules;
its exact startup has 408,563 transitions. The 228 proof covers 6,656 cases and
1,614,426 rules; its exact startup has 409,835 transitions. Every literal row
is covered, all primary register values and padding are unbounded, and the
spare list is an arbitrary nonempty finite list. These counts describe proof
construction, not the running time of the complete proof search.

The ordinary mathematical composition establishes blank halting iff ZFC
proves a contradiction, using the reviewed K230 source/theory theorem, exact
source binding, universal runtime proofs, and complete blank initialization.
Actual nonhalting remains conditional on consistency of ZFC. This packet
claims no new Rocq/Lean kernel endpoint or internal PA derivation.

## Replay

Python 3.10+ and its standard library suffice. No compiler, package install,
network access, upstream build script, or external workspace is needed.
From any directory, run:

```
python /path/to/packet/reproduce.py --full --output-dir /path/to/replay
```

This verifies the packet manifest; reconstructs all three literal tables and
state bijections; checks the complete source trees and collapsed control
flow; replays complete startup with sparse and dense tapes; and freshly
rederives all three universal runtimes. The fresh case and block records must
match the sealed evidence. Expect a few minutes. Success ends with
`FULL_PORTABLE_REPLAY_PASS` in `verification_result.json`.

Omitting `--full` checks construction/source/startup and sealed runtime input
pins, but does not freshly rederive the universal cases. It reports only
`QUICK_PORTABLE_BINDING_REPLAY_PASS`. Do not use Python -O for runtime replay:
its inherited engine deliberately rejects disabled assertions.

Fresh outputs go only to the selected output directory. The candidate
folders contain sealed inputs and receipts. The entry scripts contain no
imports of the original research workspace. `RUNTIME_DEPENDENCIES.json`
identifies the vendored proof engine and helper byte-for-byte.

## Source-aware construction

The 229 table retains the exact original K230 source list. It transfers the
historical delayed-erasure fold K140→71 with three retained-row edits. That
fold has a right-neighbor premise and is not claimed correct from every
arbitrary initial tape. The direct universal source-runtime proof and exact
startup discharge the needed blank/source-calibrated composition.

The 228 source makes four substitutions of the terminating transfer-plus-one
loop. Both old and new blocks map arbitrary natural registers (n,y) to
(0,n+y+1), leaving all other registers unchanged. Induction on n proves this
local identity. The literal source checker validates the exact local control
graphs, absence of external entry into block interiors, and identical 5,113-node
collapsed global control graphs. A context fold K79→63 then removes one state.
A separate all-tape positive-block proof applies to this last fold on the
rotated229 basis; it is not an all-tape claim about the source rotation.

`candidate.klabels.tm` preserves original K230 labels. `candidate.tm` uses a
collision-free proof-engine labeling. `candidate.canonical.tm` is contiguous.
`renumbering.json` gives the complete original-to-engine and original-to-
canonical bijections, so the canonical/proof relationship is checked literally.

## Additional source-aware 228 to 227 reduction

Four closed source reassociations preserve all 5,121 ordered primitive
occurrences and every one of the 6,655 literal control-flow edges. An
independent checker also compares the complete 3,590-node jump-resolved graph.
The constructor replays every rotation on the actual source-role allocation,
then reassigns one tagged role to K150 and folds K175 into K152. The literal
helper row K176/1 changes; its correctness is covered by the full final-table
universal runtime proof, not inferred merely from decoder-prefix checks.

The first three-rotation experiment introduced a seven-zero source path and
failed an actual valid instruction frame. It is not a verified machine in
this packet. The fourth rotation restores the six-zero bound without adding
a state. Only the repaired, fully proved table is included as a result.

The separate completed 228/229 packet remains unchanged. This extension adds
the 227 source-aware constructor, independent source-equivalence checker,
startup replay, and fully rederived universal certificate. To replay only
the 227 universal cases after a quick binding check, use:

```
python replay_runtime.py source_fold227_zerofix --output-dir /path/to/runtime227
```

## Upstream and scope

`upstream/K230` preserves the supplied repository sources at commit
`3142e4dd980f0be12f4abb636c4ae2528afc17eb`, including its notices and licenses.
The ordinary replay verifies its 103 manifest-pinned local input files and
its exact machine/source pins. The 115 external reference proof files are not
needed by this checker and are not rebuilt here; their prior intake hash
audit is retained separately. The repository's original formal endpoint and
build procedure remain upstream claims until independently kernel-rebuilt.
No upstream build or fetch script is invoked by this packet.

The JSON files under `independent_audits` record separately implemented input,
startup, local-fold, and old-runtime-guard checks. Their historical paths are
provenance labels, not replay dependencies. The portable replay's own fresh
receipts are authoritative for what it actually reran.

See `ATTRIBUTION.md`, the retained upstream notices, and `licenses/` for credit
and licensing. No publication or repository push was performed.
