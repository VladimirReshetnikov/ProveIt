473-BYTE COMPOSITION FOR THE CURRENT COMPUTATION-LEAF PRESENTATION

checker473.py       Complete candidate module: 272 tokens, 308 AST, 473 bytes.
control474.py       Exact current computation-leaf control: 270, 308, 474.
PROOF.txt           Universal relative proof and precise input contract.
verify.py          Exact-source, metric and isolated-process verification.
metrics.json       Complete-module measurements, including the size tradeoff.
verification.json  Delivered test receipt.
SOURCE_AUDIT.json   Pinned snapshot, five incoming archive hashes and metrics.
fixtures/          Only the fixtures needed for verification.
reference/         Attributed inherited proof fragment and exact token/AST controls.
LICENSE.txt        Upstream MIT No Attribution license, also used here.

Run:
    python3 verify.py
    python3 checker473.py < fixtures/direct_zero_seed.json

The example prints ACCEPT. Ordinary and optimized Python are checked.
The measurement runtime is CPython 3.12.14; other ast.unparse versions may
change exact counts. Reproduction may update verification.json.

The byte saving is one. It composes two existing ideas and does not delete
an arithmetic/logical primitive or improve the 243-token/264-node records.
The envelope 243/264/473 is attained by different programs, not one module.
The complete iPRA interpretation is inherited, with all proof dependencies
stated explicitly. No claim of global minimality or a new mechanized proof
is made.

Source: VladimirReshetnikov/ProveIt,
commit 12197d86f63e9ec73b2d91399c4de2a8cb0077ee,
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/incoming/
ipra_computation_leaves_2026-11-12.zip, member
ipra_computation_leaves/code/checker_bytes.py.

The reference fragment is copied verbatim from lines 141-704 of that
archive's report.tex, with two provenance comments added. It is a fragment
for inspection, not a standalone LaTeX build target.
