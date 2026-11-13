SUBSTITUTION BY COMPOSITION IN iPRA
13 November 2026

STATUS

The requested construction below the full existing complexity frontier has
NOT been obtained. This package delivers two precisely limited results:

1. A program/environment presentation with no numerical variable binders in
   programs and root-only logical reindexing. All nine arithmetic schemas and
   ten remaining rule families are stated explicitly. A written comparison
   proof establishes its intended ordinary realization as bi-interpretable
   and equiconsistent with iPRA, using the pinned native-kernel bridge. This
   metatheory has not been newly formalized in Lean.

2. A separate same-contract reduction of an inherited compact checker from
   238 to 236 significant Python tokens. It does not delete a mathematical
   axiom or improve every complexity coordinate.

READ

  report.pdf / report.tex       Full mathematical report and editable source.
  code/pointfree_checker.py      Complete standalone reference proof checker.
  code/environment_programs.py   Semantic demonstrator, NOT a proof checker.
  compact_refinement/PROOF.txt   Universal equivalence proof for the small edit.
  evidence/                     Measurements, tests, and independent reviews.
  reference/                    Pinned baseline census and selected controls.

MEASUREMENTS

CPython 3.12.14, ast.unparse(whole_source)+LF, gzip level 9 with mtime=0.
                              tokens  AST   bytes  gzip9
Point-free reference checker     1687  2085   5184   1374
Main compact refinement           236   262    545    327
Set-image companion               236   261    545    330
Lambda-opener companion            236   270    516    320
Matched inherited control         238   262    545    326

The direct compact pooled envelope was 238/255/455; the token refinement
changes it to 236/255/455 when seeded-header protocols are admitted.
Different programs attain those coordinates. The new environment calculus
is not smaller than the compact baseline and is not presented as such.

RUN

  python3 reproduce.py
  python3 code/pointfree_checker.py < examples/all_rules.json
  python3 compact_refinement/code/checker_tokens236.py \
    < compact_refinement/examples/global_computation_zero.jsonl
  python3 build.py

The first three commands use only the Python standard library. The last
builds report.pdf with installed TeX and downloads nothing. It can create a
private format and font map if the local installation lacks generated caches.

INPUT CONTRACTS

The reference point-free checker validates its entire JSON proof DAG,
including program/formula sorts and strictly earlier premise references.
The final context must be empty; the reported theorem is the universal
closure in the ambient environment of the final formula's reading.

The compact checker uses its inherited promised integer/list and canonical
guarded public syntax. Its first line is [G,A], with G beginning with the
administrative entry 0. For a theorem, use G=[0]. Extra context formulas
are assumptions, not theorems. This checker is not an exact public-syntax
validator. The examples/ subdirectory already has the correct seeded header.
The fixtures/ subdirectory preserves the original theorem-format fixtures;
verify.py converts their first line before running the new programs.

EVIDENCE AND LIMITATIONS

The census measured 3,782 .py/.py.gz entries at pinned commit
e0d702b905c74b74a23d045f8289b151bb8ebcff, including all seven incoming ZIPs.
All 2,284 distinct filed Git blobs were hash-verified. The ledger is a source
measurement audit, not a correctness proof of every historical file.

Compact regression evidence: 35 cases, 280 normal/optimized isolated
executions, four pre-major freshness boundaries, zero disagreements.
Point-free kernel evidence: 34 positive proof nodes cover all 19 primitive
schemas; two positive and twelve rejection cases run in normal and optimized
Python (28 executions). Semantic demonstrations perform 3,377 finite checks.
These checks support the written proofs; they are not end-to-end formal
verification of the new metatheory.

All checker measurements include parsing, validation present in that checker,
schema recognition, and the acceptance marker. Generic Python/JSON runtime
cost is treated consistently with the pinned comparisons. No hidden normalizer
or arithmetic-specific imported library is used.

PROVENANCE

Baseline: VladimirReshetnikov/ProveIt, Logic/PrimitiveRecursiveArithmetic/
ConciseIPRA, at the commit above. Historical checker sources and fixtures
are attributed in the reference ledger and compact fixture provenance.
LICENSE-upstream.txt retains the repository's MIT-0 license. The compact
programs are explicit modifications of the inherited seeded control. The
point-free calculus, checker, and semantic demonstrations are the work
developed for this response; no global historical-priority claim is made.

Verify delivered file integrity with:
  sha256sum -c MANIFEST.sha256

Reproduction writes new receipts and regenerates examples. The PDF and the
LaTeX source contain the complete report; this README is a navigation guide.
