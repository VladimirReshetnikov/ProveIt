U211: a 211-state candidate for the consistency of Peano arithmetic
================================================================
Research prepared for Vladimir Reshetnikov, 28 October 2026.

RESULT
------
machine/u211.tm is a complete, deterministic, two-symbol, one-tape machine
with 211 working states numbered 0 through 210. Start in state 0, head 0,
on a two-way infinite all-zero tape. The separate halt label is 211.
All 422 transitions move L or R; the initializer is included in the count.

The mathematical proof composes the new literal/source simulation with the
retained U212 source/calculus and Theory U/PA calibration to obtain

  PA |- Nonhalt(U211, blank) <-> Con(U) <-> Con(PA).

This release supplies a mathematical argument and freshly executed universal
symbolic verification. It is not a newly compiled Lean, Rocq, MM0, or exported
PA endpoint certificate. The inherited arithmetic interpretation arguments
remain explicit dependencies. No unconditional consistency, nonhalting,
discovery priority, or global state minimality is asserted.

COMPARISON AND NEW REDUCTION
---------------------------
All eight incoming U212 proposals specify the same literal machine and source.
Seven complete archives contain identical files. The upstream archive (5) is
truncated; its intact CRC-checked parent and builder reconstruct the same files.
See comparison/comparison.json and its eight retained snapshots.

The new construction uses six closed-source rotations, repairs engine entry
171/read0, and merges native state 180 into 163 by reading the preceding tape bit
through existing helper 211. Relative to U212 it changes 16 retained rows and
deletes both rows of state 180. The source keeps 3,909 primitives, 197 subtrees,
maximum depth 42, and maximum zero run 6. Exactly 549 binary source addresses
change; every opcode, operand, and resolved ordinal control edge is preserved.

IMPORTANT LABEL CONVENTION
--------------------------
The proofs use inherited native labels: helper 211 is a WORKING state and
native 254 is halt. In the delivered dense table, helper 211 becomes 196,
merged state 163 becomes 156, and the HALT label is 211. The bijection is in
machine/state_map.json. Native labels are names, not the state count.

VERIFICATION COMPLETED
----------------------
- Six universal local path cases, with opaque/unread tape exterior.
- Eight deliberately damaged controls rejected by the independent checker.
- Complete incoming-edge census for the zero/one predecessor-bit invariants.
- All 3,909 primitive instructions and 5,083 control edges preserved.
- All 5,084 arbitrary-natural primitive contracts freshly rederived.
- All 422 literal rows covered; 1,277,525 symbolic inference applications.
- Four arbitrary-value list-block lemmas rederived; positive affine times.
- Exact 48,140-step blank prefix, identical complete tape and trace to U212.
- Independent finite executor: 15,252 primitive cases, 6,757,680 literal steps.
- Independent finite rejection when the engine-entry repair is removed.
- Selected U212/213/214 dependency reconstruction and finite audit replayed.

The symbolic cases quantify over arbitrary natural registers and gap and an
arbitrary nonempty finite spare list. They use unary/list induction in an
ordinary Python checker; they are not samples of 5,084 numerical inputs.
The independent C++ runs are separately labeled finite regression evidence.

The new fold adds two steps when its merged state reads zero. Source rotations
also change durations. This release claims a state reduction, not a speedup.

FILES
-----
report.tex / report.pdf       Report, mathematical proofs, and full dense table.
machine/                     Native/dense tables, source, relabeling, recipe.
code/                        Deterministic construction and independent checks.
code/runtime/                Byte-identical inherited induction-engine modules.
evidence/                    New local/runtime/startup/finite-check receipts.
comparison/                  Eight source/table snapshots and pinned provenance.
baseline/selected_U212.zip    Exact selected parent with complete dependencies.
baseline/pa_unary_power_cover.zip  Exact supplied unary-theory manuscript/code.
research/                    Discovery discussion and limited search utilities.
licenses/ / NOTICE.txt       Attribution and inherited terms.
SHA256SUMS                   Hash manifest for all other release files.

OFFLINE REPRODUCTION
--------------------
Python 3.10+ with the standard library; no network or solver is needed.
Run with assertions enabled, without -O or PYTHONOPTIMIZE:

  python3 -B reproduce.py
  python3 -B reproduce.py --full --baseline --report /tmp/u211-replay.json

The default checks every file hash, reconstructs all candidate bytes, compares
all eight proposals, replays both local proofs and startup, and audits the
saved symbolic records. --full freshly rederives all 5,084 universal contracts
and compares every case record. --baseline replays the preserved parent chain.
The full check generally takes a few minutes. Temporary outputs are removed;
an optional report must be written outside this sealed package.

Optional independent finite executor (C++17 compiler):

  g++ -std=c++17 -O3 code/check_finite_runtime.cpp -o /tmp/check_u211
  /tmp/check_u211 machine/u211.native.tm machine/sites.tsv

Rebuild the report in a working copy, with a TeX distribution:

  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

PDF bytes can vary with TeX versions and timestamps. Regeneration does not
change the literal machine. Editing a sealed file invalidates SHA256SUMS.

PRIMARY SHA-256 IDENTITIES
-------------------------
Dense table:
91f02738127a5c7e0a681aa88b92f67787d40a7fdc7e40c44ce9e57ef7feab2f
Native table:
ac75e2fa934e89b3c5b3e2ce5f05daa04bb71c4194566208efae03a21f7bc842
Source program:
48143023724f845a96a3bd43ea13b445a5d0153e38ff1e45f05d4181a90a0ca1

Repository snapshot used for the comparison:
VladimirReshetnikov/ProveIt commit 9d50bf3df8c9e14941b549945c4f8400172d81f4.
