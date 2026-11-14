U212 by combining direct transfer and a contextual bypass
========================================================
Research prepared for Vladimir Reshetnikov, 28 October 2026.

RESULT
------
machine/u212.tm is a complete 212-working-state, two-symbol, single-tape
Turing machine including its blank-tape initializer. Working states are
0..211, initial state/head are 0, the entire two-way infinite tape is 0,
and halt is the separate label 212. All 424 transitions move L or R.

The chosen parent is U213_ConPA_2026-10-28 (1).zip. The entry-bypass idea
from u213_from_u214_2026-10-28.zip transfers after translating helper 167
to native 211 in this different physical allocation. The exact native patch:

  180/read1: (1,R,172) -> (1,R,211)
  172/read0: (0,L,112) -> (0,L,67)
  Delete both outgoing rows of native 112. No other retained row changes.

Four universal local path identities and complete incoming-edge invariants
prove halting equivalence with the exact parent from state 0 on any common
initial tape. The finite-trace argument is formalizable in PA, and gives

  PA |- Halt(U212, blank) <-> Halt(parent U213, blank).

Composing with the explicitly retained parent's numerical calculus and
Theory U/PA mathematical calibration yields

  PA |- not Halt(U212, blank) <-> Con(U) <-> Con(PA).

This is a mathematical proof with executable verification; no new
end-to-end Lean, Rocq, MM0 or exported PA certificate is claimed. The
independent fixed K215/ZFC certificate is not used to certify this table.
No global minimality or discovery-priority claim is made.

WHAT WAS VERIFIED
-----------------
- All eight incoming U213 tables compared, with exact source/CFG metrics.
- Four opaque-exterior local path identities; six damaged controls rejected.
- Identical complete calibrated blank prefix through 48,140 transitions.
- Same 3,909-primitive, 197-subtree source as the selected direct-transfer parent.
- All 5,084 arbitrary-register symbolic contracts freshly rederived.
- All 424 final literal rows covered;1,275,761 symbolic inference steps.
- Minimum constant term of each literal simulation duration is 5.
- Dense/native relabeling, full table closure and212 graph-reachable states.

The runtime contracts quantify over arbitrary natural primary registers,
gap and a nonempty finite spare list; they use unary/list induction.
They are not samples at 5,084 particular numerical input vectors. The
checker is ordinary Python, with its induction rules outside a small
proof-assistant kernel.

The 48,140-step endpoint is an interior axiom-command frame, not the first
dispatcher entry or the U214 clean root. Its native state is 84, head -2,
header 54, source ordinal 136, registers (1,0,13,0,0,1,0,0,1), and 43 spare
registers equal to 1. The full tape has 120 one-cells and zero exterior.
The parent's protected-tail/credit argument is preserved exactly.

FILES
-----
report.tex and report.pdf     Full comparison, proof, calibration and table.
transition_table.tex         Complete generated dense transition table.
machine/u212.tm              Primary dense literal table.
machine/u212.native.tm       Same table in inherited native labels (halt 254).
machine/state_map.json       Exact dense/native bijection.
machine/sites.json           Unchanged calibrated source.
machine/stage1.native.tm     Bypass intermediate, still 213 states.
inputs/parent_*.zip          Exact complete selected parent and dependencies.
comparison/                 All eight input tables/sources and comparison.
code/                       Deterministic build and independent proof checks.
code/vendor/                Byte-identical parent induction engine/helpers.
evidence/                   Receipts, runtime case records, startup and audits.
licenses/                   Retained upstream terms and attribution.
SHA256SUMS                  Integrity manifest for all other delivered files.

REPRODUCE OFFLINE
----------------
Python 3.10 or later; standard library only; keep assertions enabled.

  python3 -B reproduce.py
  python3 -B reproduce.py --full --report /tmp/u212-replay.json

Default: all hashes, table reconstruction, native/dense bijection, independent
four-case proof, startup, exact comparison, saved runtime coverage, and the
selected parent's complete finite/default audit. --full additionally
reconstructs every U212 symbolic contract and compares every saved record.
The optional --parent-full flag also rederives the parent's full runtime.
No network, optimizer, solver or proof assistant is needed.

Temporary work is deleted automatically. A supplied --report path is the
only persistent replay output; choose it outside the sealed package.
Do not use -O or PYTHONOPTIMIZE with the full runtime/reproduction driver.
The independent local checker itself also works with assertions disabled.

Rebuild the PDF in a working copy with two passes:

  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

PDF metadata can vary with build time and TeX version; literal machine
identities are independent of PDF regeneration.

LITERAL IDENTITIES (SHA-256)
---------------------------
Dense:
c979e55e6a6f75b08effdf67067cceb460e30a4c28aef9c79797d0a6d32a074e
Native:
386ce16259d4c97e4af31b3ba494feaff11a0a1a066e0235dddc154b4cea38c4
Unchanged source:
7b6539dc67b66ff73f22554018d7af5985d85574460a73fea5f025103c523d00

For a halting computation from the common start, the literal times satisfy
T212 <= T213 <= (7/3) T212, and T213-T212=4r+2s for the specified exceptional
block counts. This conditional comparison does not assert that either blank
machine halts.
