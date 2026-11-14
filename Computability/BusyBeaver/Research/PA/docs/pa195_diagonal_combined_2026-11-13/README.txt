PA195DC — a different 195-state machine for Con(PA)
=================================================

Result
------
This package constructs a deterministic binary Turing machine with 195
working states whose nonhalting from the blank tape is provably equivalent
to Con(PA). No verified machine below 195 states was obtained.

The main report proves, in ordinary mathematical form,

  PA |- Halt(PA195DC, blank) <-> exists p Prf_PA(p, code(0=1)),
  PA |- Nonhalt(PA195DC, blank) <-> Con(PA).

The report distinguishes this argument from inherited Lean results and
from the executable finite/symbolic certificates. A new kernel-checked
Lean or Rocq theorem of the entire biconditional is not supplied.

Read report/pa195_diagonal_combined.pdf first. Its complete LaTeX source
and included sections are in report/. Appendix A prints every transition;
Appendix B compares all 32 top-level incoming archives at the pinned commit.

Machine conventions
-------------------
The definitive file is machine/machine.tm. Each row has five fields:

  current_state read_bit write_bit direction next_state

Working states: 0 through 194. Initial state: 0. Separate halt label: 195.
The tape is indexed by all integers and initially contains only zeros.
The head starts at position 0. Directions are L and R, with no stay moves.
There are 390 transitions; the halt label has no outgoing transition and
is excluded from the count. machine/machine.native.tm uses inherited labels
(start 74, halt 254); labels.json is the exact dense-to-native conjugacy.

SHA-256 of machine/machine.tm:
e5cc1b2cb374fa4342070e95d8bdfd60c1bb845e7a52d44857bdee937bba7938

What is new
-----------
PA195DC combines the original bundled-diagonal PA195 emitter and seven
contextual folds with the inherited Combined command controller. Exactly
six native transition rows change. The command semantics and compiled
proof-word construction change, not merely the state names. The source
has 3,676 instructions, compared with 3,700 in the original diagonal PA195.
Complete blank startup takes 57,922 transitions, compared with 58,154.
This startup difference is not a claim of uniformly faster proof search.

The state count is 134 fixed controls + 68 readers - 7 folds = 195.
The new graph is absent from all 422 spanning action-graph classes in the
pinned literal-table census, even ignoring the start root and allowing
tape reflection, global bit complementation, or both. This establishes
finite graph novelty within that corpus, not a state lower bound.

Reproduce the primary result
----------------------------
From this extracted directory, using Python 3.10+ and its standard library:

  python3 machine/build_verify.py
  python3 independent/replay.py
  python3 comparison/verify_novelty.py machine/machine.tm --start 0

Keep assertions enabled; do not use Python -O. No network, optimizer,
solver, or proof-assistant installation is required for these checks.
All three commands passed from a clean copy. Their captured output is in
validation/. The primary build checks exact table bytes, source binding,
4,784 symbolic outcomes for both raw and folded machines, 28 local fold
cases, and the complete blank startup. The independent replay recomputes
its five certificates directly from the literal table and command algebra.

The checkers establish the executable interfaces used by the mathematical
proof; running them does not replace reading the calibration and uniform
compiler arguments in the report. SHA256SUMS covers every delivered file
other than itself. On systems with sha256sum, check it before replay:

  sha256sum --check SHA256SUMS

Contents
--------
machine/       Exact machine, source, primary build/checker, baseline,
               seven folds, initialized tape and deterministic certificates.
independent/   Separate physical and command checkers, recorded certificates,
               input manifest, and byte-exact replay driver.
comparison/    All-archive inventory, literal-table and graph census,
               novelty check, full provenance, and comparison scripts.
report/        Main TeX source, included sections, PDF and build instructions.
references/    Attributed inherited arguments and selected Lean source files.
search/        Bounded local searches, logical source variants, five corrected
               anneals and optional secondary implementation witnesses.
validation/    Output of the three successful clean-copy acceptance runs.

The optional search data records 39,661,078 proposed grammar moves and
49,513 distinct endpoint trees in a final radius-two neighborhood. Neither
search found a sub-195 candidate. These are finite search results, not an
impossibility theorem. Two secondary 195-state implementation witnesses are
retained as research leads; their finite checks are separate from the main
PA195DC consistency proof and are labeled accordingly.

Provenance
----------
All source comparison is against ProveIt commit
5ed5a41fa5932433111eea096311364c6087e8e3:

https://github.com/VladimirReshetnikov/ProveIt/tree/5ed5a41fa5932433111eea096311364c6087e8e3

The report and PROVENANCE.json attribute the inherited emitter, controller,
calculus, and checker components. Original ProveIt and James Chang license
notices are retained beside imported code. The 13 November report date uses
the Pacific-date convention; the latest incoming archive uses 14 November
UTC in its filename. The full original corpus is referenced by immutable
paths and hashes rather than duplicated inside this package.
