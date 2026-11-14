CON(PA) TURING-MACHINE COMPARISON AND REDUCTION STUDY
13 November 2026

RESULT STATUS
The requested construction with fewer than 196 working states was NOT obtained.
This packet does not claim a 195-state machine. The strongest new complete
intermediate has 196 binary working states, with a written PA-provable
consistency calibration, exact blank startup, and 4,928 uniform instruction
contracts. Its changed logical proof has not been exported as a new Lean theorem.

START HERE
report.pdf                 Complete comparison, proofs, results, and limitations.
report.tex                 Editable LaTeX source; additional chapters/ are included.
machines/h_only_mp_h.tm     Complete 392-row transition table of Combined196.
machines/direct_negation197.tm  Complete 197-state direct-negation variant.
machines/*_sites.json       Exact resolved-source input specifications.
verify.py                  Replays the finite and symbolic certificates.
comparison/                Selected 208/209/196 tables and canonical comparison.
provenance/                Exact source pins, archive hashes, provenance, notices.
research/                  Clearly separated source/layout and parity experiments.
reference/                 Pinned source excerpts and upstream attribution.
receipts/                  Machine-readable validation results.

REPRODUCE
  python3 verify.py
  python3 verify.py --extended
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  # Alternative with an isolated missing-format fallback:
  python3 build_report.py

Python uses only the standard library. The extended check includes the larger
207-state physical realization of the repaired 157-node source and the 197-state
direct-negation specialization with 3,556 source instructions. The scripts do
not rebuild the upstream Lean development. See the pinned upstream reproduction
instructions for that separate task. All symbol/state counts use a binary,
single-tape, deterministic, left/right-moving, blank-input machine with one
terminal label not counted among the working states.

TABLE FORMAT
Each noncomment row is: current_state read_bit write_bit L_or_R next_state.
For Combined196, working labels are 0..195, the initial control is 0, the blank
symbol is 0, and the terminal label is 196. The tape extends in both directions.
No bound on observed execution is used as evidence of nonhalting.

PROVENANCE AND CREDIT
The research builds on the supplied works of James Chang and Vladimir Reshetnikov,
their predecessor sources, and the research packets already present in the
pinned incoming directory. Their notices are preserved under provenance/notices
and reference. Earlier negative findings, source reductions, and paper-level
proof arguments are identified as prior work in the report. Selected comparison
and symbolic-runtime code is adapted from those inputs; exact input-table
membership was rechecked against all 18 current top-level archives.

The parity control table is a COMPONENT ONLY: it has not integrated the new
formula encoding or discharged its blank-startup obligation. It is not an
additional complete Con(PA) machine. The 157-node source has a verified 207-state
realization and does not imply a 157-state or 195-state Turing machine.
