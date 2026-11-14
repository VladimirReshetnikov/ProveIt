A 195-STATE PA CONSISTENCY TURING MACHINE
========================================

Primary result: machine_195S.tm
  195 working states, numbered 0..194; initial state 0; terminal halt 195.
  Two-way infinite binary tape, initially all 0; head initially at cell 0.
  Every row is: current_state read_bit write_bit direction next_state.
  Write, then move L or R, then enter the next state. Halt has no rows.
  There are 390 transitions. The halt control is excluded from 195.

MATHEMATICAL RESULT
  PA proves Nonhalt(machine_195S) <-> Con(PA), by the finite-trace
  preservation theorem in report.pdf and the inherited calibration of the
  supplied separate-diagonal-head 196-state parent. The source program is
  exactly unchanged; 67 AX readers replace 68, retaining six compatible
  folds: 134+67-6=195. No axiom, head order, parameter assignment, guard,
  stack position, command semantics, or scheduler changes.

  This archive provides an ordinary mathematical proof and executable
  finite/symbolic certificates. It does not claim a new end-to-end Lean
  theorem. The imported arithmetic-box interfaces and existing logical
  calibration are explicitly identified in the report and source files.

READ FIRST
  report.pdf / report.tex : comparison, construction, proof, complete table.
  construction195/README.md : main portable construction and provenance.
  construction195/rebuilt_195S/verification.json : primary full receipt.
  source195_audit/preservation.tex : detailed two-way PA trace argument.

REPRODUCTION (Python 3.10+, standard library only for the primary checks)
  python3 construction195/verify_manifest.py
  python3 construction195/build_check.py
  python3 source195_audit/audit.py
  python3 construction195/rotation_witness.py
  python3 physical195_audit/replay.py

  Do not run with Python -O. The main builder deliberately rejects it.
  It reconstructs the exact supplied parent, validates its emission and
  source bindings, then checks the 195-state grammar, all 4,780 arbitrary-
  register primitive cases, and exact 58,154-step complete-tape startup.
  The source audit additionally checks the full CFG with two independent
  resolvers and binds the unchanged 44 native arithmetic-box rows.

INDEPENDENT PHYSICAL CERTIFICATE
  physical195_audit/ checks every source outcome over arbitrary natural
  registers, arbitrary nonempty spare lists and gaps at least 48. It
  follows literal transitions and rederives four generic list lemmas;
  it uses no arithmetic-box oracle. Both 195S and 195C passed. The complete
  per-outcome certificates and exact blank seeds are under recorded/.
  This full replay takes several minutes; the frozen certificates are
  included, so rerunning it is optional.

SUPPLEMENTAL CONSTRUCTION
  machine_195C.tm has 195 states and uses the same grammar with the changed
  Shift/MP controller. Run:
    python3 construction195/build_check.py --combined
  It has 3,649 source instructions and 4,749 passing symbolic cases; exact
  blank initialization takes 57,922 steps. The command proof for this
  controller is in independent_verification/composite_command_audit.tex.

SUPPORTING MATERIAL
  inventory/ : all 27 incoming archives, nested ZIPs, main PA tables,
               canonical graph census and rejected candidate evidence.
  construction195/search/ : actual successful search source and receipts.
  axioms/ : two earlier 196-state compositions and their executable checks.
  independent_verification/ : independent context checker and bounded
               reduction experiments on the 196-state precursors.
  direct_negation197/ : valid source shortening requiring 197 controls.
  prospective_recoding/ : mathematical encoding idea; no smaller table claim.
  logical_background/ : inherited diagonal-calculus argument and provenance.
  manifest_sha256.json : byte hashes of the complete release.

Compile report.tex twice with pdfLaTeX in this directory. The complete
primary transition table is also printed in the PDF appendix.

Source snapshot: ProveIt 906367250a7f96c923147b10df392294bced7be5.
The census describes that fixed source corpus; the two 195-state machines
were constructed subsequently during this investigation.
