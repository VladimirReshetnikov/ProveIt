NEW LEAN PROOF SIMPLIFICATIONS FOR THE CYCLIC AND WANG DEVELOPMENTS
26 October 2026

Start with report/report.pdf or its editable report/report.tex.
This continuation proposes specific new changes after comparing the incoming
manuscripts. It does not repeat their broad abstraction recommendations.

PROVENANCE
  Proof source: b310142330df89e48413c8fce62e7de223e1c7d5
  Bounded late comparison: 9bd29079d5e1c6cc1c0bcaee6cb57d59b835cba9
  Lean: 4.32.0; mathlib: 81a5d257c8e410db227a6665ed08f64fea08e997
  Repository: https://github.com/VladimirReshetnikov/ProveIt

The first comparison covered five incoming ZIPs and one retired/placed
manuscript. A final bounded comparison covered five additional arrivals:
11 actual manuscripts in total. The edited source modules and marked-word
adapter were byte-identical at the two source pins. This is not a claim of
global originality or a fresh Lean build at either pin.

NEW PROPOSALS
  1. Specialize binaryWord_prefix directly in the two South-word proofs.
  2. Reuse theta as the difference-cell witness, and derive zero-base
     propagation from the existing arbitrary-base propagation theorem.
  3. Derive two guarded boundary-color fibers once, then specialize the
     eight exact-color corollaries without repeating family elimination.
  4. Optionally characterize any independently extracted selector-index
     assignment over the SAME original word, then transport marked-word
     correctness by equality. This API adds code and claims no current saving.

The three-module core patch set changes 534 to 462 physical lines and
20,980 to 19,664 UTF-8 bytes, including new helper declarations. The optional
47-line selector module is not included in that saving. Older Cell/iteration,
constructor-view and uniqueness-transport ideas are credited rather than
presented as new general strategies. Reflected-parity drafts were excluded.

VERIFICATION STATUS
  All new Lean code remains UNCOMPILED.
  Source hashes, unchanged declaration text, exact patch application and
  finite arithmetic regressions were checked. These checks do not establish
  Lean elaboration, kernel acceptance, performance or full-project integration.
  No upstream source, public repository, or prior delivered archive was changed.
  See VALIDATION.json and the report for exact scope.

PACKAGE LAYOUT
  report/       New report, TeX and an installed-TeX rebuild script.
  cyclic/       Two original/candidate modules, patches, metrics and regressions.
  wang/         Guarded-fiber prototype, proposed module, patch and validators.
  occupation/   Optional additive selector-binding API, tests and patch.
  audit/        Read-only patch/signature and finite source-address audits.
  evidence/     Source inventory and the bounded late-comparison evidence.
  catalog/      Exclusion/novelty ledgers and prior manuscript reference copies.
  baseline/     Main Lean source snapshot plus selected documentation.

The catalog contains OLD manuscripts only as exclusion evidence. They are not
new results of this report. Its reference copies are not complete original
packets; full archives can be recovered using the recorded repository paths,
arrival commits and SHA-256 values. Prior compilation claims are not promoted
to validation of these new candidates.

The baseline contains all 574 files under the pinned main Lean directory,
not the full repository/dependency closure. The broad inventory separately
records 761 Lean files, including archived research material outside it.

READ-ONLY STATIC REPLAY
  Requires Python 3 and Git; no Lean, network access or installation:
    python3 -B verify.py
    python3 -O -B verify.py
  These commands check every sealed byte, the pinned main sources, reference
  manuscript hashes, exact patches, finite regressions and failure controls.
  Temporary patch-application trees are removed afterward. Output goes to
  stdout; redirect it OUTSIDE the sealed package if saving a new receipt.
  PASS_STATIC_REPLAY is not a Lean verification result.

  To inspect the original complete source census:
    python3 inventory.py /path/to/full/ProveIt

BEFORE ADOPTING A PATCH
  Use a disposable checkout at the proof pin with its exact pinned toolchain.
  Establish an unchanged baseline, inspect/apply the three core patches,
  and build dependencies serially, one Lean process at a time. The repository
  README warns that LAKE_JOBS=1 alone does not prevent dependency fan-out.
  Compile the original and changed modules, the affected reverse dependencies
  and explicit check/audit modules; inspect theorem types and axiom reports.
  Test the optional selector API separately. An import-only prototype and an
  in-place replacement are alternatives, not files to load simultaneously.

  Preserve N=1, arbitrary whole-period shifts, exact original selector bits,
  the c>=434 fiber guard, initializer South=4, halting target 215, and all nine
  seam tuples. Do not add a coprimality, unique-Start or machine-run premise.
  Measure actual elaboration/memory effects rather than inferring them from LOC.

The report does not claim the final polynomial-to-Con(ZFC) equivalence,
full machine-run extraction, controller completeness or an internal-ZFC proof.
The original source license is retained in baseline/LICENSE.
