Logical source alternatives: focused research artifacts
======================================================

Scope
-----
The actual QT244 construction retains the original logical theory.  This folder
contains alternative-basis and source-encoding research, with positive proofs,
measured negative compiler controls, and independently replayable obstructions.
None of the alternative source families is itself a new certified machine bound.

formalism_report.tex is a body-only LaTeX appendix.  Include it from the main
report with amsmath and url or hyperref loaded.  formalism_notes.txt is a longer
working record; its shared-helper deletion discussion concerns an earlier,
rejected proposal and does not concern the successful QT rotation.

Main checks (tested with Python 3.12; standard library only)
-----------------------------------------------------------
Run from this folder:

  python formalism_verify.py

This independently replays both condensed-detachment certificates, including
rigid falsity, disjoint premise variables, and an occurs check.  It also verifies
every substitution instance and MP closure for the three supplied finite
matrices.  The stored output is formalism_verification.json.  The finite matrices
only refute derivability in their explicitly stated propositional fragments;
they are not models of the full CP/GIC set theory.

  python formalism_fusions.py
  python formalism_kbp_sources.py
  python formalism_kbp_sources.py --peirce-f

These regenerate 1368 equality-root fusions, 1296 K/B/Peirce sources, and 648
K/B/fixed-falsity-Peirce sources.  Every word's symbolic stack and parameter read
events are checked.  The three-field AX codec and twelve-cell push contract for
the latter two families are part of the mathematical source bridge in the report.
Fine word lengths are not state counts.  Companion grammar files record the
charged source-to-grammar searches and their negative results.

  python formalism_split_bundle.py

This regenerates four complete tables using the included original Wade backend:
original and reemitted controls have 281 working states; split outputs have 290;
the version sharing its zero scrub has 288.  It checks every source decision edge
against the generated table and 192 exact helper cases.  The tables are labelled
compiler cost controls: they do not carry a new binary simulation theorem.

  python formalism_shared_gate_counterexample.py

Two literal source interpreters reproduce three exact failures of the rejected
shared-gm deletion.  This script imports formalism_dirty_seed.py for its literal
interpreters and parses the original formalism_reference/Dag254.v.  The finite
dirty-seed bootstrap files are optional historical evidence and are unrelated to
the clean initialization of the final QT244 construction.

Portable dependencies and attribution
------------------------------------
Keep formalism_reference/ beside all Python scripts.  It contains the original
symbolic emitter, fine macro dictionary, set-theory specification, 219-node source,
and public Wade compiler.  PROVENANCE.json records original locations, pinned
commits, and SHA-256 hashes.  LICENSE.wade accompanies the included backend.
formalism_kbp_sources.py also imports formalism_fusions.py.

formalism_cdbasis.cpp and formalism_cd_kbpf.cpp are optional C++17 search programs
adapted from the pinned upstream cdfast.cpp.  They are not trusted by the Python
certificate replay.  No C++ compiler, proof assistant, network service, or external
Python package is needed for the principal finite verifications.

The separate grammar outcome files are:
  grammar_work/fusion_search_summary.json
  grammar_work/kbp_seeds_audit.json
  grammar_work/kbp_search_summary.json
  grammar_work/kbpf_seeds_audit.json

formalism_PACKAGE.json lists the focused files and their hashes.  It deliberately
omits unfinished search outputs and Python bytecode.  The main archive's machine
certificate and report establish the actual 244-state result; this appendix
provides the alternative logical research and measured compiler experiments.
