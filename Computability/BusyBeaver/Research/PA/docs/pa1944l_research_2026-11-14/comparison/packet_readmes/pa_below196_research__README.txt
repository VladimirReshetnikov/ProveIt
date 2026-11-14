PA CONSISTENCY MACHINES: CURRENT COMPARISON AND REDUCTION EXPERIMENTS
13 November 2026

OUTCOME

No verified binary blank-tape Turing machine below 196 working states was
obtained. The requested construction remains unresolved. This archive is a
research and verification packet, not a successful 195-state machine.

Read report.pdf or compile report.tex with its three result-table includes
and archive_table.tex. All substantive deliverables are in this archive.

SOURCE PIN

ProveIt: 3268f238cb6be4b9c68b6cddaf289f173f77566e
Imported PA196: 407cdc356f6b586635e71ac92be394255f4bfea4
Imported PA209: 69d98241a721ead20b4f0b17df9062950b40fbfe

THE IMPORTANT DISTINCTIONS

1. A source instruction count is not a physical state count.
2. An allocated or finitely tested table is not automatically a verified TM.
3. The imported formal arithmetic endpoint is

       PA proves Nonhalt(PA196) -> Con(PA).

   The internal converse required for the requested biconditional remains
   a separate proof obligation in the compared repository. Standard-model
   nonhalting does not by itself supply that PA theorem.
4. Negative searches here are limited by their explicit templates; they are
   not general lower bounds on the number of states required.

CONTENTS

report.tex, report.pdf, *_results.tex, archive_table.tex
  Complete report, proofs, comparison tables, experiment results and further
  research questions. The PDF is compiled from these exact LaTeX sources.

census/
  All 23 top-level archive identities, recursive inventory of 36 unique ZIP
  payloads and 1,223 literal TM members, and 15 pairwise nonisomorphic
  designated 196-state reference tables. Thirteen have reported uniform or
  constrained physical checks; two are experimental MP variants. Also
  includes 27 U208 presentations in 20 graph classes and every supplied
  195-state diagnostic, labeled with its rejection scope.

gates/
  Eight propositionally equivalent gate spellings and the finite dynamic
  program proving the restricted six-implication matrix minimum.

gate_search/, membership_search/
  Exact C++ search inputs, discovery code, retained grammar witnesses and
  independent Python audits. The first varies eight gate spellings; the
  second also transposes membership/equality constructor arguments.
  Reader matching is a discovery score, not a physical simulation proof.

theory/
  Portable ordinary proofs and local source/encoding constructions:
  - exact decoding-preserving involution for constructor orientations;
  - concrete freshness-guard obstruction R(5)=9;
  - a pairing macro shortened from 67 to 37 sites, with a larger source DAG;
  - a correctly scheduled transposed-implication AX prefix;
  - a counterinterpretation rejecting a tempting axiom-head replacement.

physical_search/
  Wider two-row fold search, displaced-head projection search, the explicitly
  partial 84-pair three-row search, positive controls and exact receipts.
  Also a proved seven-site H-only Shift guard specialization, reducing the
  source to 3,807 sites but increasing its DAG to 163 internal nodes.

reference/
  Verbatim theorem inventory and repository comparison/bridge notes, with
  their source licenses. Relative links in those notes refer to the pinned
  repository layout.

verify_all.py, verification_receipt.json, SHA256SUMS.json
  Portable quick checks, the actual checked outcome, and file integrity.
  A digest proves byte identity, not a theorem.

QUICK REPRODUCTION

Python 3.10 or later; standard library only. Use assertions enabled.

    python3 verify_all.py

This checks the byte manifest, copies the relevant subpackages to a fresh
temporary directory, and runs their finite verifiers there. It does not
modify the supplied evidence. It checks the census, U208 helper controls,
source guard, all six theory routines, the independent physical-reader
scores, and independent synthetic local-fold controls.

It does not rerun billions of search assignments, build the imported Lean
projects, certify simultaneous reader folds, or prove a PA biconditional.

EXTENDED REPRODUCTION

g++ with C++17 is required for the longer searches. Each grammar-search
directory includes search.cpp, inputs.hpp, inputs.json and search_summary.json.
Compile and run it with the iteration count and seed in that receipt:

    g++ -O3 -std=c++17 search.cpp -o /tmp/pa_search
    /tmp/pa_search ITERATION_COUNT SEED /tmp/pa_new_run

Run this from the selected search directory. The output prefix must refer to
a fresh destination. Stochastic witness discovery can depend on the compiler
and floating-point environment; verification of the retained exact witnesses
does not depend on replaying discovery.

For the completed physical screens:

    python3 physical_search/replay.py physical_search/pa196.tm \
        --output /tmp/pa_physical_replay.json

The optional --shared-three flag launches all 348 selected pairs and is a
larger experiment than the 84-pair partial result recorded in this packet.

PDF REPRODUCTION

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

If an installed TeX Live distribution has missing generated format/index
files, the optional tools/build_pdf_fallback.py creates a private temporary
format and font map without changing the system installation or TeX source:

    python3 tools/build_pdf_fallback.py report.tex

ATTRIBUTION

Original machine, source, and proof authors retain their attribution and
licenses in the relevant subdirectories. This research does not represent
them as having reviewed or endorsed the new experiments. No original
repository table or theorem statement was edited, and nothing was pushed,
published as a PR, or sent to another person.
