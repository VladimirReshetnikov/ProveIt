PA196 COMPARISON, SOURCE FACTORIZATION, AND PROOF OBLIGATIONS
13 November 2026

STATUS

The requested machine below 196 working states has NOT been constructed.
The strongest new exact size result is a 157-internal-node source tree,
down from 159, with the complete 3,812-instruction register-program CFG
unchanged. This is not a 157-state TM. The prospective 195-state estimate
loses an existing decoder helper and is not a valid state-count result.

Read report.pdf (compiled from report.tex) for the mathematical comparison,
new source result, physical helper obstruction, finite searches, native
HA-strength calculus, canonical proof-stack repair, and further research
questions. Every statement distinguishes its verification level.

PINNED SOURCES

  James Chang PA196: 407cdc356f6b586635e71ac92be394255f4bfea4
  James Chang PA209: 69d98241a721ead20b4f0b17df9062950b40fbfe
  ProveIt:          f1f076e31995f10460838d1846456f4bb9c8ae80

No repository was modified, committed, or pushed by this research.
The upstream PA196 publication/source checks passed. The full Lean project
was not rebuilt; no new kernel-checked theorem is claimed.

FAST REPLAY

From this extracted directory, using Python 3:

  python3 verify.py

This verifies delivered file hashes when SHA256SUMS.json is present,
machine state/row counts, the nine-table U208 classification, complete source
CFG identities, source-node counts, the generated Compact157.lean data,
deterministic two-edit factorization, an intentionally altered graph control,
and the nine native-checker implementation controls.

SOURCE WITNESSES

  source_reductions/source157.json
    157 internal nodes; 3,812 leaves; maximum path length 37;
    maximum zero run 6; seed site 25 still has path 100000.

  source_reductions/layout158.json
    158 internal nodes; an incomplete estimated physical cost of 195;
    that estimate is NOT a compiled machine. Seed path is 1000000.

  source_reductions/essential158.json
    Readable two-edit common-factor construction; 158 internal nodes;
    maximum zero run 8; missing old helper shape. Full CFG unchanged.

  source_reductions/Compact157.lean and EssentialProgram.lean
    Definitions-only source renderings, not Lean-compiled in this session.
    They import the upstream M6 source-tree datatype. No machine theorem
    has been transported merely by copying an old theorem statement.

The SHA-256 digests and independent source audit are in the same directory.
The minimal 158-node construction is reconstructed by:

  python3 search/source_analysis/build_essential.py \
    search/source_analysis/upstream /tmp/pa196-essential

OPTIONAL SOURCE SEARCH

The exact witness can be checked without repeating a stochastic search.
For a seeded grammar-size experiment similar to its discovery run:

  python3 search/rotations/anneal_source.py --steps 250000 --seed 137 \
    --temp .20 --max-zero 6 --max-depth 38 --output /tmp/pa196-anneal

The optimizer output is not trusted: independently compare its full source
CFG before using a result. Physical-cost objectives are only estimates and
can omit helper-state costs; the report explains a concrete failure.
Recorded search receipts retain their original experiment labels.
The separately scoped physical allocation model and its reproduction commands
are in search/allocation/README.txt (requires z3-solver).

OPTIONAL LARGER SCREENS

1. Source-conditioned local folding (Python 3 and C++17; no network):

     python3 search/local_folds/reproduce.py

   This regenerates all 4,959 symbolic instruction contracts and 2,219
   admitted five-cell contexts, checks 353 concrete fixtures, and reruns
   the single-helper, retained-two-row, and two-arbitrary-row screens.
   It independently replays six synthetic positive controls. It can take
   several minutes. Every component was run during the research; the
   combined wrapper is supplied as an offline reproduction convenience.

2. Joint register abstractions and targeted helper reassociation:

     cd search/source_analysis
     python3 prepare_graph.py upstream /tmp/pa196-source
     python3 helper_associations.py upstream baseline_decoder_aliases.json \
       /tmp/pa196-helper-associations.json
     g++ -O3 -std=c++17 joint_trits.cpp -o /tmp/pa196-product
     /tmp/pa196-product /tmp/pa196-source/source_graph.txt /tmp/trits.bin 3
     /tmp/pa196-product /tmp/pa196-source/source_graph.txt /tmp/quads.bin 4
     g++ -O3 -std=c++17 relational.cpp -o /tmp/pa196-relational
     /tmp/pa196-relational /tmp/pa196-source/source_graph.txt

   The four-category run is considerably larger than the fast checks.
   Generated bitsets are intentionally omitted; their hashes and compact
   receipts are supplied. Negative screens are not global state lower bounds.

NATIVE HA REFERENCE CALCULUS

  python3 logic/verify_reference.py
  python3 logic/native_ha_checker.py < logic/compound_progress_certificate.json

This is a written HA-strength extension of the report-level witness calculus
with full formula-template transport. It is not an established extension
of the minimized trOne Lean kernel. The explicit checker changes only DI.
No compiler or binary-TM state budget is supplied. The PA consistency
translation is a mathematical proof plan/metatheorem, not an implemented
PA proof-code compiler.

BUILD THE REPORT

With a standard LaTeX installation including the listed packages:

  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

PROVENANCE AND RIGHTS

Upstream files retain their original licenses and attribution in provenance/
and the corresponding input directories. Historical runtime and U208 notices
are included. These authors have not reviewed or endorsed this research.
The packet does not relicense inherited materials wholesale. New analysis,
reference code, and reports are supplied for review and further research.

The text notes in logic/ and search/ retain simple Markdown notation in .txt
files for portability. The complete typeset account is report.pdf.
