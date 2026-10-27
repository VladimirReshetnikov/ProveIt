ADAPTIVE EVALUATION OF THE SUBEXPONENTIAL SAT MODE GRAPH
Research prepared for Vladimir Reshetnikov with ChatGPT
October 26, 2026 (Pacific time)

START HERE
  report.pdf                 Complete research report and proofs.
  report.tex                 Main LaTeX source; includes sections/*.tex.
  PROOF_STATUS.json          Machine-readable scope and proof dependencies.
  INTEGRATION.txt            Suggested repository placement and review order.

RESULTS
Write E(s) = s / sqrt(log2(s)), with s the normalized Boolean-wire count
in the inherited tensor-contraction interface, not the SAT variable count.
Polynomial factors in the total input length are suppressed here.

1. Adaptive quartet conditioning: polynomial space and time
   2^((C_Q + o(1)) E(s)), with
   50.30468921409 < C_Q < 50.30468921410.
   A safe eventual coefficient is 50.305.

2. Joint adaptive cached contraction: time and space
   2^((C_J + o(1)) E(s)), with
   C_J = (pi sqrt(2)/ln(2)) sqrt(20 log2(9))
         sqrt(2489356/6638625)
       = 31.25239731265091985790016369...
   A safe eventual coefficient is 31.253.

These are relative theorems importing the exact upstream deformation,
recovery, packing and mode-factorization interfaces explicitly listed in
the report. They reduce explicit exponential upper-bound coefficients.
They do not improve the exponent's logarithmic order or independently
certify the upstream claim about ETH.

The reference polynomial-space comparison is 55.40466590661, a composition
stronger than the lowest displayed incoming value 55.70947831891. The
reference cached time/space pair is 35.354588058401/34.274803005023.
No dominance is asserted over conditional unimplemented summation targets,
stronger-assumption low-degree bounds, or unspecified constants in the
separate Claude manuscript. Keeping the existing specialized algorithms
alongside these two new algorithms preserves their applicable bounds.

REPRODUCE THE CHECKS
From this directory, with Python 3.10 or later (tested with Python 3.12.14):

  python3 run_checks.py
  python3 -O run_checks.py

No third-party Python packages and no network are required. These commands
run five independent scripts and write deterministic JSON results under
results/. The optimized replay confirms that no verification depends on
removable Python assert statements. The scripts check exact identities,
finite contractions, rational covariance formulas, strict schedule gates,
and certified intervals for the coefficients. They are not a complete SAT
solver, fast-matrix implementation, or proof assistant development.

REBUILD THE PDF
Install a standard TeX Live distribution with pdflatex and the packages
listed at the top of report.tex, then run:

  python3 build_report.py

The script compiles three times into build/, checks unresolved references,
and copies the complete PDF to report.pdf. Build logs remain in build/.
The supplementary triangle_precursor.tex is an earlier 34.325-coefficient
argument retained for context; it is not an input to the final report and
is not a standalone LaTeX document.

FILE MAP
  code/          Original exact finite evaluators and arithmetic checkers.
  results/       Machine-readable outputs and replay status.
  sections/      Complete proofs of the two new bounds and degree-flow lemma.
  provenance/    Twenty-packet claim ledger, immutable paths, source hashes,
                 commit history and verified relocation record.
  audit/         Separate mathematical and source review notes. These are
                 natural-language/computational reviews, not formal proofs.
  supplementary/ Earlier triangle-only analysis and its exact checks.
  MANIFEST.sha256 SHA-256 hashes of every other delivered file.
  verify_manifest.py  Validate all manifest entries without third-party code.

SOURCE SNAPSHOTS
Initial review: fd0edd17e6a29117179b40a453c0def59165bd7c
Closing review: dde01c4a63b822c25b8eb345299346c36f837b49
Repository: https://github.com/VladimirReshetnikov/ProveIt

The initial review covers fifteen integrated packets and five incoming
archives in the requested directories, plus the two primary manuscripts.
The closing placement commit 450252e9d86c155f188b485629b9755c5c665371
moved all five archives under SubexponentialSAT/Research. Every one of the
230 archive members matches its closing Git blob byte for byte. Thus all
twenty committed packets are included. The archive records fingerprints
and immutable links to external source material; it does not duplicate
the entire upstream collection. No upstream repository files were changed.

The conserved degree-flow lemma is a separate exact algebraic result. The
report explains why degree conservation alone does not yet supply a cheap
recursive entry evaluator or a smaller-order SAT algorithm.
