FULL CROSSING-BLOCK CAUCHY MODES
Research prepared for Vladimir Reshetnikov, October 26, 2026

MAIN RESULTS

The report reviews all seven ETH packets at ProveIt commit
3c64ee065c708ded485b8b14d9ad6c703a30ab11, including their placement into
Computability/SubexponentialSAT. It develops an integral decomposition of
each full crossing orientation that works at every retained valuation level.
The weights become a+1-i+4q-2*popcount(q), with the old mode multiplicity.

Under the preprint's normalized tensor-contraction interface, with size s,
the new polynomial-space time coefficient is 319.6857570777 on the scale
s/sqrt(log_2 s); 320 is a convenient eventual bound. Combining earlier
factorial modes with the earlier optimized schedule family approaches
368.6540181 on that scale.

A second algorithm caches group functions and uses three block tables plus
division-free rectangular Strassen multiplication. Its time coefficient is
225.5970572839 and its space coefficient is 196.1994455176; convenient
eventual coefficients are 226 and 197.

These are comparisons of explicit exponential upper-bound certificates.
The general SAT exponent order n*loglog(n)/sqrt(log(n)) is not improved.
The constants above are for normalized tensor size s, not directly n.
The source's global counting reductions and interpolation/packing identities
remain dependencies. There is no new Lean certificate or full SAT solver.

CONTENTS

report.tex / report.pdf     Complete mathematical report and proofs.
build_report.py             Recompile with pdflatex, shell escape disabled.
code/joint_cauchy.py        Exact integral kernel over Q and Q[U]/(U^2+U+1).
code/mode_graph.py          Directed mode-graph, caching, block tables, Strassen.
code/exact_weight_index.py  Dynamic-programming exact-weight ranking/unranking.
code/verify_*.py            Local correctness checks, not SAT benchmarks.
code/compare_certificates.py Exact mode counts and analytic coefficient table.
results/                   Complete JSON records and mode-count CSV.
provenance/                Source pins, archive/report hashes, proposal inventory.
audit/                     Independent comparative and mathematical review notes.
MANIFEST.sha256            SHA-256 file inventory for this deliverable.

REPRODUCE

Use Python 3.10 or newer, with no third-party Python packages:

  python3 code/verify_joint_cauchy.py
  python3 code/verify_mode_graph.py
  python3 code/verify_joint_cauchy_independent.py
  python3 code/compare_certificates.py

The first two tests can also be run with python3 -O. The independent checker
also uses explicit checks and supports an optimized replay. Finite checks
validate the implemented algebra and summation, not the asymptotic theorem.
Exact-weight index lists are generated using polynomial-size count tables;
they do not assume an oracle for completion counts.

To rebuild the report:

  python3 build_report.py

This requires pdflatex and the standard packages in report.tex. Auxiliary
files are kept in _build/. The supplied PDF was compiled and visually checked.
No original source repository was modified or submitted to during this work.

PROVENANCE AND PRIORITY

The classical Cauchy identity and Strassen algorithm are not new. One prior
packet already proves the local i=0 Smith spectrum. The additional result
here constructs a compatible full-orientation decomposition at all i, with
the required source/target locality and without a mode-family penalty, then
pays the full cost of an optional mode-graph aggregation. No global priority
claim is made beyond comparison with the reviewed source corpus.
