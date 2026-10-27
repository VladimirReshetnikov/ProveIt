SHARPER PACKET PACKING FOR SUBEXPONENTIAL EXACT COUNTING
Research report prepared for Vladimir Reshetnikov, October 26, 2026

MAIN RESULT

The new deterministic packet-balancing lemma and additive precision guard,
combined with earlier factorial Cauchy modes and exact Hermite precision,
give the normalized tensor-contraction upper bound

  (s + description_length)^O(1)
    * 2^((95.6639404728982... + o(1)) * s / sqrt(log2(s))),

where the exact coefficient is 9*pi*sqrt(22)/(2*ln(2)).

The strongest reviewed individual explicit certificate was 648.4410666488.
Combining that existing schedule with the earlier Cauchy basis already gives
374.3776243833. The report compares against this stronger combined baseline.
The ratios are comparisons of upper-bound coefficients, not runtime ratios.

The general SAT logarithmic order remains
  n*log(log(n))/sqrt(log(n));
the fixed-density order remains n/sqrt(log(n)).
No smaller unrestricted logarithmic order is proved in this package.
The number 95.664 is per normalized tensor size s, not per SAT variable n.

WHAT IS NEW

1. A two-stage deterministic multigraph labeling: greedily balance row
   degrees, then minimize an exact exponential conditional potential over
   column labels. It replaces the source's sufficient D^2*Delta packing
   scale by D*Delta times logarithmic factors.
2. Padding is asymptotically 1+o(1), so the mode-family coefficient becomes
   2 instead of 6 and child size becomes (2+o(1))*M/r.
3. The cumulative packet exponent is sum(u_j) plus an additive squared-log
   guard, replacing 2*sum(u_j).
4. A completely specified rational schedule and full bit-cost analysis.

The factorial Cauchy basis, precision coefficient six, density reductions,
scalar parity lift, and streamed coefficient extraction are credited prior
work from the seven reviewed archives. Their stronger conditional targets
remain conditional. Concentration and conditional expectation are classical;
novelty is scoped to the construction and certificate relative to the reviewed
packets, not a claim of global priority for those general techniques.

FILES

  report.tex / report.pdf   Complete report, theorem statements, and proofs.
  code/packet_packing.py    Exact Fraction-based labeling and packet prototype.
  code/verify_packing.py    Exhaustive and seeded tests, plus negative controls.
  code/schedule_analysis.py Exact integer schedule and numerical certificates.
  code/verify_schedule.py  Exact finite schedule checks and negative controls.
  code/run_checks.py        Runs normal and optimized Python verification.
  code/verify_manifest.py   Checks SHA-256 integrity of the supplied package.
  results/                 Recorded verification and parameter results.
  provenance/              Reviewed snapshots, comparison, and source anchors.
  provenance/upstream/     Two unchanged source appendices and scope document.
  provenance/APACHE-2.0.txt License for the redistributed OpenAI source files.
  Makefile                 Convenience targets for checks and PDF compilation.
  SHA256SUMS.txt            Fingerprints of the final deliverable files.

REPRODUCTION

Use Python 3.11 or later. The new code uses only the standard library.
From this directory:

  python3 code/verify_manifest.py
  python3 code/run_checks.py
  python3 code/schedule_analysis.py --help

On Windows, replace python3 by the appropriate Python executable, such as py.
No downloaded research script is executed by these checks.

Build the PDF with a standard TeX Live or MiKTeX installation containing
latexmk and the packages listed in report.tex:

  latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

The TeX file is self-contained: it requires no external figure or bibliography
files. The PDF and source can therefore also be used outside this directory.

VALIDATION

Both normal and python -O packing runs pass 1,332 labelings. Each checks
9,136 candidate potentials, 5,374 trace values, 13,888 padded slots, and
562 real slots. Thirteen negative controls are rejected. Both schedule runs
pass 6,369 explicit checks, including 1,112 guard-boundary cases and two
negative controls. Check gates use explicit exceptions, not removable assert
statements. JSON outputs record the Python optimization flag.

These are finite implementation checks. The report's proofs establish the
all-size mathematical claims. The schedule analyzer manipulates lambda, not
an actual network of size 2^lambda. Its huge-parameter tests are not SAT
benchmarks or practical performance predictions.

SCOPE AND PROVENANCE

OpenAI source snapshot:
  7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a
ProveIt review snapshot:
  aa6933442eb936962de79ba6d321cd0391c450bd
Relevant intake commits:
  a505bd768bce347c70e923586c5f72ad3085bf44
  64b3202ee84fc4d71fe69c34d2110c93b7da95cd
  8afdbbea48d67b8d252a99e8926f3eca9649eae3

All seven proposal archives and both incoming PDFs were downloaded at the
frozen ProveIt snapshot and verified against their Git blob hashes. Their
SHA-256 fingerprints and report members are in provenance/reviewed_sources.json.

A final check also reviewed placement 2b925d8800cd, upstream-source vendoring
3e096089911f, and the topic-summary commit 45233238aebf. The same packets now
reside under Computability/SubexponentialSAT/Research/. Their placed report
sources were checked against the archive bytes; no eighth proposal appeared.
The placement review is recorded in provenance/placement_review.json.

The result refines the source contraction framework. This package does not
contain a complete SAT solver, an upstream Lean rebuild, or a new Lean/Rocq
formalization. It is not an independent formal certification of the entire
ETH claim. Independent mathematical and code cross-reviews found no remaining
issue in the new packing lemma, schedule, or coefficient calculation.

No GitHub repository was modified by preparing this package.
