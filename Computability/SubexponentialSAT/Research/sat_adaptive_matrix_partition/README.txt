ADAPTIVE PARTITIONS FOR SUBEXPONENTIAL SAT
Prepared for Vladimir Reshetnikov, October 26, 2026 (Pacific time).

RESULT
This packet reviews 20 refinement proposals (15 filed and 5 incoming) at
ProveIt commit fd0edd17e6a29117179b40a453c0def59165bd7c. It proves two
smaller explicit normalized contraction certificates, relative to the
reviewed exact algebraic interfaces:

  Polynomial space:
    old time coefficient 55.709478318910...
    new time coefficient 50.210434836331...
    safe eventual coefficient 50.22.

  Cached, subexponential space:
    old fastest time / its space: 35.354588058401 / 34.274803005023
    new time / space:             34.325282797285 / 34.024178007491
    safe eventual coefficients:   34.33 / 34.03.

All coefficients multiply s/sqrt(log2 s) in a base-two exponent, where s
is the normalized Boolean wire budget. The general root degree is at
most ceil(s^(9/10)); see the full theorem for entry-cost and ring premises.

The new ideas are exact second-moment bounds for partitions chosen from
actual mode-list sizes. The cached branch uses a partition into three
triples and binary table construction. The streamed branch chooses an
optimal balanced sixteen-group separator tree. Its implemented subset
dynamic program uses 14,827 states and 462,465 splits.

SCOPE
The explicit upper-bound functions improve asymptotically. The SAT
logarithmic order n loglog n/sqrt(log n) remains unchanged, and the
stronger n/log n-type conditional targets remain unproved. Coefficients
per wire are not automatically coefficients per SAT variable.

The existing lower-memory cached point and stronger low-degree branches
remain useful. This packet does not claim to dominate every time-space
tradeoff, prove the upstream ETH conclusion independently, implement a
complete SAT solver, or provide a new Lean/Rocq proof. No SAT speedup was
measured. The fast matrix backend is theoretical; local matrix-shaped
tests use ordinary exact scalar arithmetic.

CONTENTS
  report.tex, adaptive_triangle.tex, adaptive_streaming.tex
      Complete LaTeX report and mathematical proofs.
  report.pdf
      Compiled report.
  code/
      Exact covariance/PSD and rational-constant verifiers, group
      contraction prototype, optimal tree selector, independent checks.
  results/
      Reproducible finite results and validation summary.
  review/
      Independent proof reviews and a scoped incidence-support example.
  provenance/
      All twenty packet identities, source hashes, pinned recent commits.
  MANIFEST.sha256
      Bundle file checksums (not a signature or proof of authorship).

REPRODUCE
  python3 code/verify_all.py
  make pdf

Python 3.10 or newer and its standard library suffice for the code.
The report builds with a normal pdfLaTeX installation and the packages
declared in report.tex. No network access is needed for the local checks.
The verification scripts explicitly raise on failed checks even under
optimized Python. Finite checks support, but do not replace, the uniform
mathematical proofs or validate imported results in their entirety.

SOURCE CREDIT
The report cites the unchanged OpenAI preprint, the earlier ProveIt
research packets and archives, and the established matrix multiplication
result. New priority is claimed only relative to the reviewed corpus;
no exhaustive literature priority investigation was undertaken.

CLOSING REPOSITORY CHECK
Commit 450252e9d86c155f188b485629b9755c5c665371 placed the same five
incoming archives under Research/. All 230 filed members were independently
checked against their Git blobs and are byte-identical. It changes canonical
locations but not the reviewed mathematical baseline. The closing check and
new directory mapping are in provenance/closing_placement_check.json.
