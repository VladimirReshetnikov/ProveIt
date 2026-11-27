TWO RESULTS FROM THE PROVEIT DIRICHLET GRH PROJECT
27 November 2026

Read filters/cluster_filters.pdf for the answer to the article's cluster-splitting
question. Read cayley/cayley_periods.pdf for the exact least periods of oriented
Cayley walks over a fixed finite abelian group. The papers can be read independently.

Filters
  For N positive frequencies of mean kappa, a positive cancelling measure needs
  diameter at least N*pi/kappa. Theorem 1 gives the equality criterion.
  Theorem 2 identifies the signed-cluster correction, its coefficient and the
  order in every asymmetric direction. The result applies to averaging terms
  from zeros on a common vertical line. The symbolic checker verifies the
  coefficient and a tenth-order example; a separate numerical solution at
  90-digit working precision illustrates the sixth-order law.

Cayley periods
  For a host of order N and exponent n, precisely the periods 2*pi/(a*sqrt(f))
  occur as least positive periods, with -f a negative fundamental discriminant,
  f dividing n and a*f dividing N. The paper gives the sharp outdegree, all
  fastest labelled symbols, a duality for the minimizers, and the mixing and
  transfer cases among fastest walks. The checker exhausts 334,780 connection
  sets on 24 groups. The distinct nonempty periodic connection sets number 8,820.

Build and verification
  In cayley/, run pdflatex cayley_periods.tex twice. In filters/, run
  pdflatex cluster_filters.tex twice. A standard TeX Live installation suffices.
  From the root of this archive the following commands reproduce the checks.
    python3 cayley/verify_graphs.py > /tmp/graph-check.json
    diff -u cayley/exhaustion.json /tmp/graph-check.json
    python3 filters/check_filter.py > /tmp/filter-check.txt
    diff -u filters/filter_checks.txt /tmp/filter-check.txt
  The graph program uses the Python standard library. The filter program uses
  SymPy and mpmath. All four commands were checked on the delivered outputs.
  SHA256SUMS contains hashes of the paper sources, PDFs, programs and receipts.

Source snapshot
  VladimirReshetnikov/ProveIt at 00cadb961bbe77c74e5d082c4948f8884d58a970
  https://github.com/VladimirReshetnikov/ProveIt/tree/00cadb961bbe77c74e5d082c4948f8884d58a970/Analysis/GeneralizedRiemannHypothesis
  Article/sections/fil.tex supplies the local analytic optimizer and poses the
  asymmetric splitting question. Article/sections/li.tex and the additional
  Research/dirichlet_li_recovery/heat.tex supply the circle inverse problem
  and the character projection. The latter already proves the cyclic minimum
  discrepancy and its equality cases. The two papers identify the prior results
  they use. Their main mathematical claims are unconditional. The interpretation
  for general Dirichlet zero clusters uses the project's critical-line input.
  These are human-readable proofs with computational checks. No new Lean proof
  or independent upstream rebuild is included. Global priority remains open.
