BEYOND DIRICHLET GRH
Certified graph optima and quantitative local transfers
Prepared for Vladimir Reshetnikov -- 26 November 2026
=====================================================

START HERE
----------
report.pdf is the complete report. report.tex and sections/ contain its
complete editable LaTeX source. The ZIP also supplies exact certificate
programs, their results, predecessor replay logs, source excerpts, and
provenance. Nothing here is a new Lean formalization.

MAIN FINDINGS
-------------
1. Seven new exact signed-graph optima, relative to the reviewed incoming
   corpus. For C_n(1,2), n=34,36,38,42,44,46, the minimum radius is
       2 sqrt(cos(pi/n)^2 + cos(2*pi/n)^2).
   Exactly two labeled switching classes minimize it: alternating triangle
   signs with Hamilton-cycle sign product -1.

   For n=50 the minimum lies strictly between 2.811568906156 and
   2.811568906157. The exact value is the square root of the largest real
   root of the supplied degree-25 integer polynomial. All minimizers have
   Hamilton-cycle sign product +1 and triangle word a rotation of
       (--+-++-+) repeated six times, followed by (-+),
   or its global negative. There are 100 labeled minimizing switching
   classes. Every other class has radius at least 7029/2500=2.8116.
   These claims use exhaustive rational/integer certificates, not a
   floating-point optimization or a random search.

2. An exact local coefficient theorem. For q=p^f, f>=1, let
       L(pX+X^q)=p L(X), L(X)=X+O(X^2), N=v_p(n), n>0.
   For 1<=j<=p^N, the coefficient of X^(n+j(q-1)) in L(X)^n has
       v_p = N-v_p(j)-j.
   This gives the exact first nonintegral coefficient and sharpens the
   predecessor's integrality window. The proof is in the report.

3. A repaired coefficient-module computation. The published author erratum
   identifies a defect in the old experimental baseline. The supplied
   programs use only genuine trace-kernel generators, and two distinct
   exact elimination methods agree. Examples include s0(12)=30 at p=2,
   even though an individual coefficient reaches the desired valuation
   already at depth 18. This difference is essential.

4. Revalidated predecessor results. The report checks the infinite-family
   optimum for every C_(8m)(1,2), m>=4, and strict natural-versus-upper
   density gaps for geometric-progression-free sets. These are credited
   to the incoming reports, not presented as new work from this analysis.

5. Arithmetic transfer limits. The covolume/rank/divisibility mechanism
   suggests a concrete nonabelian cubic-field benchmark, but a new
   Frobenius-sensitive arithmetic inequality is still needed. No new
   Artin-GRH, BSD, Vandiver, or general algebraic K-group-vanishing theorem
   is claimed. The congruence-length appendix gives a useful finite
   diagnostic and explains the coefficient-ring quantifier issue.

Novelty is relative to the inspected 46-archive incoming corpus. The
report does not assert worldwide publication priority.

REPRODUCING THE MATHEMATICAL CHECKS
---------------------------------
Use Python 3.10 or newer with assertions enabled; do not use python -O.
The checks were run with Python 3.12.14. Only the independent integer HNF
check needs SymPy (tested with 1.14.0). The plot uses Matplotlib (3.10.8).
All other mathematical checks use the standard library. The optional
requirements.txt records these two dependency versions.

From this directory, run:

    python3 run_checks.py

This runs the new checks and the selected predecessor checks, saving logs
and a manifest under rerun_logs/. It stops on the first nonzero exit.
Individual certificate files next to the programs are regenerated.
The graph searches can take several minutes on a normal computer.

    python3 run_checks.py --new-only

omits predecessor replays. To run only standard-library checks, add
--skip-hnf; the missing HNF verification will be explicitly recorded.

Individual commands (run within the indicated directory):

checks/graphs/
    python3 verify_even_extensions.py

checks/graphs/n50/
    python3 certify_n50.py
    python3 verify_n50_independent.py

checks/local/
    python3 verify_log_window.py
    python3 coefficient_depth.py --p 2 --cutoff 48 --out depth_p2_48.json
    python3 coefficient_depth.py --p 3 --cutoff 100 --out depth_p3_100.json
    python3 verify_depth_hnf.py

checks/congruence/
    python3 check_congruence_lengths.py

checks/predecessors/
    python3 verify_graph.py
    python3 verify_by_permutations.py
    python3 verify_small_cycles.py
    python3 check_integer_gap.py
    python3 check_integer_prefix.py

A null depth-table entry means only that the finite cutoff was exceeded.
Exact certificates support the stated finite claims; the general local
coefficient theorem is proved in the manuscript, not established by
testing finitely many examples. The two n=50 algorithms independently
reconstruct all local path survivors. Cyclic completion and the full
holonomy exclusions are done by the first verifier; root isolation is
done by the second.

BUILDING THE PDF AND FIGURE
--------------------------
Use a standard TeX Live installation with pdfLaTeX, latexmk, Latin Modern,
and the usual LaTeX packages listed in report.tex:

    latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

Alternatively run pdflatex on report.tex repeatedly until references are
stable (normally three passes). The included figure is already a PDF;
Matplotlib is unnecessary for building the manuscript.

To regenerate the figure and its CSV:

    python3 figures/make_figure.py

The graph is illustrative. Decimal plotting never enters a certificate.

SOURCE SCOPE AND AUDIT
----------------------
grh-lean:
    https://github.com/lsernau/grh-lean
    72fead102f663d5c7a407964a13dc0cf9d977207
ProveIt incoming:
    https://github.com/VladimirReshetnikov/ProveIt/tree/main/docs/incoming
    5cc267af75a635199ac5d93a7d49cbce521daefc

The upstream endpoint is RH and GRH for Dirichlet L-functions. All 46
GRH-related incoming archives at the pinned snapshot were inventoried;
selected mathematical arguments were independently reviewed and replayed.
The source audit is lexical plus an import-graph traversal. It is not a
local Lean kernel build or a repeat of the upstream independent checkers.

Only selected upstream files are included in sources/grh-lean/, copied
verbatim with the original license and notices. They are evidence excerpts,
not a complete buildable upstream checkout. The predecessor TeX excerpts
likewise need their original parent projects; the deliverable manuscript
at the package root is complete.

To repeat the static audit, obtain the full upstream checkout at the
pinned revision and run:

    python3 provenance/audit_sources.py /path/to/full/grh-lean --output audit.json

The archive inventories retain original extraction-relative paths. Those
paths describe provenance; they are not all included in this ZIP.
SHA256SUMS lists every delivered file except itself. It verifies the
delivered snapshot; rerunning programs may regenerate some output files.

No repositories were changed or published as part of this work.
