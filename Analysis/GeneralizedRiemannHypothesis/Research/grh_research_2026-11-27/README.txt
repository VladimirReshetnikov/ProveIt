RESEARCH SUPPLEMENT TO THE PROVEIT GRH TRANSFER PROGRAM
27 November 2026

READ FIRST

This archive contains two research papers with complete mathematical proofs,
editable LaTeX sources, exact-arithmetic verification programs, explicit
polynomial witnesses, source provenance, and internal review notes.

The results extend the pinned repository's local methods. They do not use RH
or GRH as hypotheses. They are proposed new research results, not a claimed
proof of a further prominent named conjecture. Publication priority has not
been established by an exhaustive literature review. The new proofs have
not been formalized in Lean or externally peer reviewed.

MAIN PAPERS

papers/sparse_roots.pdf (14 pages)
  Finite residue classification of sparse polynomial roots:
  Exact local bounds, a sharp odd-prime staircase, and binary disk profiles.

  For a fixed prime p, term count t and positive minimum depth, only finitely
  many residue digits of the exponents determine the entire optimal local
  root-count profile. A finite minimum-determinant-basis calculation gives
  the exact answer, including transition endpoints and rational witnesses.
  Enumerating residue multisets computes the sharp geometric local bound.

  For odd primes and p+2 <= t <= 2p-1, the sharp count in
      v_p(X-1) > 1/(p-1)
  is p^2 + floor((t-p-2)/2). At p=2 the five-, six- and seven-term
  cases have exact profiles with thresholds 4/3 and 3/2. The main .tex
  file inputs sharp_range.tex and binary_profile.tex in the same folder.

papers/torsion_phase_transition.pdf (7 pages)
  A polynomial growth exponent for finite families in torsion specialization.

  For n polynomial tests, total valuation budget B, and fixed tolerance
  delta>0, the worst necessary torsion-order exponent satisfies
      c B^n <= H_n(B,delta) <= C B^n (log B)^2 log log B.
  In particular log H_n(B,delta)/log B -> n. This answers the growth-exponent
  aspect of the pinned article's Question cost:q:cardinality(b). The actual
  torsion order is p^H, not H. A leading constant and the joint limit
  delta -> 0 remain open.

REPRODUCE THE CHECKS

Requires Python 3.10 or later, standard library only. No internet, third-party
Python dependencies, Sage, Mathematica, Lean, or numerical p-adic library is
needed for the included checks. From this archive's root run:

    python3 code/run_checks.py

This regenerates the finite result files and results/reproduction_summary.json.
It checks the general local solver against full original binomial matrices;
tests the residue-algebra staircase independently; verifies polynomial
expansions, Newton polygons and simple-root certificates; and checks finite
torsion constructions. The asymptotic and arbitrary-parameter results rest
on the written proofs, not on extrapolation from these checks.

REBUILD THE PDFS

Requires a standard TeX Live installation with pdflatex, latexmk, and the
packages listed in the two preambles (amsmath, amsthm, mathtools, lmodern,
geometry, booktabs, longtable, microtype, xcolor, enumitem, fancyhdr, hyperref).

    make papers

Or, in the papers directory:

    latexmk -pdf -interaction=nonstopmode -halt-on-error sparse_roots.tex
    latexmk -pdf -interaction=nonstopmode -halt-on-error torsion_phase_transition.tex

The bibliographies are embedded in the .tex files; no BibTeX database is needed.
No repository checkout is required to compile the papers.

USE THE EXACT ROOT-COUNT SOLVER

Prescribed support, open exponential disk:

    python3 code/sparse_disk.py --prime 5 --support 0,1,5,6,10,15,20,25,30

Whole profile in the exponential region:

    python3 code/sparse_disk.py --prime 5 --support 0,1,5,6,10,15,20,25,30 --profile

Closed disk of any positive rational depth:

    python3 code/sparse_disk.py --prime 2 --support 0,1,2,4 --depth 1/4

Sharp bound over all six-term supports at p=2:

    python3 code/universal_bound.py --prime 2 --terms 6

The default depth string "open" means v_p(X-1)>1/(p-1). A numerical rational
depth r means the CLOSED disk v_p(X-1)>=r. --profile currently returns the
whole exponential-region profile; the all-depth finite-residue theorem is
proved in the paper, and arbitrary positive rational depths can be queried
individually. Decimal inputs should be avoided in favor of exact fractions.

The general dual-row witness can have zero coefficients on some allowed
exponents. Pair witness_coefficients with the returned support array. The
paper proves that exact support and Eisenstein irreducibility can always be
imposed for t>=2. The separate nine-term witness in sharp_range_witness.json
already includes explicit full support and an Eisenstein-at-2 certificate.

The universal enumeration is finite but can be very large. Its default
100,000-profile budget is checked before enumeration; --max-profiles changes
that limit. Exceeding it returns no partial or approximate answer. The budget
does not bound preprocessing, integer sizes, or the work per matrix.

SOURCE AND STATUS

Analyzed ProveIt snapshot:
    b82291c1f75389938c7464ef161907d7d5e75b2a
    https://github.com/VladimirReshetnikov/ProveIt/tree/b82291c1f75389938c7464ef161907d7d5e75b2a/Analysis/GeneralizedRiemannHypothesis

notes/SOURCE_ANALYSIS.txt records the specific source branches, inputs,
advances, and the unsuccessful attempt on the complete-bipartite Ehrhart
canonical-line question. notes/VERIFICATION.txt summarizes the checks.
The other notes record the independent internal readings and literature
scope. results/source_manifest.json pins source files by hash and URL.

Only the newly written papers, code, reports, and notes are packaged. The
third-party repository and literature PDFs are linked, not redistributed.
SHA256SUMS.txt checks the packaged files. Re-running checks or rebuilding
PDFs can change hashes; keep the original manifest as the release record.
