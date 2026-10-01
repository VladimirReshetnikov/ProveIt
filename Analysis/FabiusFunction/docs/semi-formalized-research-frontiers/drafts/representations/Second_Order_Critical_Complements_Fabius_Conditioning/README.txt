Second Order Critical Complements in Fabius Conditioning
Research note prepared for Vladimir Reshetnikov, 1 October 2026

Contents
  Second_Order_Fabius_Crossover.tex  Editable mathematical source
  Second_Order_Fabius_Crossover.pdf  Rendered research note
  check_gamma.py                    High-precision formula diagnostics
  gamma_checks.csv                  Recorded diagnostic output
  gamma_checks.log                  Recorded standard output of check_gamma.py
  requirements.txt                  Pinned Python requirement (mpmath 1.3.0)
  Makefile                          Build and check targets (see below)
  README.txt                        This file

Ordinary TeX build
  Requires a TeX distribution with libertinus-type1 and the standard
  packages named in the preamble. Run pdflatex three times.
  Mathematics intentionally uses Computer Modern, text uses Libertinus.
  (make all runs these three passes in place and overwrites the filed
  PDF; build on a copy.)

Diagnostics
  Python 3 with mpmath. Run python check_gamma.py.
  The calculations use 70 decimal digits but are not interval-certified.
  (On the ProveIt machine use py, or uv run --no-project --with
  mpmath==1.3.0 python, rather than bare python; make check calls bare
  python.) Since the editorial pass below the program writes
  rerun/gamma_checks.csv beside itself unless --output-dir is given; as
  delivered it overwrote gamma_checks.csv in the current directory, so
  regenerate the recorded file with --output-dir . only on a copy.

Status
  Manuscript-level proofs; not Lean verified or independently peer reviewed.
  The note proves an explicit critical-window refinement and a strict
  comparison of two observation masks. It does not claim worldwide
  novelty, a famous-conjecture resolution, or all mesoscopic regimes.
  No remote repository files were changed.

Source snapshot
  https://github.com/VladimirReshetnikov/ProveIt
  Commit 63a7a325109ba611a1816b61dfd0eb072b896a7a
  Exact manuscript links are in the bibliography.

Editorial amendments (ProveIt, 2026-10-01)
------------------------------------------
Made in the editorial pass after batch 71 of docs/incoming/ (see
docs/incoming/README.md); every change to the source is marked
"% ed. (2026-10-01)", every change to the program "ed. (2026-10-01)". The
mathematical text is unchanged. The pdfauthor entry and byline ("Research
note prepared with OpenAI for Vladimir Reshetnikov", "Developed with
OpenAI") are kept as delivered.

- Second_Order_Fabius_Crossover.tex: an unnumbered environment ednote
  ("Editorial note (ProveIt, 2026-10-01)") is defined after remark (the
  theorem counter is unchanged). Two notes:
  - end of Section 1: for q = 1/2 the probability representation cited
    from Arias de Reyna is machine-checked as
    Fabius.ProbabilityRepresentation.weightedSumCDF_eq_fabiusReal and
    Fabius.ProbabilityRepresentation.geometricUniformDensity_one_half_eq_rvachevUp
    (Analysis/FabiusFunction/Lean/FabiusFunction/ProbabilityRepresentation.lean),
    which the note does not cite; no result of the note is formalized. The
    two source articles are filed beside this package, and their
    questions answered here now carry reciprocal editorial notes;
  - end of Section 2: a dictionary. "early" and "late" name the hidden
    bulk coordinates, while both sources name the observed block: the
    early mask is the block {r+1, ..., n} observed in
    ../Critical_Complements_Fabius_Conditioning/ with r = m, the late mask
    the prefix of ../Critical_Complements_Sharp_Information_Loss/. rho is
    the latter's (which states its theorems for 1 <= rho < 1/q; any
    rho > 0 here); the former's is rho/q. H_0(1) = E exp(R_0) is the
    former's product K, and log H_0(1) is the latter's K_{q,rho,0}; at
    q = 1/2, rho = 1/2 it is 0.486134172..., reproduced to 30 digits. As
    c tends to 0, K_early(c) tends to log H_0(1) + 1, the constant of both
    fixed-complement theorems when only the tail is hidden, and the limit
    in (3.12) tends to -infinity, matching for fixed m >= 1 the divergent
    gap m log Lambda_n - log m! + K_{q,rho,0} - K_{q,rho,m} between those
    theorems (consistency checks outside the range of Theorem 3.1); at
    q = 1/2, rho = 1 the limit in (3.12) is -1.0279 for c = 1 and -20.44
    for c = 0.002. Only C(c) among the letters A, B, C, D, F, K_j, L, W
    means the same in the latter article; the former uses K for a product,
    C for rho q/(1-q) and c_n for eps_n, whereas c_n = m/log n here.
- Second_Order_Fabius_Crossover.pdf: rebuilt from the amended source with
  three pdflatex passes (MiKTeX 26.2, pdfTeX 1.40.29): 10 A4 pages (9 as
  delivered), 563,685 bytes; all 16 fonts embedded, none Type 3; the final
  log has no error, overfull or underfull box, undefined or multiply
  defined reference, duplicate destination, or rerun request. The three
  pages carrying the notes were rendered and inspected.
- check_gamma.py: new option --output-dir (default rerun/ beside the
  program), receiving gamma_checks.csv, which is written with LF line
  endings on every platform (CRLF before, the csv module's default); the
  last line of its output names the file written. A rerun of the amended
  program on a copy (2026-10-01, uv run --no-project --with mpmath==1.3.0
  python check_gamma.py, Python 3.13.5, about 4 seconds) reproduced the
  recorded gamma_checks.csv byte for byte, and its standard output equals
  gamma_checks.log after CRLF-to-LF conversion except that last line;
  with --output-dir . the output equals gamma_checks.log entirely.
- Makefile: kept as delivered (see "Ordinary TeX build" and
  "Diagnostics" above).
- README.txt: the four unlisted files under "Contents", the parentheses
  under "Ordinary TeX build" and "Diagnostics", and this section.

A second editorial pass the same day, after batch 72 of docs/incoming/,
added:
- Second_Order_Fabius_Crossover.tex: a third note, after the proof of
  Corollary 3.3 (cor:comparison): the strict order of the two masks holds at
  every finite parameter, not only eventually. The later note
  ../Strict_Fabius_Conditioning_Order/ (batch 72, unreviewed) proves
  O^late_{n,m} < O^early_{n,m} for every q in (0,1), rho > 0, n >= 2 and
  1 <= m < n (its Corollary 4.2), in the same model with the same masks and
  superscripts; the nonstrict order for every f-divergence is Corollary 4.1
  of ../Exact_Fixed_Conditioning_Order/, and for q = 1/M
  ../Exact_Fabius_Mask_Order/ realizes it by one residue map valid for every
  total-sum reweighting. The limit (3.12) is not affected. For
  delta n <= m <= (1 - delta) n, Corollary 5.2 of
  ../Proportional_Fabius_Mask_Edgeworth/ gives
  O^early - O^late = phi(c) c D(q, rho)/m + O(n^{-3/2}), with
  D(q, rho) = sum_{r>=1} a_r^2 e^{a_r}/(e^{a_r} - 1)^2. These notes bear on
  the third question of Section 7 only in part.
- Second_Order_Fabius_Crossover.pdf: rebuilt again (three pdflatex passes,
  MiKTeX 26.2, pdfTeX 1.40.29): 10 A4 pages, as before, 567,183 bytes;
  all 16 fonts embedded, none Type 3; the final log has no error, overfull
  or underfull box, undefined or multiply defined reference, duplicate
  destination, or rerun request. The page carrying the note was rendered and
  inspected.
- README.txt: this paragraph.
