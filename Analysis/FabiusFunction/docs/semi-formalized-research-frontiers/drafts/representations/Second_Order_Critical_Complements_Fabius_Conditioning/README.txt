Second Order Critical Complements in Fabius Conditioning
Research note prepared for Vladimir Reshetnikov, 1 October 2026

Contents
  Second_Order_Fabius_Crossover.tex  Editable mathematical source
  Second_Order_Fabius_Crossover.pdf  Rendered research note
  check_gamma.py                    High-precision formula diagnostics
  gamma_checks.csv                  Recorded diagnostic output

Ordinary TeX build
  Requires a TeX distribution with libertinus-type1 and the standard
  packages named in the preamble. Run pdflatex three times.
  Mathematics intentionally uses Computer Modern, text uses Libertinus.

Diagnostics
  Python 3 with mpmath. Run python check_gamma.py.
  The calculations use 70 decimal digits but are not interval-certified.

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
