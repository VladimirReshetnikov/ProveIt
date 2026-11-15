LOGARITHMIC-INTEGRAL STRENGTHENINGS OF THE PNT IN iPRA
Prepared for Vladimir Reshetnikov, November 15, 2026

START HERE
==========
pnt_li_ipra.pdf is the complete human-readable article.
pnt_li_ipra.tex and tex/*.tex are its complete LaTeX sources.

RESULT AND SCOPE
===============
The article proves an explicit nonoptimal stretched-exponential bound,
  |pi(n) - Li_2(n)| <= 64 n/log(n) exp(-2^-26 (log n)^(1/10))
above the stated primitive recursive threshold. Here Li_2(n) is the
offset logarithmic integral from 2 to n.

It also proves every inverse-logarithmic error order, the full factorial
asymptotic expansion with explicit remainder constants and thresholds,
eventual first-omitted-term inequalities, and a bounded search procedure
for finding a prime in a specified relative interval.

The core first-order statement uses only natural numbers and rational
arithmetic. With b(n) the binary length, A(n,v) the exact rational algorithm
in code/arithmetic.py, and
  N(m) = 2^(2^241 (m+7)^10),
the conclusion is
  n >= N(m)  ==>  |pi(n)-A(n,v)| <= n/(2^m b(n)) + 2^-v.
The article displays the corresponding denominator-cleared integer matrix.

The mathematical proof is developed in full with explicit finite analytic
cutoffs, apartness bounds, rational contours, and quantifier-free induction
invariants. It is a human proof in the stated constructive interpretation.

This package does NOT prove the stronger classical square-root-logarithm
rate, Vinogradov--Korobov's rate, or an unconditional RH-sized error.
The 1/10 exponent is an established nonoptimal analytic exponent, not a
claimed new classical exponent. Numerical constants are deliberately coarse.

FORMALIZATION STATUS
====================
The lean/ directory contains UNCOMPILED outlines and interfaces, not a
completed Lean PNT proof. No Lean executable was available in the construction
workspace. Small algebraic proof candidates have not been kernel checked here.
The source introduces no new axiom named as though PNT were already proved.

The final completion target is an actual term
  Prf PRAAx [] mainFormula
in ProveIt's embedded intuitionistic theory, followed if desired by its
proved native-calculus translation. An ambient Mathlib theorem does not
automatically establish this endpoint. lean/STATUS.txt and lean/ROADMAP.txt
list the outstanding obligations.

CONTENTS
========
pnt_li_ipra.pdf                 Compiled article.
pnt_li_ipra.tex                 Main LaTeX source and bibliography.
tex/foundations.tex            Arithmetic interpretation, algorithms, target.
tex/analytic.tex               Euler products, apartness, Perron, dyadic estimate.
tex/theta_bridge.tex           Prime-power correction and simple theta modulus.
tex/transfer.tex               Li transfer, expansion, interval consequences.
tex/finite_contour.tex         Exact finite contour and precision accounting.
tex/formalization.tex          Lean route, scope, provenance, verification status.
code/arithmetic.py             Exact rational executable specifications.
code/check_arithmetic.py       Finite implementation and numerical checks.
code/build_pdf.sh              Rebuilds the PDF, with a private TeX fallback.
lean/ArithmeticTarget.lean     Exact target and finite algorithm definitions.
lean/FiniteAbel.lean           Finite algebraic proof candidate.
lean/NativeBridge.lean         Existing-library object proof transport interface.
lean/STATUS.txt                Formalization status.
lean/ROADMAP.txt               Remaining formalization proof obligations.
evidence/proveit_sources.json  Exact repository revision, paths, and blob hashes.
evidence/AUDIT.txt             Repository and prior-draft scope audit.
evidence/FINAL_MATHEMATICAL_AUDIT.txt
                              Independent mathematical review, not kernel checking.
verification.json             Results and explicit limitations of executable checks.
manifest.sha256               Checksums of the delivered package files.

REPRODUCTION
============
With an ordinary TeX Live installation, from this directory run:
  pdflatex -interaction=nonstopmode -halt-on-error pnt_li_ipra.tex
  pdflatex -interaction=nonstopmode -halt-on-error pnt_li_ipra.tex

Or use:
  bash code/build_pdf.sh

The latter script first uses a normal initialized TeX installation. Its
fallback creates private runtime data for an installed Debian TeX tree
without generated indexes; it does not modify the system TeX tree.

Finite checks:
  python3 code/check_arithmetic.py

They use mpmath for independent 100-digit numerical comparisons. The exact
arithmetic specification itself requires only Python's standard library.

VALIDATION AND ITS LIMITS
========================
50 signed-rational finite Abel cases were checked exactly; 261 equivalences
between the rational target and its integer matrix were checked exactly.
30 logarithm enclosures and 5 Li enclosures were compared with independent
100-digit values. Representative dyadic prefactor inequalities were checked.
The manuscript constants and finite error estimates were independently
reviewed, and the PDF was rendered for visual inspection.

No finite test purports to prove a universal PNT statement, a zero-free
region, or iPRA provability. The large threshold is never materialized by
the checks. Small-input tests with a false threshold antecedent are not
reported as evidence for the main theorem.

REPOSITORY BASELINE
===================
VladimirReshetnikov/ProveIt at
  b5a3ad037723c44d69a3d5b28a950c554327a989
Relevant path:
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
The inspected repository declares Lean and Mathlib v4.32.0. This package
does not modify that repository and does not claim to have rerun its build.
All source URLs are retained in the article and evidence manifest.
