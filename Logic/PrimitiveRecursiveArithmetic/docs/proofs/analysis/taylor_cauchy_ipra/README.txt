TAYLOR'S THEOREM AND CAUCHY'S INTEGRAL FORMULA IN iPRA
===================================================
Prepared for Vladimir Reshetnikov, November 15, 2026.

Start with report.pdf; its complete LaTeX source is report.tex.

MATHEMATICAL RESULTS
--------------------

1. Taylor's exact integral remainder, the factorial error bound, and a
   quantitative Peano remainder. A single weighted derivative jet cancels
   to its final derivative. The paper supplies the fully rational finite
   certificate, including the rounding error proportional to the mesh size.

2. Cauchy's ordinary circle formula at any rational interior point with a
   supplied positive margin, extended to any fixed PR-named interior point
   with such a margin. Rational quarter-circle parametrizations and a
   finite homotopy grid prove the formula from a uniform first derivative
   certificate. Continuity of the supplied derivative is not assumed.

3. All Cauchy derivative formulas, Cauchy's derivative bounds, and complex
   Taylor expansion with a primitive recursive geometric-tail cutoff.
   These are derived from finite inverse-power/geometric identities.

FOUNDATIONAL SCOPE
------------------

The results are first-order iPRA theorem schemas for fixed primitive
recursive rational approximation procedures and explicit bounds/moduli.
They are not single first-order assertions quantifying over all classical
real functions. Uniform Taylor order requires a jointly PR derivative
table. There is no universal PR evaluator for arbitrary PR program codes.

The human mathematical arguments are complete for the stated effective
hypotheses. All induction invariants used in the arithmetic reconstruction
are finite rational equalities/inequalities or PR Boolean folds.

FORMALIZATION STATUS
--------------------

lean/FiniteCore.lean supplies actual finite algebra proof scripts.
lean/NativeBridge.lean supplies the existing repository translation step.
lean/FORMALIZATION_PLAN.txt specifies the remaining implementation.

These Lean files are UNCOMPILED. No Lean executable was available in the
producing environment. They contain no proof holes or new analytic axioms,
but successful elaboration and kernel checking have not been established.
The complete coded rational library and Taylor/Cauchy Prf PRAAx derivations
are not yet implemented. The native bridge alone does not prove them.

The inspected ProveIt revision is:
  876ef598f674759da5f084dc34f63ca4e182aae0
It specifies Lean v4.32.0 and Mathlib v4.32.0.

FILES
-----

report.tex / report.pdf       Complete mathematical paper.
lean/FiniteCore.lean          Finite algebra reference scripts.
lean/NativeBridge.lean        Actual iPRA-to-native derivation transport.
lean/FORMALIZATION_PLAN.txt   APIs, layers, induction audit and missing work.
lean/README.txt              Build instructions and status.
code/validate_exact.py        Standard-library exact Fraction validation.
code/validation.json         Deterministic exact results.
code/README.txt              Coverage and circle certificate derivation.
provenance/sources.json       Pinned source inventory and hashes.
provenance/validation.json    Build, verification and status record.
SHA256SUMS                   Checksums of archive contents.

REPRODUCING THE CHECKS
---------------------

From this directory, with Python 3.10 or later:

  python3 code/validate_exact.py --output code/validation.json

Only the Python standard library is required. Every asserted comparison
uses exact rational arithmetic; decimal displays are informational.
Finite examples are not a formal proof of the general theorems.

To compile the report in a normal TeX Live installation:

  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

The report uses standard LaTeX packages, Latin Modern fonts and TikZ.
See lean/README.txt for the separate Lean compilation commands.
