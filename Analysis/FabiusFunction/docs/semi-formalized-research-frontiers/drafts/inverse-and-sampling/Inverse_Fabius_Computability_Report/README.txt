COMPUTABILITY OF THE INVERSE FABIUS FUNCTION
=============================================

Contents
--------
inverse_fabius_computability.tex
    Complete 2743-line LaTeX source of the report.  Its latest synchronized
    update adds the logarithmic reciprocal-modulus crosswalk described below.

inverse_fabius_computability.pdf
    Current 39-page A4 report, produced from the 2743-line source in exactly
    three serial pdfLaTeX passes.

inverse_fabius_computability_experiments.py
    Exact-rational Python supplement.  It uses only the Python standard
    library and documents the finite Thue--Morse spline, endpoint-mass bounds,
    interval-mass check, and a certified comparison/bisection demonstration.

numerical_output.txt
    Captured output from the Python supplement with its default arguments.

SHA256SUMS.txt
    SHA-256 digests for the current built package revision.  All five entries
    verify against the live payloads.

Repository snapshot
-------------------
The documentation audit and all repository-relative novelty statements are
pinned to ProveIt commit:

    40fdea4cc0a728189f357389e3f114a2cb00e561

Post-publication Lean crosswalk
-------------------------------
The structural inverse-modulus portion of the report is crosswalked to:

    Analysis/FabiusFunction/Lean/FabiusFunction/InverseModulus.lean

That module covers global fixed-length Fabius increments, reflection and
one-sided shape, the least endpoint increment, constrained forward
superadditivity, local and global inverse-gap bounds, global inverse
subadditivity, attained exact unit-interval and totalized moduli, and the
exact effective-injectivity threshold.

The effective-uniform-continuity portion is exhaustively crosswalked to all
fourteen public declarations (two definitions and twelve theorems) in:

    Analysis/FabiusFunction/Lean/FabiusFunction/FabiusInverseEffectiveContinuity.lean

That module proves a one-term inverse-dyadic recurrence bound stronger than
the report's elementary box estimate, the exact numerical Delta_r endpoint
inequality, strict and closed versions of both the Delta and stronger
factorial-denominator inverse moduli, primitive recursiveness of both explicit
denominator sequences, and EffectivelyUniformContinuous for the totalized
inverse with the simple r=n factorial-denominator witness.

The logarithmic refinement is exhaustively crosswalked to all eighteen public
declarations (three definitions and fifteen theorems) in:

    Analysis/FabiusFunction/Lean/FabiusFunction/FabiusInverseLogarithmicModulus.lean

That module defines the primitive-recursive least order r(n), proves its
binary-length and least-order characterizations and r(n) <= n, composes both
the Delta and stronger factorial denominators with r(n), proves both composed
denominators primitive recursive, supplies strict and closed-input reciprocal
moduli, and packages EffectivelyUniformContinuous with either witness.  The
Delta package is the exact d(n), d(0)=1 construction stated in the report.

The random-series box-event proof itself is not formalized: Lean proves its
numerical conclusion through the stronger recurrence route.  The exact
ceiling denominator d_* and its qualified fixed-target minimality, tolerant
bisection, sequential computability, the combined computable-real-function
theorem, and input-bit asymptotics remain open Lean work.  The report retains
their complete human proofs and imported-source qualifications.  The scope
correction for d_* remains in force: it is
denominator-minimal for the fixed dyadic proxy 2^{-r(n)}, not for the weaker
target tolerance 1/n.

Render and ledger status
------------------------
The 2743-line source and 39-page A4 PDF are synchronized after exactly three
serial pdfLaTeX passes.  The final log has no TeX errors, unresolved references,
rerun request, or overfull box.  All fonts are embedded/subset, Libertinus is
present, no Type 3 font is used, representative pages were inspected, and all
five active checksum entries verify.

Reproduce the numerical supplement
----------------------------------
Run:

    python inverse_fabius_computability_experiments.py

No numerical experiment is used as a premise of the computability proof.
