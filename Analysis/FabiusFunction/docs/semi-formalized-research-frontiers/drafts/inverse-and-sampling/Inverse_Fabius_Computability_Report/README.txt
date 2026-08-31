COMPUTABILITY OF THE INVERSE FABIUS FUNCTION
=============================================

Contents
--------
inverse_fabius_computability.tex
    Complete 2621-line LaTeX source of the report.  Its latest source update
    crosswalks the effective-continuity formalization described below.

inverse_fabius_computability.pdf
    Current 37-page A4 report, rebuilt from the 2621-line source in exactly
    three serial pdfLaTeX passes after the effective-continuity crosswalk.

inverse_fabius_computability_experiments.py
    Exact-rational Python supplement.  It uses only the Python standard
    library and documents the finite Thue--Morse spline, endpoint-mass bounds,
    interval-mass check, and a certified comparison/bisection demonstration.

numerical_output.txt
    Captured output from the Python supplement with its default arguments.

SHA256SUMS.txt
    SHA-256 digests of the preceding files and this README.

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

The random-series box-event proof itself is not formalized: Lean proves its
numerical conclusion through the stronger recurrence route.  The logarithmic
r(n) modulus, exact ceiling denominator d_* and its qualified fixed-target
minimality, tolerant bisection, sequential computability, the combined
computable-real-function theorem, and input-bit asymptotics remain open Lean
work.  The report retains their complete human proofs and imported-source
qualifications.  The scope correction for d_* remains in force: it is
denominator-minimal for the fixed dyadic proxy 2^{-r(n)}, not for the weaker
target tolerance 1/n.

Render and ledger status
------------------------
The 2621-line source was rebuilt in exactly three serial pdfLaTeX passes as a
37-page A4 PDF.  The rendered metadata now includes the formerly blank author
field; all fonts are embedded and subset, Libertinus is present, and no Type 3
font is used.  References, layout, and the complete render were inspected,
auxiliary files were removed, and the active checksum ledger was refreshed.

Reproduce the numerical supplement
----------------------------------
Run:

    python inverse_fabius_computability_experiments.py

No numerical experiment is used as a premise of the computability proof.
