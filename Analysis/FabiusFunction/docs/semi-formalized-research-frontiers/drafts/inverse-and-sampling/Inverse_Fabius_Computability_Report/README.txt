COMPUTABILITY OF THE INVERSE FABIUS FUNCTION
=============================================

Contents
--------
inverse_fabius_computability.tex
    Complete LaTeX source of the report.

inverse_fabius_computability.pdf
    Rendered 34-page report.

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
The structural inverse-modulus portion of the report is now crosswalked to
the compiler-validated module:

    Analysis/FabiusFunction/Lean/FabiusFunction/InverseModulus.lean

That module covers global fixed-length Fabius increments, reflection and
one-sided shape, the least endpoint increment, constrained forward
superadditivity, local and global inverse-gap bounds, global inverse
subadditivity, attained exact unit-interval and totalized moduli, and the
exact effective-injectivity threshold.

It does not cover the closed Delta_r lower bound, recursive-modulus packaging,
tolerant bisection, sequential computability, the combined computable-real-
function theorem, or the input-bit asymptotics.  Those retain the complete
human proofs and imported-source qualifications in the report.  The revision
also corrects the scope of d_*: it is denominator-minimal for the fixed dyadic
proxy 2^{-r(n)}, not for the weaker target tolerance 1/n.

Build and validation
--------------------
The PDF was built with three direct pdfLaTeX passes.  The final log has no
unresolved references, overfull boxes, or underfull-box warnings.  The PDF was
checked with pdfinfo, pdftotext, font inspection, PyMuPDF preflight, and a full
34-page Poppler render.

Reproduce the numerical supplement
----------------------------------
Run:

    python inverse_fabius_computability_experiments.py

No numerical experiment is used as a premise of the computability proof.
