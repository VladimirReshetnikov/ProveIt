SIEGEL'S THEOREM AND INTUITIONISTIC PRIMITIVE RECURSIVE ARITHMETIC
Research package prepared for Vladimir Reshetnikov
15 November 2026

READ FIRST
==========
This package DOES NOT prove the general Siegel theorem in iPRA.
It provides a precise analysis of that unresolved request, a complete
constructive Runge subcase, exact algorithms, compiled native Lean results,
and an explicit path to embedded iPRA proofs of the elementary results.
No independence or unprovability claim is made.

The full general positive height/list target, the weaker general cardinality
target, and their embedded iPRA proofs remain unproved. A general height/list
proof would have consequences for the open general effective Siegel problem.
A count bound is logically different and does not automatically locate points.

MAIN RESULTS
============
1. From a finite identity D^2 f = A^2 + R, with D > 0, deg A >= 1,
   R nonzero, and deg R < deg A, the paper proves every integer solution
   of y^2=f(x) satisfies

       |x| <= H = sum of absolute lower coefficients of A
                    + sum of absolute coefficients of R,
       |y| <= K = sum_i |f_i| H^i.

   Here H >= 1. The exact finite enumeration is complete.

2. An explicit rational square-completion algorithm constructs such a
   certificate for every nonsquare integer polynomial of positive even
   degree whose leading coefficient is a positive integer square.

3. For every m >= 2, y^2=x^(2m)+x+1 has exactly four integral points:
   (-1,-1), (-1,1), (0,-1), (0,1).
   Its smooth projective completion has genus m-1. The genus identification
   is explained separately; the arithmetic proof does not assume it.

4. For y^2=x^4+a*x^2+b with delta=a^2-4*b != 0:
       4*x^2 <= |delta|+1-2*a,
       4*|y| <= |delta|+1.
   The divisor algorithm gives a complete solution list.
   The example a=7,b=1 has exactly the six points (0,+/-1),(+/-1,+/-3).

5. The logic discussion proves the precise implication from a hypothetical
   uniform positive iPRA theorem with decidable hypotheses to a primitive
   recursive height bound, using the arbitrary-matrix witness theorem.
   It distinguishes this from count and negative finiteness formulations.

FORMAL STATUS
=============
Arithmetic.lean, FiniteSearch.lean, QuarticExample.lean, and
Specifications.lean compile under Lean 4.32.0 with Std only.
The arithmetic factor bound, exact finite-list/bound equivalence, and the
global six-point quartic classification are proved in native Lean.
The audited native results use at most propext and Quot.sound; none uses
Classical.choice, sorryAx, or a new axiom declaration.

RungeBoundTarget, RungeEnumerationTarget, GenusFamilyTarget,
PositiveSiegelTarget, and CountSiegelTarget are definitions of UNPROVED
Lean propositions, not asserted theorems or assumptions.
The Boolean admissibility parameter of the last two has no built-in
geometric implementation.

The full polynomial Runge proof and the uniform genus-family classification
are human-readable arithmetic proofs. Their native polynomial-list Lean
proofs remain to be completed. No deeply embedded Prf PRAAx proof object
has yet been constructed. The paper and lean/OBJECT_PLAN.txt provide
explicit quantifier-free invariants and the actual ProveIt interfaces.

CONTENTS
========
paper/siegel_ipra.pdf         Complete report.
paper/siegel_ipra.tex         Master editable LaTeX source.
paper/01_*.tex ... 07_*.tex    Included sections.
paper/references.tex          Primary sources and pinned repository reference.
lean/*.lean                  Four native modules plus axiom audit.
lean/OBJECT_PLAN.txt         Object-iPRA definitions and proof obligations.
lean/build.sh                Reproducible native Lean build.
lean/lean-toolchain          leanprover/lean4:v4.32.0.
code/runge.py                Exact certificate construction and solvers.
code/verify.py               Finite cross-checks, independent implementations.
code/verification.json       Recorded Python results.
code/build_pdf.py            PDF build with optional private TeX format.
verification/                Build logs and document checks.
provenance/                  Repository audit and source references.
SHA256SUMS                   SHA-256 of every other delivered file.

REPRODUCE
=========
From this package root:

    python3 code/verify.py
    bash lean/build.sh
    python3 code/build_pdf.py

With a custom Lean executable:

    SIEGEL_LEAN_BIN=/absolute/path/to/lean bash lean/build.sh

Lean requires only the pinned release's bundled Std, no Mathlib download.
Python requires only its standard library.
LaTeX needs the packages listed in paper/siegel_ipra.tex. The build script
can create a private format from installed TeX sources if system formats
are missing. Shell escape is disabled.

Verify checksums before rebuilding:

    sha256sum -c SHA256SUMS

VALIDATION SCOPE
================
The reference checks compare 10,385 square-root cases, 11 family instances,
284 nonzero-delta quartics, and two additional completion examples.
Nine malformed/out-of-scope cases are rejected. These checks verify finite
program behavior; the written proof establishes universal completeness.
The PDF was built and visually inspected. Native Lean theorem and axiom
checks are recorded in verification/lean_build.txt.

REPOSITORY
==========
VladimirReshetnikov/ProveIt was read at commit
7eeb3c0e821594d5d5ebcfbaf4bdba64819e3502.
Exact paths and verified Git blob hashes are in provenance/repository_manifest.json.
The upstream repository was not modified or rebuilt. The delivered native
Lean package is standalone. The related repository packages do not furnish
a completed general effective Siegel theorem.
