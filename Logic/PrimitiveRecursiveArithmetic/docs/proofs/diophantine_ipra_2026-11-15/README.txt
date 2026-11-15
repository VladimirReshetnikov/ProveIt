CONSTRUCTIVE DIOPHANTINE THEOREMS IN iPRA
15 November 2026

READ FIRST
==========
This package does not prove all three requested full theorems.  It provides:

1. A complete human-readable, primitive-recursive proof and enumeration
   algorithm for Størmer's theorem on consecutive smooth positive integers.

2. A complete finite proof of a constructive Davenport–Schmidt theorem,
   retaining exponent 3 and using the explicit constant 32768*max(1,xi^2).
   The theorem is a schema for a fixed primitive-recursive rational name and
   a fixed primitive-recursive quadratic separation modulus.  The report
   supplies such a modulus for algebraic inputs of degree at least three.

3. A complete constructive Roth cutoff for every quadratic algebraic
   irrational and positive rational exponent increment, and the Liouville
   range for all degrees.  The full general effective Roth cutoff is NOT
   proved; it remains an outstanding effectivity problem.  Cardinality
   bounds and denominator cutoffs are explicitly distinguished.

4. Lean specifications and a concrete route to object-level iPRA proofs.
   The new Lean files have NOT been compiled or kernel checked, and the
   principal object-iPRA derivations have NOT been completed.

CONTENTS
========
paper/diophantine_ipra.pdf      Complete article
paper/diophantine_ipra.tex      Main LaTeX source
paper/01_*.tex through 05_*.tex Article sections
paper/references.tex           Primary references and pinned repository links
code/arithmetic.py            Exact reference algorithms, standard library only
code/verify.py                Reproducible finite checks
lean/FiniteSpecifications.lean Numerical definitions and theorem specifications
lean/ObjectTargets.lean       Object formula and existing repository transport
lean/FORMALIZATION_STATUS.txt  Precise formal status and completion commands
verification/                 Exact JSON examples and build/check evidence
provenance/                   Source provenance and repository snapshot
SHA256SUMS.txt                File integrity hashes
build.sh                      Ordinary two-pass pdflatex build

REPRODUCTION
============
From this directory:

    python3 code/verify.py
    ./build.sh

Python needs no external package.  The document build needs a working LaTeX
installation with the standard packages listed in the main .tex file.

Do not eagerly evaluate the enormous theoretical Pell or Davenport–Schmidt
bounds for numerical work.  The reference Pell implementation compares its
bound in compressed form and returns as soon as it finds the fundamental
solution.  The Davenport–Schmidt example search verifies small exact root
certificates; it does not execute the enormous universal construction.

REPOSITORY BASELINE
===================
https://github.com/VladimirReshetnikov/ProveIt
Commit b33ee1acb02b7619dfef419e61c3e343735a7bc4
ConciseIPRA source:
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/
Toolchain: leanprover/lean4:v4.32.0

No repository write, commit, or pull request is included in this deliverable.

VALIDATION SCOPE
================
The PDF was compiled and visually inspected.  The mathematical bounds and
core proofs received independent audits.  Python checks use exact arithmetic
and compare the Størmer enumerator with independent smooth-number generation.
These checks support the reference code.  They do not replace the general
proofs and do not certify a Lean or object-iPRA derivation.
