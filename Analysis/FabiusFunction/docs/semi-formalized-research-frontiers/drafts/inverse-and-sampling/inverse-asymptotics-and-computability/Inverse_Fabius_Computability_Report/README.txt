COMPUTABILITY OF THE INVERSE FABIUS FUNCTION
=============================================

SOURCE-ONLY MERGE STATUS (2026-08-31)
-------------------------------------
The current TeX has 2937 lines and SHA-256
3ee69aa0c27486d5005e4d5f8448b36a8133083c8b79df51e9d08a5af56880b5.
The retained 42-page PDF was not rebuilt after the notation migration and is
not claimed to be synchronized with that source.  SHA256SUMS.txt was
intentionally not refreshed: its TeX row and this README row are pending,
while its other four rows pass.  Later uses of "synchronized", "current", or
"final" in historical build notes refer to the preceding checkpoint.

Contents
--------
inverse_fabius_computability.tex
    Complete 2937-line, canonically styled LaTeX source of the report.  Its
    semantic merge unites the equality/rigidity, effective-continuity, and
    logarithmic reciprocal-modulus crosswalks described below.

inverse_fabius_computability.pdf
    Retained 42-page A4 rendering from the preceding publication checkpoint;
    not rebuilt from the current merged source.

inverse_fabius_computability_experiments.py
    Exact-rational Python supplement using only the standard library.  It
    checks finite Thue--Morse splines, endpoint-mass bounds, interval masses,
    and a certified comparison/bisection demonstration.

numerical_output.txt
    Captured default output from the supplement.

ARRIVAL_SHA256SUMS.txt
    Immutable five-file ledger for the delivered payload.

SHA256SUMS.txt
    Six-entry operational ledger from the preceding checkpoint (the ledger
    itself is intentionally not self-hashed); TeX and README rows are pending.

Arrival provenance
------------------
The source archive Inverse_Fabius_Computability_Report.zip was 689,198 bytes
with SHA-256

    755d77354490d25d4f327419d0345623e91ea49dd4ba681ba97c84a0b686b8c1

Its path and integrity audit was clean.  The original five-file checksum
ledger verified 5/5 before any editorial normalization; those hashes are
preserved in ARRIVAL_SHA256SUMS.txt.  The manuscript recorded ProveIt commit
40fdea4cc0a728189f357389e3f114a2cb00e561 as its arrival snapshot.

Theorem-status boundary
-----------------------
The structural least-interval-mass and exact inverse-modulus layer now has
matching public Lean declarations in `InverseModulus.lean`.  That module
formalizes fixed-length increment shape and reflection, the least endpoint
increment, constrained forward superadditivity, local and global inverse-gap
bounds, inverse subadditivity, attained exact unit-interval and totalized
moduli, and the exact effective-injectivity threshold.

The numerical endpoint-mass estimate, strict and closed dyadic inverse
moduli, primitive-recursive denominator packaging, and effective uniform
continuity now have matching declarations in
`FabiusInverseEffectiveContinuity.lean`; Lean derives the endpoint inequality
through a stronger recurrence rather than the report's random-series event.
`FabiusInverseLogarithmicModulus.lean` additionally formalizes the least
logarithmic order, both composed denominators, the strict and closed
reciprocal moduli, and effective uniform continuity with either logarithmic
witness.  The probabilistic event proof, exact ceiling denominator,
tolerant-bisection realizer, inverse sequential computability, combined
computable-real-function theorem, and optimal input-bit law remain paper-level.
The explicit periodic inverse correction and explicit all-orders inverse
reversion are imported research-frontier results, not Lean theorems.

The live formal corpus already proves the forward spline certificate and
forward computability, strict density shape, the clamped inverse and its
inverse identities/calculus, exact dyadic inverse evaluation, and the leading
inverse endpoint equivalent.  The report names those exact declarations and
keeps its remaining inverse-computability declarations unqualified and
schematic.  The live union audit scans 615 Lean modules and 8,383 public
declarations with zero documentation/header gaps.  No unqualified worldwide
novelty claim is made.

Reproducibility
---------------
Running

    python3 inverse_fabius_computability_experiments.py

reproduced numerical_output.txt byte for byte (SHA-256
6f65be66860d65b95c20dee9f2cfa204b0b6c4464f8d768467184c3fd47e2ff9).
No numerical experiment is used as a premise of the computability proof.

Post-publication Lean crosswalk
-------------------------------
The structural inverse-modulus portion of the report is crosswalked to:

    Analysis/FabiusFunction/Lean/FabiusFunction/InverseModulus.lean

That module covers global weak and maximal strict fixed-length Fabius-increment
shape, reflection, the least endpoint increment and its complete equality
locus, constrained forward superadditivity with exact equality cases, local and
global inverse-gap bounds, unit-input inverse-gap rigidity, global inverse
subadditivity, attained exact unit-interval and totalized moduli, and the exact
effective-injectivity threshold.

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

Build and validation
--------------------
At the preceding publication checkpoint, the then-2967-line source used the
repository's canonical article/A4/27 mm/Libertinus style and was rebuilt from
clean auxiliaries in exactly three strict serial pdfLaTeX passes.  The
retained 42-page PDF has populated
author metadata; every page is A4 with zero rotation; every font is embedded
and subset; Libertinus is present; and no Type 3 font is used.  The final log
has no errors, unresolved references/citations, rerun request, or overfull
box.  Text extraction and visual checks cover the status boundary, corpus
audit, asymptotic caveat, Lean roadmap, proof-status tables, and both
exhaustive effective-continuity crosswalks.  Auxiliary files were removed
after validation and the six-entry active checksum ledger refreshed. Those
build and ledger facts are historical; the source-only merge status above is
the current state.
