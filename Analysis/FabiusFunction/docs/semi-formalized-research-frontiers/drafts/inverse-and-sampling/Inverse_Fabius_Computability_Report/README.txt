COMPUTABILITY OF THE INVERSE FABIUS FUNCTION
=============================================

Contents
--------
inverse_fabius_computability.tex
    Complete 2665-line, canonically styled LaTeX source of the report.  Its
    latest update crosswalks the effective-continuity formalization described
    below.

inverse_fabius_computability.pdf
    Current 37-page A4 rendering (693,787 bytes), rebuilt from the merged
    source in exactly three strict serial pdfLaTeX passes.

inverse_fabius_computability_experiments.py
    Exact-rational Python supplement using only the standard library.  It
    checks finite Thue--Morse splines, endpoint-mass bounds, interval masses,
    and a certified comparison/bisection demonstration.

numerical_output.txt
    Captured default output from the supplement.

ARRIVAL_SHA256SUMS.txt
    Immutable five-file ledger for the delivered payload.

SHA256SUMS.txt
    Six-entry ledger for the current repository-normalized package (the
    ledger itself is intentionally not self-hashed).

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
The probabilistic event proof, logarithmic modulus, exact ceiling denominator,
tolerant-bisection realizer, inverse sequential computability, combined
computable-real-function theorem, and optimal input-bit law remain paper-level.
The explicit periodic inverse correction and explicit all-orders inverse
reversion are imported research-frontier results, not Lean theorems.

The live formal corpus already proves the forward spline certificate and
forward computability, strict density shape, the clamped inverse and its
inverse identities/calculus, exact dyadic inverse evaluation, and the leading
inverse endpoint equivalent.  The report names those exact declarations and
keeps its remaining inverse-computability declarations unqualified and
schematic.  The live union audit scans 602 Lean modules and 8,194 public
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

Build and validation
--------------------
The 2665-line source uses the repository's canonical article/A4/27 mm/
Libertinus style and was rebuilt from clean auxiliaries in exactly three
strict serial pdfLaTeX passes.  The final 37-page, 693,787-byte PDF has the
formerly blank author metadata populated.  Its log has no errors, unresolved
references or citations, rerun requests, duplicate destinations, overfull
boxes, or underfull boxes.  Every page is A4 with zero rotation.  All 22 font
rows are embedded and subset; six are Libertinus and none is Type 3.  Text
extraction and visual checks cover the status boundary, corpus audit,
asymptotic caveat, Lean roadmap, proof-status table, and crosswalk.  Auxiliary
files were removed after validation and the active checksum ledger refreshed.

Current release hashes
----------------------
inverse_fabius_computability.tex
    17d5e306561da3b5e6c909569b89e56b68f374efbec45c9f57389cebc33be3bb

inverse_fabius_computability.pdf
    f1fac402b23f39804175f3864dc35ed182fc0f4d5ca4646b5ad9005c9810a9b5
