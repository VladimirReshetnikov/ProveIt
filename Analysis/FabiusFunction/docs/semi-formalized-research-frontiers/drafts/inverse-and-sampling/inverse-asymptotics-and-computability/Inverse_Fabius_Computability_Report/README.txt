COMPUTABILITY OF THE INVERSE FABIUS FUNCTION
=============================================

CURRENT SOURCE AND RETAINED PDF CHECKPOINT (2026-09-01)
-------------------------------------------------------
The current TeX has 2992 lines and SHA-256
359ac1239788d1d7af25214a6be26e421f716db6d1c254692469bddd2d25833a.
It retains the Lagrange/synthesis crosswalk and local inverse-notation/source
repairs, with the combined live audit updated to 631 modules and 8,556 public
declarations.  Exactly three clean, strict, serial pdfLaTeX passes produced
the retained 42-page A4 PDF (712,447 bytes; SHA-256
dc8da9d476d6b5330aad0ac3253bab162ddcb944653b038bc0aede4be4fc3fe1).
That PDF predates the present census update. A fresh three-pass render is
required before publication synchronization is claimed again; the operational
ledger already verifies the current distinct source and retained PDF.

Contents
--------
inverse_fabius_computability.tex
    Complete 2992-line, canonically styled LaTeX source of the report. Its
    semantic merge unites the equality/rigidity, effective-continuity,
    logarithmic reciprocal-modulus, and Lagrange/synthesis crosswalks while
    retaining the local inverse-notation and source repairs.

inverse_fabius_computability.pdf
    Retained validated 42-page A4 rendering of the preceding source checkpoint;
    it is pending a fresh render from the current source.

inverse_fabius_computability_experiments.py
    Exact-rational Python supplement using only the standard library.  It
    checks finite Thue--Morse splines, endpoint-mass bounds, interval masses,
    and a certified comparison/bisection demonstration.

numerical_output.txt
    Captured default output from the supplement.

ARRIVAL_SHA256SUMS.txt
    Immutable five-file ledger for the delivered payload.

SHA256SUMS.txt
    Refreshed six-entry operational payload ledger (the ledger itself is
    intentionally not self-hashed); all six rows verify the current distinct
    source and retained-PDF payloads without asserting render synchronization.

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
witness. `EffectiveMonotoneInverse.lean` formalizes computable clamping, the
three tolerant-comparison certificates, the fixed-depth bisection realizer,
its uniform dyadic-name error, and the restricted sequential inverse theorem.
`FabiusInverseComputable.lean` instantiates it and proves the combined
computable-real-function theorem for the totalized inverse. The probabilistic
event proof, exact ceiling denominator, the stronger abstract theorem deriving
an inverse modulus from a computable positive gap sequence, and the optimal
input-bit law remain paper-level.
The explicit periodic inverse correction and explicit all-orders inverse
reversion are imported research-frontier results, not Lean theorems.

The live formal corpus already proves the forward spline certificate and
forward computability, strict density shape, the clamped inverse and its
inverse identities/calculus, exact dyadic inverse evaluation, and the leading
inverse endpoint equivalent.  The report names those exact declarations and
now crosswalks the completed inverse-computability layer declaration by
declaration; only the stronger gap-derived abstract inversion statement keeps
an explicit partial boundary. The live union audit scans 631 Lean modules and 8,556 public
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
numerical conclusion through the stronger recurrence route. Tolerant
bisection, restricted and totalized sequential computability, and the combined
computable-real-function theorem are now formalized in
`EffectiveMonotoneInverse.lean` and `FabiusInverseComputable.lean`. The exact
ceiling denominator d_* and its qualified fixed-target minimality, the
stronger abstract gap-to-modulus theorem, and input-bit asymptotics remain open
Lean work. The report retains
their complete human proofs and imported-source qualifications.  The scope
correction for d_* remains in force: it is
denominator-minimal for the fixed dyadic proxy 2^{-r(n)}, not for the weaker
target tolerance 1/n.

Build and validation
--------------------
The current 2992-line source uses the repository's canonical
article/A4/27 mm/Libertinus style.  At the preceding source checkpoint, exactly
three strict serial pdfLaTeX passes produced the retained 42-page PDF with
populated title, author, subject, and keyword metadata.  All 42 pages are A4
with zero rotation and contain extractable text.  All 22 font rows are
embedded and subset, six are Libertinus, and no Type 3 font is used.  The
final log has no errors, warnings, unresolved references or citations, rerun
request, overfull box, or underfull box.  Pages 1, 21, and 42 were inspected
visually.  Auxiliary sidecars were removed after validation.  The active
six-entry ledger verifies the complete current payload, but the census-only
source update means the PDF is no longer claimed to render that source.
