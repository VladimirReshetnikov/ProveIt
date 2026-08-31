COMPUTABILITY OF THE INVERSE FABIUS FUNCTION
=============================================

Contents
--------
inverse_fabius_computability.tex
    Canonically styled LaTeX source of the research-frontier report.

inverse_fabius_computability.pdf
    Current 35-page A4 rendering (682,022 bytes), regenerated from the merged
    source.

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

The elementary endpoint-mass estimate, recursive-modulus packaging,
tolerant-bisection realizer, inverse sequential-computability/effective-
uniform-continuity packaging, and optimal input-bit law retain self-contained
paper proofs but no matching public Lean declarations.  The explicit periodic
inverse correction and explicit all-orders inverse reversion are imported
research-frontier results, not Lean theorems.

The live formal corpus already proves the forward spline certificate and
forward computability, strict density shape, the clamped inverse and its
inverse identities/calculus, exact dyadic inverse evaluation, and the leading
inverse endpoint equivalent.  The report names those exact declarations and
keeps its remaining inverse-computability declarations unqualified and
schematic.  The live union audit scans 596 Lean modules and 8,124 public
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
The source now uses the repository's canonical article/A4/27 mm/Libertinus
style.  After the final source freeze, exactly three strict serial pdflatex
passes were run from clean auxiliaries.  The final log has no errors,
unresolved references or citations, rerun requests, duplicate destinations,
overfull boxes, or underfull boxes.  All 35 pages are A4 with zero rotation.
All 22 font rows are embedded and subset; six are Libertinus and none is
Type 3.  Text extraction and visual checks cover the status boundary, corpus
audit, asymptotic caveat, Lean roadmap, proof-status table, and crosswalk.

Current release hashes
----------------------
inverse_fabius_computability.tex
    c258ee98ecc740981863d8a7f44c055c8bd8ee5d32f7f39a5b106517b409574e

inverse_fabius_computability.pdf
    cb01e5e8f73eeeed743a248e80d902deaa5164e98471defceb83bf540ed52b5d
