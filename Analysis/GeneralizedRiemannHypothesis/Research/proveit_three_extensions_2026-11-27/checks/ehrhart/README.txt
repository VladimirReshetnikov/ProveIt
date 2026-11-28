CRITICAL EHRHART COLLISIONS

Main proof fragment: ../../sections/ehrhart_critical.tex
Exact checks and binary64 illustrations: check_critical_ehrhart.py
Results: critical_ehrhart_checks.json
80-decimal recurrence cross-checks: high_precision_collision.py
Results: high_precision_collisions.json

Dependencies: Python, SymPy, SciPy, mpmath.
Commands:
    python check_critical_ehrhart.py --max-power 5
    python high_precision_collision.py

All 172 exact checks passed. Numerical examples remain numerical and are not
interval certificates. The proof does not depend on their correctness.

THE NEW RESULT
For K_(d+1) with M matching edges deleted, the local Ehrhart-zero collisions
near -1/2 + i (2j+1) pi/log(d) have different critical scales by dimension parity.
Even dimensions: a quadratic normal form with parameter window log(d)^(-2),
root splitting log(d)^(-2), and explicit positive threshold correction.
Odd dimensions: a cubic normal form with parameter window log(d)^(-2/3),
root splitting log(d)^(-4/3), and explicit negative threshold correction.
The exact first-order threshold in the preceding report is locally stable in
the even case, while the odd equality already has an off-line pair.

Every j is fixed. The results concern a specified local cluster, not the
first off-line root globally. M is interpolated as a real parameter for the
exact collision; integer M gives actual graph Ehrhart polynomials. All
new assertions are unconditional human-readable proofs, not Lean proofs.

SOURCE BOUNDARY
Pinned ProveIt commit: 42efb893353a150857f5c8e2f9e7732d0d46f15f.
Article/sections/gra.tex: finite-width canonical-line result and all-width question.
docs/incoming/multipartite-ehrhart.zip: matching-deletion identity and strict
sub/supercritical asymptotics; equality is explicitly omitted there.
No duplication was found in the 26 current incoming archives on this local
second-order/cubic collision question. This is a scoped comparison, not an
exhaustive literature priority claim.

The broader complete-bipartite all-width conjecture was investigated but not
resolved. Exact Sturm checks found all expected positive squared roots for
K_(34,34), K_(40,40), K_(50,50); this finite evidence proves no general result
and is not part of the new theorem. Exploratory scripts ehrhart_square.py and
check_diagonal.py may be omitted from the final deliverable.

PRIMARY CONTEXT SOURCES
Higashitani--Kummer--Michalek, Interlacing Ehrhart polynomials of reflexive
polytopes, arXiv:1612.07538 (original named conjecture, broader multipartite
version now disproved elsewhere).
Higashitani--Jochemko--Michalek, Arithmetic aspects of symmetric edge polytopes,
arXiv:1807.07678 (known graph Ehrhart formulas).
Kolbl, On a conjecture concerning the roots of Ehrhart polynomials of symmetric
edge polytopes from complete multipartite graphs, arXiv:2404.02136.
NIST DLMF 15.8.4 for the hypergeometric connection formula and chapter 5 for
gamma/digamma identities. Flajolet--Sedgewick, Analytic Combinatorics,
Chapter VI for multiple-singularity transfer.

Web search additionally verified that the Davis six-partite counterexample
refutes the original multipartite formulation; it does not prove the bipartite
question, which the present work does not settle.
