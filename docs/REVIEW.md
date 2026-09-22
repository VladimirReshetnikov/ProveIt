# Exposition and proof review record

This records the scope of the September 22, 2026 documentation review. It is
separate from [Lean coverage](FORMALIZATION.md): an expanded mathematical proof,
a finite regression check and a compiled Lean theorem are different evidence.
No row below certifies every claim in an entire report.

## Reviewed portions and corrections

| Report | Inspected portion and result |
|---|---|
| [Foundations](foundations-and-computation/foundations/) | Expanded `found:thm:workspace` with arithmetic and universe-smallness prerequisites; supplied the missing positive, well-ordered control-set hypothesis in `found:prop:positive`. Distinguished intrinsic modulus/valuation topology from the full fine subspace topology. Proved the geometric convergence criterion and added `found:ex:boundedrankone`. |
| [Dynamics](surcomplex/dynamics-and-normal-forms/) | Corrected `dyn:cor:ancestry` to retain input support, proved finite dependence by word/block decompositions, and checked its arbitrary-input uses. The specialized linearizer counts an initial positive letter and retains its stronger bound. Corrected the blanket claim that changing exponent orientation reverses every inequality. |
| [Physics](physics/surreal-scalars-and-spacetime/) | Expanded `phys:prop:pole` and corrected abstract, conclusion and summaries: formal ramification preserves the pole but changes the coefficient by `w(0)^(−p)`. Distinguished the normalized recorded tests from the general theorem. |
| [Analytic geometry](surcomplex/analytic-geometry/) | Corrected `analytic:conv:notation` to define standard-part topology on finite tuples and explain its indiscrete zero-monad restriction. In `analytic:rem:fixed-not-transferred`, showed explicitly why the fixed-disk corona pair generates the whole common-domain germ ring after shrinking. |
| [Trigonometry](surcomplex/trigonometry/) | Corrected the infinitesimal-ideal notation and stated the nonzero-denominator condition in the asymptotic conventions. |
| [Computable surreals](foundations-and-computation/computable-surreals/) | Reviewed numerical names, basic ring operations, gap extraction and inversion. Added the missing output-range filter in `lem:geom`, qualified `prop:topology` by index size, repaired the runner/build paths, and tested the candidate-cover contract with negative zero candidates. |
| [Hahn evaluation at omega](surreal/hahn-evaluation-at-omega/) | Read the main proofs through the Higman/Neumann support appendix. Corrected the false ring/semiring incomparability claim by restriction and unique extension by differences. Distinguished general infinitesimal substitution from pure-monomial exponent change; proved intrinsic Laurent-field convergence of the geometric example while retaining full-surreal nonconvergence. Expanded zero evaluation, order preservation and the root/embedding correspondence. |
| [Broadcast sums](surreal/broadcast-sum-of-surreal-sequences/) | Read the move/rank definitions, commuting truncations, number-valuedness, perturbation and nested classification proofs. Corrected `cor:cofinite` to compare families on the same index set and required an infinite index set in `cor:dyadic-tail`, with a singleton counterexample. Extended the stated constant-family theorem to arbitrary infinite index sets using its finite-exception argument. Proved the no-options criterion and clarified limit thresholds and finite normal play. |
| [Canonical forms and option graphs](surreal/canonical-forms-need-not-be-subgraphs/) | Read the finite witnesses, prefix/minimum arguments, both girth constructions, classification and ordinal examples. Proved that the first spaced-spine construction already has maximum degree three and is planar in traversal leaf order. Supplied sign and template-disjointness steps; corrected the implications between triangle-free and containment failures, stronger-containment scope, and the recorded comparison-oracle claims. |
| [Genetic gaps and primitives](surreal/genetic-gaps-and-primitives/) | Read the main article and short proof. Strengthened `thm:general` with one positive radius valid at every input, using the set of positive pairwise differences and no simultaneous choice of witnesses. Distinguished local order-field openness from the source's restricted set-union convention, and checked the cited option-construction and topology conventions against their primary texts. |

Each correction was reviewed against its local definitions and downstream uses
within the stated scope. Changed PDFs were rebuilt and affected pages inspected.
The dynamics PDF retains its three pre-existing small overfull boxes; the
evaluation-at-omega and genetic-gap PDFs retain their baseline font/layout
warnings. The revised broadcast and option-graph PDFs have no warnings. Finite
symbolic checks support the physics examples; the corrected computability runner
passes its four separately counted suites. Its new cover regression fails when
the range filter is removed. Both option-graph suites were rerun successfully,
including all 3,860 exhaustive forms, 126 spaced-spine instances and 710
sparse/cycle certificates. Original broadcast test data were preserved without
a new run. These checks do not prove infinite statements.

## Collection-wide work

The [reader map](README.md), [catalogue](manifest.tex) and
[notation guide](NOTATION.md) cover all 26 canonical reports. The guide records
meaningful differences rather than treating shared names as definitions:
coefficient domains, support orientation, scalar standard part versus function
reduction, topologies, strong sums, derivatives, phases and computational names.
Its report links and cited labels were checked. Maintained Markdown navigation
was checked separately from deliberately historical paths in verification records.
Original manuscript archives are accessed through Git history; their removal
from the current tree does not discharge source-claim reconciliation.

## Remaining scope

The reports above have received targeted corrections or a main-text reading,
as recorded in each row. Uninspected portions, imported results, source-claim
reconciliation and any formalization remain separate obligations. The other
sixteen main reports have been mapped for notation and navigation but have not
received a full mathematical review in this pass:

- Exponential automorphism rigidity; Gamma functions; both birthday reports.
- Surcomplex analysis; contours and Stokes; differential equations; entire
  functions at arbitrary rank; finite deformations; global divisors; nonabelian
  support; polynomial algebra; rank-one Berkovich geometry; spectral theory.
- Surquaternions; computer algebra.

Continue with elementary statements and their dependencies before broad
classification theorems. For each portion, check definitions and size/domain
hypotheses, reconstruct abbreviated arguments, inspect downstream uses of any
correction, align terminology with the guide, and rebuild the affected document.
A source-to-merged-claim reconciliation is still required where a report's
provenance account alone does not establish equivalent scope.
