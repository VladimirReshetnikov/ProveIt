# Sources and attribution

Reviewed on 30 September 2026 (America/Los_Angeles). ProveIt reference commit:
`a866ff9a2cdb9c5f436bb1d82ea5dca59dfee38d`, timestamp
`2026-10-01T00:16:34Z` (still 30 September locally).

## ProveIt

Base URL:
https://github.com/VladimirReshetnikov/ProveIt/tree/a866ff9a2cdb9c5f436bb1d82ea5dca59dfee38d

Reviewed via the GitHub connector:

1. `README.md` and `Algebra/JacobianConjecture/README.md`.
   Used for the repository map, original polynomial definition, determinant,
   collisions, declared formal status, and links to follow-up reports.
2. `Algebra/JacobianConjecture/Lean/JacobianConjecture/Counterexample.lean`.
   Read at the exact reference commit, lines 80–173. Includes
   `counterexample`, `jacobianDet_counterexample`, `collision`, and the two
   collision-value proofs. Content blob:
   `52bcf58a062b2db21d1a556579aa5d3d8564437f`.
3. `SetTheory/Cardinals/docs/reports/jacobian-conjecture/weighted-keller-rigidity/README.md`.
   Read the classification, source-shear construction, degrees, proposed-work,
   and status/limitation descriptions. Reports themselves are unrefereed.
   The shear construction and classification are credited, not claimed new.
4. `SetTheory/Cardinals/docs/reports/jacobian-conjecture/arithmetic-local-global-fibers/README.md`.
   Read the notation and cubic-inverse baseline. The inverse parameter is
   `tau=y+1/x`, not `x*y`. No arithmetic Hasse-principle result is needed
   by the new proofs.

The new results only depend on the explicit displayed map and elementary
identities rederived in the article; the larger report classifications are
not assumed as unverified mathematical premises.

## Liam Giannini

*The Alpöge–Fable counterexample to the Jacobian Conjecture: verification,
geometry, dynamics, and an equivariant program for the plane case.*
Zenodo, version 1.1, 20 July 2026.
https://zenodo.org/records/21461572
DOI: 10.5281/zenodo.21461572

The public record description lists iterate degrees 7,43,265,1633,10063,62011
and suggests first dynamical degree 3+sqrt(10). The article proves that value
by an all-iterate argument. The linked PDF could not be successfully retrieved;
the linked `Liam-G/m` source repository returned not found through the connector.
No conjecture number, internal PDF theorem statement, or claim about an unseen
proof is attributed to that source. This record is not peer reviewed.

## Shuhong Gao

*Counterexamples to the Jacobian conjecture in dimensions greater than two.*
arXiv:2608.00222v1, 31 July 2026.
https://arxiv.org/html/2608.00222v1

HTML representation reviewed, especially Section 3.4 / Theorem 3.3 for the
same baseline map and generic degree three. The article does not assume
new constructions or fiber classifications from this source.

## External audit

`shadybrook/jacobian-counterexample-audit` contributors,
*An Exact Audit of an Announced Three-Dimensional Keller Map.*
AI-assisted working note, stated revision 21 July 2026.
https://github.com/shadybrook/jacobian-counterexample-audit/blob/main/paper/main.md
Content blob read: `a6950580cd582458d1f05ccf259af33e833f9fce`.

Reviewed the baseline discussion and Proposition 8.3 with adjacent context.
Its component degrees `(5d-3,5d-4,4)` concern varying the construction parameter
`d`, not iteration. Its generic degree also varies, unlike the source-shear
family in the present article. This distinction is stated in the article.

## Priority boundary

Targeted searches included the map's name with “dynamical degree” and
“degree growth,” and the displayed numerical value with Jacobian terminology.
They do not establish an exhaustive absence of prior proofs. These results
are presented as independent theorems and research extensions, not as the
first proof of a long-standing named conjecture. The public numerical
prediction is verified; global novelty and historical priority remain
unestablished. No material from an inaccessible full manuscript is treated
as reviewed.
