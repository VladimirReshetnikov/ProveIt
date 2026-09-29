# Source and attribution ledger

Access and comparison date: 29 September 2026.

## Pinned repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit: `9b24a3a8d545af9624f6ac455f5b548be62818b6`  
Commit timestamp: 2026-09-29 16:02:05 UTC.

Repository content was read using the connected GitHub tool. This package
neither edits the repository nor inherits the formal status of declarations
stored elsewhere in it.

### Formal project context

`Algebra/JacobianConjecture/README.md`

Pinned URL:
https://github.com/VladimirReshetnikov/ProveIt/blob/9b24a3a8d545af9624f6ac455f5b548be62818b6/Algebra/JacobianConjecture/README.md

Used for the exact original map, Jacobian -2, rational/integral collisions,
weighted action, and the repository's account of its Lean/Rocq development.
The original determinant, collision, and normalization relation were also
checked independently in exact SymPy arithmetic.

### Prior weighted-Keller report

Directory:
`SetTheory/Cardinals/docs/reports/jacobian-conjecture/weighted-keller-rigidity/`

Files read: `README.md` and relevant contiguous portions of `article.tex`,
including the setting, normal forms, proof lemmas, reconstruction, source
shear, degree spectrum, formal-status discussion, and further questions.

Pinned URL:
https://github.com/VladimirReshetnikov/ProveIt/tree/9b24a3a8d545af9624f6ac455f5b548be62818b6/SetTheory/Cardinals/docs/reports/jacobian-conjecture/weighted-keller-rigidity

The prior article is dated 24 September 2026. Its Section 10.2, appearing
in the source range beginning at line 1280, asks whether r=R(t)+G(t)v can
have nonconstant G when p and q remain affine in v and the polynomial lift
is Keller. The present article answers that exact question negatively.

The prior report already contains the constant-slope classification,
source shear extension, tame inverse, core support, degree spectrum, and
normalization of the known map. The report itself credits the project's
research notes for the weighted determinant identity and collision
mechanism. These are not presented as discoveries of this package.

Other future problems in that report, including quadratic v-dependence
and high-degree stabilization of the noninjective double point, are not
claimed solved by the new slope theorem.

## Primary literature consulted

### T. Shaska

*Graded Keller maps and the Jacobian Conjecture*, arXiv:2607.20210v2.
Submitted 22 July 2026; version 2 dated 25 July 2026.

https://arxiv.org/abs/2607.20210v2
https://arxiv.org/html/2607.20210v2

Used for current context on graded maps, quotient-coordinate Jacobian
conditions, and coefficient schemes. The HTML text was inspected rather
than treating the abstract as a substitute for the full paper. Its weight
sign convention is the simultaneous opposite of the one used here; the
underlying torus symmetry is the same after parameter inversion.

### Shuhong Gao

*Counterexamples to the Jacobian conjecture in dimensions greater than two*,
arXiv:2608.00222v1. Submitted 31 July 2026.

https://arxiv.org/abs/2608.00222v1
https://arxiv.org/html/2608.00222v1

Used for current context on the tangent-sweep construction and geometric
fiber degrees. The paper's geometric degree must not be conflated with
ordinary polynomial degree. No external classification theorem from Gao
is assumed in the new proof.

## Review limitations

This was a targeted repository and primary-literature comparison, not a
complete bibliographic priority search. No independently refereed status
is inferred from arXiv posting or repository placement. The new written
proofs are self-contained apart from elementary field, polynomial,
unique-factorization, nilradical, and cubic-Galois facts that are explained
where used. The formal-flow construction is standard and is not advertised
as a new general deformation principle.
