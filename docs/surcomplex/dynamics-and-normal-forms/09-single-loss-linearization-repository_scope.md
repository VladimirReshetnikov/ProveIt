# Repository provenance and scope

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit:

    a3124af79f66b8b9c196d76b4cbc5ac3938907c4

Relevant source:

    docs/surcomplex/dynamics-and-normal-forms/article.tex

Companion documentation:

    docs/surcomplex/dynamics-and-normal-forms/README.md
    docs/README.md

## The targeted question

The main source's open-questions section restates its exact-multiplier
common-domain problem under the label `dyn:q:commongerm-restate`, referring
back to `dyn:q:commongerm`. The source explicitly separates this problem
from a negative result that allows infinitesimal multiplier drift.

Its coefficient-category setup allows several dynamical variables and
requires each positive Hahn coefficient of the nonlinear perturbation to
have zero constant and linear terms. It uses the inverse-coordinate
convention J(F(z))=lambda*J(z) in one variable.

The delivered theorem gives the exact common-radius answer in **one
dynamical variable**. The main text uses F(H(z))=H(lambda*z), proves
same-domain inversion, and includes a second proof for J in Appendix B.

The source's drifted-multiplier question for a fixed cyclic value group
is separate and is not claimed solved. The new exact-multiplier theorem
itself applies to every nonzero set-sized ordered abelian value group,
including a cyclic one.

## Inspection limits

The repository inspection was targeted, not a line-by-line audit of every
package or Lean file. The pinned snapshot, rather than a moving main
branch, is the comparison point. No repository files were modified.

The external comparison includes Fauvet–Menous–Sauzin (2018), their
arXiv:2507.13216v2 revision of 13 September 2026, Marmi's small-divisor
notes, and the classical Neumann, Higman, and Gonshor references listed
in the article. The comparison does not certify bibliographic priority.
