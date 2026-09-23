# Sources, comparison, and priority limits

Research date: 23 September 2026.

## Fixed repository version

Repository: https://github.com/VladimirReshetnikov/Surreal

Revision: `3d40856953f4bb0f5d069e45a3b4bab6eda33040`.

The pin was obtained through the connected GitHub recursive-tree action.
The connected GitHub file/directory actions were used to inspect:

- root `README.md` (large returned text, partial);
- `docs/README.md`, including its catalogue and research-status notes;
- the holonomic report directory;
- `docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/README.md`;
- `docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/10-nonlinear-rigidity-PROOF_AUDIT.md` (complete);
- `docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/11-coarsening-differential-rigidity-SOURCES_AND_SCOPE.md` (complete);
- the beginning (lines 1–100) of that report's `article.tex`.

An attempted read of the oversized `docs/FORMALIZATION.md` returned no content;
that is not evidence about its mathematical coverage. A code search returned no
match for the question label; the question is instead located by the substantive
scope documents. Directory inventories and searches are not used to prove absence
of equivalent results elsewhere.

This was not a line-by-line audit of the 91-page assembled holonomic manuscript,
all 57 reports, archived submissions, history, or Lean declarations. A container
git clone failed due to unavailable network/DNS; the connector reads above worked.
The repository was not built during preparation of this article.

## The exact comparison target

The inspected source-11 scope document identifies the nonlinear question as
Question 19.1, label `hol:q:nonlinear` (formerly Question 15.1). The preceding
source-10 audit states first-order rigidity for every nonzero ordered group,
but no unrestricted theorem at order two or higher. The assembled report's
README and the source-11 document record the subsequent all-order solution
when the value group has no order unit, including meromorphic descent there.

The new article proposes:

1. the unrestricted second-order result for every nonzero value group;
2. the third-order result through cubic differential degree;
3. a more general third-order first-polar factor criterion;
4. external-constant and Gaussian-omnific coefficient consequences;
5. the planar algebraic-system consequence;
6. exact formal classifications of two higher-order boundary equations.

The nontrivial extension of the repository question is the order-unit case.
Existing all-order no-order-unit results, strong-summability conventions,
coefficient criteria, corner techniques, and the partial-theta witness are
credited, not presented as inventions of this article.

## Primary literature inspected

Vincenzo Mantova and Mickaël Matusinski,
*Surreal numbers with derivation, Hardy fields and transseries: a survey*,
arXiv:1608.03413v2 (2016).
https://arxiv.org/html/1608.03413v2

Used for normal-form and omega-map background and to distinguish scalar surreal
derivations from the added function-variable derivative. No all-order theorem
is imported from this survey.

Pei-Chu Hu and Yong-Zhi Luan,
*Non-Archimedean meromorphic solutions of functional equations*,
arXiv:1311.5291v1 (2013).
https://arxiv.org/html/1311.5291v1

Used for comparison with non-Archimedean functional-equation literature. The
article's particular absolute-value and equation hypotheses are not silently
extended to arbitrary-rank Hahn fields. No theorem is needed from it for the
proofs in this delivery.

Rida Ait El Manssour, Anna-Laura Sattelberger, and Bertrand Teguia Tabuguia,
*D-Algebraic Functions*, arXiv:2301.02512.
https://arxiv.org/abs/2301.02512

Consulted for general differential-algebraic context, not as a source of the
new rigidity theorem.

The user-provided Wikipedia page on surreal numbers was opened for orientation,
not treated as the technical authority for the proofs. Related coefficient-
arithmetic literature was also located, but its theorems are not needed for the
Newton-transition method and are not presented as dependencies.

## What the search establishes

The repository's inspected scope documents support identifying a specific gap
and comparing the proposed results to the recorded prior claims. The current
proofs are supplied in full and do not depend on a failed literature search.

The external search was limited. Several targeted queries returned irrelevant
results; that does not support an absence claim. No exhaustive MathSciNet,
zbMATH, book, thesis, or citation-network audit was performed. Accordingly this
package does not certify that no equivalent theorem has appeared elsewhere, or
that the results are historically first. No independently established famous
conjecture is advertised as completely solved.

Third-party papers, repository source files, and font files are not bundled.
