# Source audit

Preparation date: 28 September 2026.

## Repository source

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected report:
`SetTheory/Cardinals/docs/reports/log-concavity-and-unimodality/nonreal-roots-in-iterative-equations/article.tex`

Title: *Nonreal Roots Survive in Polynomial Iterative Equations: A cubic
counterexample and a classification of circular spectra*.
Report date: 20 September 2026.
Returned Git blob SHA: `ae6ea0aa0566316ba9ed06b1750c6e73275059da`.

The source's conclusion explicitly leaves minimal polynomials with roots on
several distinct circles unclassified. It also leaves decreasing maps,
zero-constant-coefficient equations, and proper interval domains outside
its classification. The present paper addresses the arbitrary-radius gap
for increasing whole-line maps; the other exclusions remain in force.

The source report's circular results, orbit recurrence framework, and
regularity discussion were inspected. The present paper reproves the
needed elementary machinery and supplies an arbitrary-radius sufficiency
construction and universal root-level reduction.

## External primary sources

1. S. Draga and J. Morawiec, *Reducing the polynomial-like iterative equations
   order and a generalized Zoltán Boros' problem*, Aequationes Mathematicae
   90 (2016), 935–950. DOI: 10.1007/s00010-016-0420-4.
   https://arxiv.org/abs/1503.00570
   Problem 6.1 appears on preprint page 13. The page was also visually
   inspected. Used to identify the root-elimination question and distinguish
   equal-modulus cases from strict modulus separation.

2. S. Draga, *A note on the order of polynomial-like iterative equations*,
   Commentationes Mathematicae 56 (2016), 243–249.
   Preprint: https://arxiv.org/abs/1604.01287v2
   Used for later order-reduction context and the distinction between a
   common annihilator and a disjunction of possible reductions for
   decreasing solutions.

3. F. Petrov, *Continuous linear recurrent relations*, MathOverflow,
   question 232493, 1 March 2016, including I. Bogdanov's comments.
   https://mathoverflow.net/questions/232493/continuous-linear-recurrent-relations
   Used for the original rigidity question and attribution of the
   piecewise-linear counterexample mechanism.

## Novelty boundary

These checks establish a concrete extension of the inspected repository
report, and delimit the relationship to the original questions. They are
not an exhaustive bibliography or priority search. The paper therefore
claims its explicit mathematical results with written proofs, not a
certified first discovery in the literature. No source paper is repackaged
in this archive.
