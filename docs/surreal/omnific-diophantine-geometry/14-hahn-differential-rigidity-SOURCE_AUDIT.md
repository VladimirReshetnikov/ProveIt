# Source, novelty, and proof audit

## 1. Fixed repository snapshot

Repository: https://github.com/VladimirReshetnikov/Surreal
Commit inspected: `4cdeaec43ff1692ed2ad9f5bdf761a41872975a5`.
Date of research: September 23, 2026.

The GitHub connector was used to read repository metadata and the recursive
tree, the main README, the documentation catalogue, and the relevant source
and report READMEs. The main mathematical comparison is with
`docs/surreal/omnific-diophantine-geometry/article.tex`, whose blob SHA at this
snapshot is `4c26f4e4bee62f76428d7c69adf4aabe5af5ec53`.

Inspected source ranges included lines 1–180 (scope and conventions),
1000–1185 (arithmetic boundaries and transfer), 1550–1785 (Euler derivations,
separated-power rigidity, the explicit elliptic limitation, and the start of
unimodular Fermat), and 2920–3080 (workspace scope and continuation questions).
The report README provides a broader statement inventory. Its Question 14.1,
label `odg:q:affine`, asks for affine-curve rigidity and names the general
Weierstrass equation with a nonzero linear coefficient as the next test.

Other report READMEs were consulted to avoid choosing a topic already covered,
including the entire-Hahn holonomic-rigidity and set-sized omnific-quotient
reports. No new result about the remaining nonlinear order-unit differential
question is claimed. No exhaustive line-by-line audit of all repository
reports or all supplementary manuscripts was performed.

## 2. Existing results versus additions

Existing repository inputs:
- The normal-form convention and ring retraction to constant coefficients.
- Nonnegative support degree and constant units in the opposite-support ring.
- Support-preserving Euler derivations and detection by a family of probes.
- Rigidity of separated powers and earlier unimodular Fermat results.
- The existence-versus-classification distinction for omnific equations.

Proposed additions proved in this article:
- Abstract contraction of global differentials over two compatible rings.
- Proper rigidity when the cotangent sheaf is globally generated.
- Classification of all smooth geometrically integral affine curves over every
  characteristic-zero coefficient field, for every nonzero ordered group.
- Squarefree superelliptic rigidity and an explicit cubic Bezout certificate.
- A sharp smooth/singular dichotomy for constant Weierstrass cubics.
- Abelian, semi-abelian, finite-cover, and unimodular projective consequences.
- An arithmetic-model dichotomy with polynomial families through every
  integer point of the exceptional affine-line case.
- A characteristic-two elliptic counterexample.

## 3. Published mathematical inputs

The article's bibliography supplies stable URLs and publication details.
The primary sources checked for the geometric proof were:

- Stacks Project, Tag 0BX5: the valuative criterion for properness using
  arbitrary valuation rings.
- Stacks Project, Tag 00RM: universal differentials and their functoriality.
- Stacks Project, Tag 0BS6: Riemann–Roch for curves.
- Stacks Project, Tag 0BXX, with 0BY1 and 0BY3: curves, function fields,
  projective models, and smoothness over perfect fields.
- Stacks Project, Tag 0C6L: genus-zero curves and rational points.
- J. S. Milne, *Abelian Varieties*, v2.00 (2008), Chapter III Section 2 and
  Chapter IV Section 6: canonical forms on curves and invariant differentials.
  The relevant PDF pages were inspected as screenshots, including physical
  pages 99 and 158 (printed pages 93 and 152).

Conway and Gonshor are cited for the classical surreal normal-form background.
The generalized-series ring is also classical in the work of Berarducci and
L'Innocente–Mantova. The latter's arXiv version 5 and publication metadata were
consulted; its factorization results are not rebranded as new here.

A significant nearby precedent is L. van den Dries, “Which curves over Z have
points with coordinates in a discrete ordered ring?”, *Transactions AMS*
264 (1981), 181–189, DOI 10.2307/1998418. The bibliographic record and abstract
were consulted through the author's bibliography. The abstract describes a
Riemann–Roch criterion for existence in a discrete ordered ring. The present
article addresses a fixed Hahn-ring family and the fixed omnific ring.
However, the full older proof was not obtained through the consulted route;
no exhaustive implication comparison or priority assertion over it is made.

## 4. Critical proof checks

1. Support orientation is consistent: t^gamma corresponds to omega^(-gamma).
   The ring B has nonpositive t-support; O has nonnegative leading valuation.
2. Constant extraction is multiplicative on B because two nonpositive
   exponents sum to zero only when both vanish.
3. Euler probes preserve B and carry O into its maximal ideal, killing the
   zero coefficient. The whole probe family separates constants; a single
   probe need not do so.
4. Kähler differentials are relative to the coefficient field k, not to the
   ambient Hahn field K. The contractions agree functorially inside K.
5. Properness supplies the O-point. The ambient field is Frac(O); no false
   assertion that Frac(B)=K is used.
6. The forms are global and regular, so they remain regular at the valuation
   center, including a center at infinity. Rational forms with poles are not
   used in that step.
7. Global generation detects every induced tangent functional. Separation of
   constants then gives a k-point, and separatedness gives equality over B.
8. The curve argument separates genus >=1 from genus zero, and distinguishes
   one deleted geometric point from at least two. Forms of A1 descend in
   characteristic zero.
9. In the elementary proof, the squarefree Bezout identity puts Dx/y^(m-1)
   in B. Its negative degree is impossible. No UFD, gcd-domain, or divisible
   exponent-group hypothesis is hidden in that argument.
10. The arithmetic arc construction clears finitely many rational
    denominators; injectivity uses the supplied inverse parametrization over
    the fraction field of a characteristic-zero domain.
11. Projective coordinate constancy uses actual unimodularity witnesses.
    Absence of a common nonunit divisor is not substituted for them.
12. Full surreal-class assertions reduce each finite tuple and its finite
    witnesses to a set-sized exponent subgroup before applying scheme theory.
13. The characteristic-two infinite identity is coefficientwise Hahn
    algebra. Finite-prefix error monomials do not tend to zero in the
    valuation topology, so a false limiting argument is explicitly excluded.

## 5. Computational evidence

`verify.py` checks 3,440 exact assertions, grouped in `verification.json`.
These cover symbolic certificates, finite Euler identities and supports,
degree inequalities, finite congruences, singular parameters, and
characteristic-two finite telescoping. They are regression checks, not a
formalization or verification of arbitrary infinite series or geometry.

## 6. Status and unresolved boundaries

The proofs are supplied as an AI-assisted research draft. No theorem is
reported as independently peer-reviewed or Lean-verified. The targeted search
did not identify an identical principal Hahn theorem in the consulted
material; this does not establish historical novelty or priority.

The full generality of singular affine curves, higher-dimensional varieties
outside the stated hypotheses, and primitive non-unimodular Fermat tuples is
not resolved. There is no claim about every field-valued surreal point being
constant; explicit nonconstant field points can have forbidden negative
omega-power tails. Characteristic zero, constant coefficients, support
restriction, and projective unimodularity are substantive hypotheses.
