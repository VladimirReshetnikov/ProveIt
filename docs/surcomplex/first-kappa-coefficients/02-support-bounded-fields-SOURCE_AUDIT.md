# Sources, proposed contributions, and proof audit

Date: 23 September 2026.

## Fixed repository baseline and actual review scope

Repository: https://github.com/VladimirReshetnikov/Surreal
Snapshot: 343dc2c471212bb9b53ff4623bace2e1943f255b

The following were retrieved through the connected GitHub interface:

1. Main recursive tree, to establish the snapshot and report inventory.
2. Root README.md.
3. docs/README.md.
4. Directory inventory for the holonomic-rigidity-for-entire-hahn-functions report.
5. Its 14-order-three-threshold-SOURCE_AUDIT.md, to avoid treating the
   already proposed universal second-order rigidity result as new.
6. docs/surreal/set-sized-quotients-of-omnific-integers/README.md.
7. docs/foundations-and-computation/surreal-fields-across-universes/README.md.

This is a targeted guide-level review, not a complete audit of every report,
source theorem, branch, or formalization file. A GitHub code search returned
an incomplete_results flag and is not used as evidence of absence.
The repository was not edited, and its full Lean build was not run.

## Public sources consulted

- Mantova and Matusinski, Surreal numbers with derivation, Hardy fields and
  transseries: a survey, arXiv:1608.03413v2. HTML inspected, especially
  normal forms, real closedness, and Theorems 2.15–2.16 on exponentiation.
  https://arxiv.org/html/1608.03413v2
- Kuhlmann and Shelah, kappa-bounded Exponential-Logarithmic Power Series
  Fields, Ann. Pure Appl. Logic 136 (2005), 284–296, arXiv:math/0512220.
  Abstract and HTML introduction/preliminaries inspected.
  https://arxiv.org/html/math/0512220v1
- F.-V. Kuhlmann, S. Kuhlmann, and Shelah, Exponentiation in power series
  fields, Proc. Amer. Math. Soc. 125 (1997), 3177–3183,
  arXiv:math/9608214. Abstract and bibliographic record inspected; attempted
  HTML full-text access failed. Only the stated classical theorem and
  general comparison mechanism are attributed to it.
  https://arxiv.org/abs/math/9608214
- Berarducci, Kuhlmann, Mantova, and Matusinski, Exponential fields and
  Conway's omega-map, Proc. Amer. Math. Soc. 151 (2023), 2655–2669,
  arXiv:1810.03029. Abstract and bibliographic record inspected.
  https://arxiv.org/abs/1810.03029
- Bournez and Guilmant, Surreal fields stable under exponential and
  logarithmic functions, arXiv:2201.08199. Abstract and bibliographic
  record inspected; not a full proof audit of that paper.
  https://arxiv.org/abs/2201.08199
- User-supplied Wikipedia surreal-number article: orientation only.
  https://en.wikipedia.org/wiki/Surreal_number

Conway and Gonshor's books are credited for foundational results accessed
through the Mantova–Matusinski survey, not represented as newly read in full.
No exhaustive MathSciNet, zbMATH, or subscription-literature audit was done.
Several targeted web searches returned irrelevant or incomplete results;
these cannot certify novelty.

## Contribution boundary

The proposed contribution is the specified proper-class hierarchy with
unrestricted surreal growth exponents, including singular support bounds,
and the following linked results:

- First-kappa-term classification of every set-presented omitted gap.
- Exact gap character and ordered-field saturation, including cf(kappa)=omega.
- Matching strong-sum and closed-ball-nest failure thresholds.
- Exp-closed fields admitting no surjective ordered exponential at all.
- A countably supported reservoir extending the prior universal quotient
  method to every support-bounded omnific integer part.
- An intrinsic no-forcing proper-class family of nonconjugate involutions,
  and pairwise nonisomorphic real integer parts with identical set targets.

The exact inherited exponential image and logarithmic hull collapse are
direct consequences of Gonshor's classical reindexing and monomial facts;
they are included with proofs and without strong independent priority claims.

Bounded Hahn fields, the general exponential quotient obstruction,
class back-and-forth, set-Cauchy stabilization, and the existence of
nonconjugate surcomplex real forms already have antecedents. In particular,
the repository's across-universes report has forcing-based real forms and
fresh-sign gap spectra. Its quotient report has constant-term universality
for full Oz and the scaled-field collision method. Neither is represented
as an original discovery here.

No named published conjecture is claimed solved. These are written proofs
of precise candidate contributions awaiting independent scrutiny.

## Sensitive proof checkpoints

1. Support cardinality is distinguished from birthday, exponent complexity,
   and arbitrary support order type. The first excluded ordinal prefix is
   the initial ordinal kappa.
2. The finite-tuple real-closedness proof lies in an ordinary set-sized Hahn
   field with a small divisible exponent group. It needs no regularity of kappa.
3. The first-outside-exponent lemma handles inserted exponents and zero
   coefficients; comparing term positions would not suffice.
4. Every set-presented omitted cut is filled first in full No, and a point
   outside F_kappa must reveal kappa terms. Class-cofinal gaps are not classified.
5. Cofinality bounds use cf(kappa), including when kappa is singular.
6. Saturation at cf(kappa)=omega is proved over finite parameter sets by a
   small exponent field, not inferred from filling finite order cuts.
7. Closed valuation balls fix coefficients at valuation strictly below the
   radius. The boundary coefficient is free.
8. Strong sums are not asserted to be topological limits. All set-indexed
   Cauchy nets stabilize because the value group has no set cofinal subset.
9. Taylor sums in one fixed support are controlled by a finite-sum monoid,
   not by an unjustified countable-union regularity assumption.
10. Any hypothetical onto ordered exponential can be normalized by
    E_2(x)=E(E^{-1}(2)*x). This proves finite-part compatibility without
    assuming compatibility with the ordinary real exponential.
11. The logarithm of a monomial has the same number of normal-form terms
    as its exponent by Gonshor's increasing reindexing. This gives the
    exact inherited image in Proposition 8.2.
12. The small-target proof uses a rational-expression reservoir, not a
    full Hahn field over an arbitrarily large exponent group. Each
    reservoir element has countable support.
13. The scaled collision identity uses no cancellation or reducedness
    in the target; noncommutative set rings are allowed as targets.
14. Real field isomorphisms preserve order by nonzero-squarehood.
    Complex field isomorphisms do not automatically preserve real forms.
15. The class back-and-forth has set-sized stages with fixed global choices;
    no class Zorn lemma or unrestricted class truth predicate is invoked.

## Verification limits

The exact program passed 31,672 finite checks. It uses only Python's
standard library and rational Fraction arithmetic. The checks are not
proofs of the transfinite statements. No new Lean theorem was compiled,
no independent peer review occurred, and no priority certification is made.
