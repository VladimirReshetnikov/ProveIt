# Source, novelty, and proof audit

Date: 22 September 2026
Repository: https://github.com/VladimirReshetnikov/Surreal
Snapshot: 465a54b479a1ee842cbf7db1689a7d2f6bfe25e1

## Inspected repository evidence

The root README and docs/README.md were read to identify existing coverage.
The following detailed READMEs were then inspected at the pinned snapshot:

1. docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/README.md
   This explicitly records first-order nonlinear rigidity, a higher-order
   nonzero-residue-corner criterion, the remaining Question 19.1, mixed
   Question 19.4, and the example sum omega^(-omega^n) z^n. A focused reread
   of original README lines 131-182 confirmed the stated boundary.
2. docs/surreal/tail-spans-and-differential-transcendence/README.md
   This records earlier all-order results for other coefficient fields and
   derivations. The new manuscript does not claim to originate those
   constructions or conflate their scalar derivations with formal d/dz.

The catalogue identified the foundations and entire-functions-at-arbitrary-rank
reports. They are cited as background and provenance. Their full text was not
needed as an unproved premise for the entireness criterion: that criterion is
proved directly in this manuscript. No exhaustive review of all reports,
Lean declarations, or repository history was performed.

## Primary external sources

Jason P. Bell, “A generalised Skolem-Mahler-Lech theorem for affine varieties,”
arXiv:math/0501309v2.
https://arxiv.org/html/math/0501309v2
The exact general-characteristic-zero-field form of classical SML was read
in Theorem 1.1. Only that classical theorem is imported, not Bell's affine
variety generalization. The nondegenerate exponential-polynomial corollary
and the formal coefficient-field deduction are proved in the article.

Christer Lech, “A note on recurring series,” Arkiv för Matematik 2 (1953),
417-421. DOI: 10.1007/BF02590997.
Publisher metadata was checked. The original proof was not independently
reconstructed. Bell supplies the inspected explicit theorem statement.

Pei-Chu Hu and Yong-Zhi Luan, “Non-Archimedean meromorphic solutions of
functional equations,” arXiv:1311.5291v1.
https://arxiv.org/html/1311.5291v1
The field assumptions and the scope of the introduction were read. This is
context for non-Archimedean function theory, not a premise of the new proof.

Olivier Bournez and Quentin Guilmant, “Surreal fields stable under exponential
and logarithmic functions,” arXiv:2201.08199v1.
https://arxiv.org/html/2201.08199v1
Section 2.3, especially Corollary 2.7, gives the classical normal-form
identification with the convention t^a -> omega^(-a). This is an imported
foundational identification, not an original contribution of the manuscript.

## Proposed additions, rather than certified priority claims

- All-order nonlinear differential rigidity for strongly entire functions
  over no-order-unit Hahn groups, without a residue-corner assumption.
- Joint algebraic independence of all derivatives at non-torsion-related
  dilations, over the entire Hahn scalar field K(z).
- Infinite coefficient-value-rank criterion, including a rank-one example
  with exponents tau^n for transcendental real tau > 1.
- A sharp order-unit equivalence for finite-transcendence-degree coefficient
  containers and failure of universal mixed-jet independence.
- Explicit comparison between persistence of formal independence under
  constant extension and loss of entireness under a new dominating scale.

Finite-generation methods, valuation rank versus transcendence degree,
Hahn/Neumann support theory, the SML theorem, partial theta, and the Conway
normal-form construction are not advertised as newly discovered here.
The searched formulations were not found in the targeted materials. That is
not an exhaustive MathSciNet/Zentralblatt/citation-network novelty audit.

## Logical dependency checks

1. Minimum total degree in jet variables makes all nonzero polynomial
   partials evaluate nontrivially.
2. The first-variation offset ell may be negative. One needs n >= r and
   n > ell + 2r before discarding the quadratic Taylor remainder.
3. Differentiation BEFORE dilation gives (n)_j lambda^(n-j).
4. Falling factorials are polynomially independent in characteristic zero.
5. Pairwise non-root-of-unity quotients rule out arithmetic progressions of
   zeros in the exponential-polynomial multiplier.
6. Only finitely many equation and initial-jet coefficients are required to
   generate the field containing every coefficient of the solution.
7. Rationally independent leading values give algebraically independent
   scalars over the trivially valued coefficient field k.
8. A finite-rational-rank subgroup has a principal convex bound. No order
   unit makes this bound proper.
9. At an exterior argument the leading values strictly decrease. This is
   a failure of the definition of strong summation; imagined cancellation
   of an undefined sum does not fix it.

## Verification boundary

The delivered verify.py completed 9,308 exact finite checks. It uses only
Python's standard library. The tests cover coefficient identities,
linearization multipliers, finite exponential-polynomial annihilators, and
finite ordered-group comparisons. They do not prove any infinite theorem.

No main result was compiled in Lean, independently refereed, or certified
by a computer algebra system as an infinite statement. The proofs are
complete written arguments relative to the explicitly cited classical
inputs. The remaining general pure-differential order-unit case is not
claimed solved.
