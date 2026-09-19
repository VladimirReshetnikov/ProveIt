# Research status and source audit

Date of research: 19 September 2026.

## Claim being made

The attached manuscript contains an all-index algebraic proof of the bilinear
identity in Barry's Conjecture 7 (arXiv:2211.12637v1), with a homogeneous
extension. The proof is intended to be complete. It has not been independently
refereed, published, or checked in Lean or another proof assistant.

The principal genus-two continued-fraction identity is an established theorem
of van der Poorten. Identifying it as an ingredient is not a novelty claim.
The note's contribution is the specific reduction, normalization, explicit
polynomial deformation and specialization, and application to Barry's formula.

## Literature consulted

1. Paul Barry, *Conjectures on Somos 4, 6 and 8 sequences using Riordan arrays
   and the Catalan numbers*, arXiv:2211.12637v1, 22 November 2022.
   https://arxiv.org/abs/2211.12637
   The actual target is Conjecture 7, printed page 7. The PDF formula and the
   neighboring examples were visually checked, not inferred from snippets.

2. Alfred J. van der Poorten, *Curves of Genus 2, Continued Fractions, and
   Somos Sequences*, Journal of Integer Sequences 8 (2005), Article 05.3.4.
   https://cs.uwaterloo.ca/journals/JIS/VOL8/Poorten2/vdp89.pdf
   Theorems 3.1 and 3.2 provide the relevant generic local identity. The source
   explicitly notes the generic/nonzero issue and allows the full cubic A(X).
   The manuscript's polynomial extension does not assume the source settled
   arbitrary singular initial-value problems.

3. Andrew N. W. Hone, *Continued fractions and Hankel determinants from
   hyperelliptic curves*, Communications on Pure and Applied Mathematics 74
   (2021), 2310--2347. https://arxiv.org/abs/1907.05204
   Section 4 and Theorem 4.1 supply context for the determinant correspondence;
   the normalization and its proof are made explicit in the manuscript.

4. Ying Wang and Zihao Zhang, *Sufficient condition for (alpha,beta) Somos 4
   Hankel determinants*, Discrete Mathematics 347 (2024), 113937.
   https://arxiv.org/abs/2305.05995
   The preprint's Corollaries 4--7 explicitly prove Barry's Conjectures 2--5,
   not the Conjecture 7 selected here. The original v2 date is 15 June 2023;
   the regenerated HTML's displayed compilation date was not used as the
   publication date.

5. Xiang-Ke Chang and Jiyuan Liu, *Hankel Determinants from Quadratic Orthogonal
   Pairs for Hyperelliptic Functions and Their Applications*.
   https://arxiv.org/abs/2603.11670
   The abstract/version record was checked through v4 (29 April 2026); the
   stated applications are to bilateral Somos-4 and Somos-5. Earlier v1 text
   was also inspected during target selection. No claim is made of a complete
   audit of all implications of this recent paper.

6. Thomas Scheuerle, *Direct Generation of a Somos-4 Sequence from an Algebraic
   Generating Function*, arXiv:2609.15754v1, 14 September 2026.
   https://arxiv.org/abs/2609.15754
   The current abstract concerns Somos-4, not the stated three-parameter
   Somos-6 conjecture.

Targeted searches included Barry's title, arXiv identifier, Conjecture 7,
Hankel/Somos-6 proof terms, and recent related work. No earlier direct
resolution of the selected conjecture was located. Some searches returned
irrelevant results, which were not treated as evidence. This bounded search
cannot rule out an unpublished proof, an obscure source, or an equivalent
result expressed in different notation. The source's use of "conjecture"
is verified; a global priority/open-status guarantee is not being made.

## What has been checked computationally

- 1,128 parameter cases, 10,248 exact zero recurrence residuals.
- All determinant values generated directly from moment matrices.
- 553 cases with zero Hankel determinants; no exclusion of singular cases.
- 84 small determinant checks against the permutation formula.
- 343 independent checks of the original moment recurrence.
- 25 interleaved-Catalan Hankel determinants equal to 1.
- 5 additional examples through H_20, adding 75 recurrence checks.
- 16 exact symbolic algebra certificates, including the coefficient identity.

The local identity, the generic nonvanishing argument, and the passage from
fraction-field equality to an integer polynomial identity constitute the
proof. Finite computations are an audit, not an extrapolation to all n.

## Important scope limits

The polynomial identity handles this determinant family's zero specializations.
It does not give uniqueness for arbitrary singular Somos initial values.
It does not resolve the source's Somos-8 conjectures or classify all Somos-6
sequences. Integrality follows from integer moments and determinants, not from
a newly asserted general Laurent-phenomenon result.
