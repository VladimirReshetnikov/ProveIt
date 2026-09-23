# Source, proof, and artifact audit

Date: 23 September 2026.

## 1. Repository comparison

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned snapshot: `bcac55ae6fd3f2b354e568ba1d2e94d496a2cc59`.

The connected GitHub tool was used to inspect the repository root, recursive
tree, main README, documentation catalogue, and the directory and README of
`docs/surreal/omnific-diophantine-geometry`. The decisive scope comparison used
these complete audit files at the pinned snapshot:

- `13-differential-rigidity-SOURCE_AND_PROOF_AUDIT.md`
- `14-hahn-differential-rigidity-SOURCE_AUDIT.md`

Both audits describe an existing smooth geometrically integral affine-curve
classification and explicitly leave arbitrary singular affine curves outside
its scope. The first audit also already describes symmetric-differential
rigidity and a nonnormal opposite-support ring. Those ingredients are not
presented as new in this package.

The very large assembled `article.tex` was not read in full. The work is not
an exhaustive audit of all repository statements, supplements, historical
commits, or Lean modules. The article's proofs are supplied independently
rather than relying on an uninspected repository proof.

## 2. Published primary inputs

### Seidenberg

A. Seidenberg, *Derivations and integral closure*, Pacific Journal of
Mathematics 16 (1966), 167-173. DOI: 10.2140/pjm.1966.16.167.

Original publisher PDF:
https://msp.org/pjm/1966/16-1/pjm-v16-n1-p16-s.pdf

The original Section 3, including printed pages 168-169, was inspected in
parsed text and as page images. Its finite identity and complete-integral-
closure argument are classical. The article re-proves the finite identity
using coefficient extraction in an independent formal variable.

C. Ciuperca, *Integral closure of strongly Golod ideals*, Nagoya Mathematical
Journal 241 (2021), 204-216, DOI: 10.1017/nmj.2019.22, Section 2.5, was also
consulted for the complete-integral-closure formulation.

### Algebraic geometry

The Stacks Project supplied the following primary references:

- Tag 0BXX and Tag 0BY3: curves, function fields, smooth projective models.
- Tag 035E: normalization.
- Tag 0BX5: valuative criterion for properness.
- Tag 0BS6: Riemann-Roch and duality for curves.
- Tag 0C6L: genus-zero curves and rational points.
- Tag 0C1B: Riemann-Hurwitz; Lemma 53.12.3 on local differentials.

The genus and ramification calculations are classical applications of these
results, not new genus formulas.

### Generalized power series and omnific integers

S. L'Innocente and V. Mantova, *A factorisation theory for generalised power
series and omnific integers*, Advances in Mathematics 442 (2024), 109513,
DOI: 10.1016/j.aim.2024.109513; arXiv:1710.07304, version 5, was consulted
for the modern primary literature and normal-form context. Conway and
Gonshor are cited for the classical background. No new result about the
remaining general factorization/refinement problems is claimed here.

### Nearby older curve literature

L. van den Dries, *Which curves over Z have points with coordinates in a
discrete ordered ring?*, Transactions of the AMS 264 (1981), 181-189,
DOI: 10.1090/S0002-9947-1981-0597875-5.

Only the bibliographic record and abstract were obtained and consulted.
The full proof was not compared. Consequently, this package makes no
priority claim or exhaustive implication comparison against that paper.

The user-supplied Wikipedia page was read for orientation, not used as a
substitute for a primary mathematical proof.

## 3. Contribution boundary

Prior/classical material:

- Hahn normal forms, the constant-term retraction, units, and Euler probes.
- The repository's smooth curve dichotomy and differential rigidity tools.
- Nonnormality of opposite-support rings at suitable non-Archimedean rank.
- Finite normalization, conductors, Riemann-Roch, and Riemann-Hurwitz.
- Seidenberg's finite derivation identity.

Proposed extensions, proved in the supplied article:

- A fixed conductor multiplier for all powers of a contracted differential.
- Positive-genus rigidity across arbitrary affine-curve singularities.
- The complete normalization-to-A^1 criterion for arbitrary geometrically
  integral affine curves over every characteristic-zero coefficient field.
- Finite derivative-order bounds in terms of a differential presentation,
  conductor pole order, and differential vanishing order.
- Finite birational invariance, scale independence, and the dimension-one
  reduced-component criterion.
- Repeated-root superelliptic consequences, the explicit singular elliptic
  seventh-order certificate, and omnific/Gaussian arithmetic consequences.

Targeted searches for combinations of Hahn series, singular curves,
omnific integers, and Seidenberg did not locate an identical combined
criterion in the consulted material. This is not evidence of an exhaustive
literature search and does not establish historical novelty.

## 4. Critical mathematical checks

1. Support orientation is consistent: t^gamma corresponds to omega^(-gamma).
   B has nonpositive t-support; it is not the valuation ring O.
2. B contains no nonzero element of positive valuation. Its nonconstant
   elements are transcendental over the constant field.
3. A nonconstant curve point induces an injective coordinate-ring map.
4. Normalization coordinates live initially in the curve function field F;
   the proof does not assume they belong to B.
5. A single nonzero conductor d clears every power of every normalization
   element. A greatest common divisor or principal conductor is not needed.
6. The Euler probe is chosen to be nonzero on the uniformizer valuation.
   The derivation is allowed to map F into K rather than into F.
7. Seidenberg's identity is used in the D-stable ring B. Its auxiliary formal
   variable is not evaluated as a surreal number or as a Hahn monomial.
8. The contraction certificate retains the actual fixed multiplier
   d^(2m+1), rather than invoking closure without quantitative control.
9. The restricted valuation on the one-variable function field is the
   discrete valuation at one point of the smooth projective model. This
   makes the valuation of the ORIGINAL conductor commensurable with the
   contracted differential's valuation, even when the ambient group has
   arbitrary rank. Positive valuation alone would not suffice at high rank.
10. Regularity of the global differential at infinity gives nonnegative
    vanishing order. The local differential du generates the cotangent
    module because the curve is smooth and the residue extension separable.
11. A second missing point is excluded by Riemann-Roch and the same
    conductor. This part does not need characteristic zero.
12. Descent from an algebraic closure uses geometric integrality,
    characteristic-zero smoothness, and the unique rational boundary point.
13. The existence theorem is not promoted into an unproved classification
    of every normalization fibre over B.
14. Gaussian arithmetic fibres use algebraic closedness of C. In the real
    singular case, an ordinary point need not have a real normalization
    preimage. The acnode obstruction is explicitly left as a boundary.
15. Full surreal assertions reduce each finite tuple to a set-sized ordered
    subgroup. Scheme theory is not applied to a proper-class spectrum.

## 5. Finite computation

`verify.py` was run successfully with Python 3.13.5 and SymPy 1.14.0.
The recorded run passed 113,940 assertions. Most consist of three checks for
each of 36,071 superelliptic multiplicity configurations, with m from 2
through 20 and one through three nonzero multiplicity residues.

Other tests cover exact rational and symbolic Taylor identities, polynomial
parametrizations and Bezout certificates, finite-support Hahn operations,
and finite valuation inequalities. The tests do not verify arbitrary
infinite series, normalization for arbitrary curves, or the universally
quantified geometric theorems. They do not certify historical priority.

## 6. Typesetting and package integrity

The final article has 20 pages. Repeated pdfLaTeX compilation resolved its
cross-references and citations. The final log contains no LaTeX warnings,
overfull boxes, or underfull boxes. The PDF was rendered to page images;
a full-document contact sheet from an earlier layout and selected final
pages, including the contents, Seidenberg identity, central proof, and
bibliography, were visually inspected. Auxiliary build files and rendered
page images are not included in the release ZIP.

The SHA-256 manifest checks package-file integrity only. Neither a clean
build, the checksums, nor the finite computation is a substitute for
independent mathematical review or formal verification.
