# Source audit and evidentiary limits

## Repository snapshot

Pinned current reading: `b7667ae40a2957eed9a53d8559d53a3ee20dd1c1`.
Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected through the connected GitHub tools:

- `Analysis/Polylogarithms/docs/manuscript/README.md` (full accessible text).
- `Analysis/Polylogarithms/docs/manuscript/chapters/05-logistic-resolvent-identities.tex`
  (full accessible text; beta density, divided differences and logarithmic moments).
- Manuscript/chapter tree and incoming-directory metadata.
- Relevant visible portions of `docs/incoming/README.md` (intake and placement rules;
  the tool's large single-line response was truncated, so it was not a full audit).

The incoming ZIP archive names were visible, but their binary contents were not
read in full. Do not infer that every incoming report was reviewed.

## Accessible preceding report

`ProveIt_Reciprocal_Lerch_Convolutions_2026-10-10.tex`, an accessible user-Library
source, was read for its transform/weighted-holomorphy proofs, integer-depth
convolutions and central-factorial kernels, Stieltjes products and harmonic
coefficients, and research question 10 in Section 12. Specific main ranges
read included source lines 199–540 and 786–930, together with retrieved research
question passages near lines 1652–1750. The file has 1,825 source lines.

That report's own source pin is
`0c740647c48baec7f0b4192723e977d69917dd52`.
This older pin is NOT the pinned current GitHub snapshot above. No claim is made
that the Library copy is byte-identical to a currently listed incoming archive.

The report explicitly asks for a real kernel and special-function expression
for g(p)^rho(p+a-1)^(-W) at noninteger rho, and asks that any finite-closure
obstruction specify its target class. This delivery addresses that request.

Introductory Library snippets of the commensurate-Lerch continuation were used
only to avoid duplicating its scale/unequal-center agenda; its full proofs were
not inspected and are not certified here.

## External primary sources consulted

- D. Chakrabarti and G. K. Srinivasan, *On a remarkable formula of Ramanujan*,
  arXiv:1206.5122 (2012), including Theorem 1.1 in the HTML full text.
  https://arxiv.org/abs/1206.5122
- W. Schoutens, *The Meixner Process: Theory and Applications in Finance*,
  EURANDOM 2002-004, Section 2. Printed pp. 5–6 were visually inspected to verify
  the Gamma density, parameter scaling, and characteristic function.
  https://www.eurandom.tue.nl/reports/2002/004-report.pdf
- NIST DLMF 5.12 (beta), 5.7 (Gamma expansions), 5.15 (polygamma), 25.14 (Lerch),
  and 25.11 (Hurwitz zeta).

The Gamma Fourier transform and the normalized Meixner convolution semigroup
are classical. The source search was not an exhaustive review of all Euler-sum,
hypergeometric, or generalized-Lerch literature. No blanket claim of historical
novelty is made for the coefficient master or every low-weight consequence.

## Error audit

No incorrect formula was established in the inspected source proofs. In
particular, the integer-depth central-factorial and symmetric Stieltjes formulas
are recovered rather than contradicted.

The new article states extension safeguards explicitly: the Gamma PRODUCT for
complex rho; nonzero negative-order resonances; pole-zero cancellation before
substitution; holomorphic continuation before depth differentiation; the extra
zeta(3,a) term at unequal continuous splits; and a specified rather than universal
finite-closure obstruction. These are not fabricated errata against prior text.

## Proof and computational status

All principal assertions have conventional analytic/algebraic proofs in the TEX.
No proof-assistant kernel certification, interval error certification, or
independent refereeing is claimed. Floating-point diagnostics are separately
labeled. The delivery includes 241 exact finite assertions, 3 negative controls,
and 88 independent-form numerical comparisons; none is presented as a substitute
for the infinite-parameter proofs.

No original repository, incoming archive, shared file, or persistent Library
entry was edited. The package is ready for additive human-reviewed intake.
