# Proposed manuscript integration

This is an integration proposal for the source revision
dcd95baeb7c0e914b138bddef6829c5b1d52b726. The repository was read only.

## Section dependencies

| Source section | Recommended role | Required mathematical input |
| --- | --- | --- |
| 02_cubic.tex | Extension of the coincident Stieltjes chapter | Hurwitz shift relation, local Taylor subtraction, Hurwitz Fourier expansion |
| 03_contacts.tex | Completion of the distributional collision discussion | Periodic Hurwitz continuation and argument-derivative contact law, restated in its proof |
| 04_coordinates.tex | Follow-up to nonlinear coordinate transport | The incoming finite residue law, with local justification reproduced |
| 05_spectral.tex | Exact normal spectral derivative section | Colored Tornheim and nested-polylog conventions defined in the section |
| 06_rays.tex | Spectral direction appendix or Tornheim subsection | The diagonal second derivative from 02_cubic.tex and a local Mellin decomposition |
| 07_harmonic.tex | Extension of fully shifted height-one Laurent data | Gamma-ratio asymptotics and the inherited finite Stirling specialization, both explained |
| 08_audit.tex | Editorial audit | Pinned source paths and the inspected author PDFs |
| 09_research.tex | Proposed further research | The exact theorem boundaries from the article |
| 10_verification.tex | Verification appendix | Reproducible scripts and JSON results |

All theorem and equation labels are namespaced. The article uses the
standard theorem, proposition, lemma, corollary, and remark environments.
The FP macro is declared as an operator in article.tex.

The cubic section must precede the ray proof unless the diagonal lemma is
moved to a shared preliminary section. The proof has no dependence on a
numerical value of the cubic finite part: its residue alone determines
the second Tornheim derivative.

## Status that must be preserved

The exact generators and coefficient formulas in the claim ledger are
proved in the supplied article. Historical priority beyond the audited
corpus is not claimed. The following limitations are material:

- The cubic digamma integral is reduced to a third diagonal Tornheim
  derivative, whose reduction to ordinary constants remains open.
- The positive-inner-order colored answer is generally in depth-two
  polylogarithms; the all-nonpositive weighted sector closes at depth one.
- Derivatives in a fixed integer parameter do not follow from an identity
  valid only at that integer.
- The harmonic theorem moves exactly two exponents and keeps the trailing
  exponents equal to one. Its general formula stops after the finite part.
- S6 and the current S8 remain conjectures.

## Correction patch

The included carry_forward_source_corrections.patch passed a dry-run
against the pinned revision. It has not been applied.

It changes only:

1. The logarithm of a real half-angle tangent to the logarithm of its
   absolute value where the stated real parameter range includes negative values.
2. An unsupported non-elementary description attached to an exact value.
3. The scope of the quadratic-character coefficient field.

These findings were already present in the earlier incoming Twisted
Stieltjes report and are explicitly credited. The superseded PSLQ
wording correction is excluded because it is already integrated.

The Borwein–Dilcher and Bailey–Borwein author-PDF corrections belong in a reference or
implementation note, not in a patch that pretends to modify an external
publication.

## Review and verification

The independent review notes describe which local proofs and coefficients
were checked by a separate analysis. They are not substitutes for the
proofs. All numerical results are labelled diagnostics. Exact checks
operate on finite algebraic expressions, rational rows, or integer
coefficient data.

Build commands and the complete replay command are in the package README.
The flattened TeX source compiles in isolation. SHA256SUMS records the
final package contents, excluding itself.
