# Integration guidance

Suggested report directory:
`Analysis/Polylogarithms/docs/reports/ordered-jet-normal-forms/`

Copy the package there, retaining `manuscript/article.tex`, the compiled PDF, code, data, and provenance. The root Makefile can rebuild from that location without changes.

The fragment `ordered-jet-normal-forms.tex` is self-contained at the level of notation and uses the existing `theorem` and `proof` environments, plus ordinary amsmath notation and the blackboard-bold alphabet provided by amsfonts or the manuscript math font package. It introduces no macros and no bibliography keys. Its labels all begin `ojnf:`. An optional insertion in the integration/differentiation chapters is:

```tex
\input{../reports/ordered-jet-normal-forms/integration/ordered-jet-normal-forms}
```

This path assumes compilation from `Analysis/Polylogarithms/docs/manuscript`, as in the repository manuscript entry point. An editor may instead copy the fragment into `chapters/` and adjust the input path.

## Research-programme replacement

Replace the predecessor's specific question asking for depth-four permutation components of the lower-depth regular jets with a status paragraph:

> The formal depth-four orientation quotient is now explicitly the standard S3 component plus the sign S2 component, of total dimension three. The full ordered finite part has a rational normal form and a three-positive-ray reconstruction. At arbitrary depth d, the specified rational linear quotient has dimension 2^(d-1)-p(d). Arithmetic evaluation kernels, nonlinear scalar extensions, and extra analytic relations remain separate questions.

Do not replace the open question asking for reduction of orientation values into a smaller named arithmetic algebra. Do not promote the quotient dimension to arithmetic independence or to rank after scalar extension. The all-index contact coefficient in the commutator identity is essential.

## Proof and verification status

The article supplies ordinary mathematical proofs. The accompanying checker verifies finite integer/rational identities, not formal analytic proofs. Numerical output is a regression record, not a certified enclosure. The incoming archive inventory was partial and was not exhaustively unpacked. No remote files were modified.
