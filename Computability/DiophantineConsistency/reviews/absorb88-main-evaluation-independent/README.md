# Independent review of the 88 evaluated main expression

On 2026-11-04 an independent reviewer inspected
[`Absorb88MainEvaluation.lean`](../../research/ordinary12-absorb88-main-evaluation-draft/Absorb88MainEvaluation.lean),
the referenced `Absorb89Main.mainParts` definition, and the checked
negative-branch orientation statement. No mismatch was found in the
expression equality or its positivity corollary. This is a source review;
no fresh Lean run was performed.

The evaluated main part is `W*b0 + H*shift`, with `W = Yq²`,
`b0 = X + a(eta + Yk)`, and
`shift = W*direct − (k − rank − 1)`. Thus the displayed expansion in
`main_expression` has the correct signs and factors. Its proof unfolds the
expression evaluator, natural-port and variable embeddings and normalizes
the resulting ring expression. The referenced main-root packet also states
the shared 88/89 main residual and the main-part shape; this review does not
replay those imported proofs.

The positivity corollary uses the same port tuple and valuation as the
equality, explicitly requires a positive 88-graph zero, positive `beta` and
the negative-transport inequality, and applies the prior expanded-expression
theorem after rewriting. The source and README do not claim an oriented Pell
balance, transport normalization, reverse 88/89 existence or an iPRA
endpoint. The author's check uses temporary providers whose complete
source/object, package, dynamic and search-path ancestry is not independently
authenticated by this review.

Reviewed source SHA-256:
`f717eb3391260c50d3a6abd2495d4b86ffa9cacb71767ed281c1f0cffffca6e4`.
The referenced `Absorb89Main.lean` SHA-256 was
`4aee0b74a59231e6d665909cd134dbf4f3332fb3a4d06dde43e6437b941a604f`.
