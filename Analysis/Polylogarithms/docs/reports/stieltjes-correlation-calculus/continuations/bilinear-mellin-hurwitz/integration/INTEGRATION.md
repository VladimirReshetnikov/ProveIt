# ProveIt integration notes

## Intended relationship

This is a continuation of

`Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/mellin-lerch-dilation/`.

A suitable local report destination is a `bilinear-mellin-hurwitz/`
continuation folder, subject to the repository's intake classification.
Preserve the delivered article, source, code, and run records before editing
canonical text. Do not run scripts in place when comparing delivered bytes.

## Source pin and question

Delivery pin: `b1df802799851c62a860570c3ac78ee31b9f5c04`.

The prior question is the tenth item in
`sections/06-audit-research.tex`, headed
“Products of polylogarithms under the Mellin kernel.” Its blob is
`c0e3d58e42005ca844ca8b6900d7feaf1b33e2f8`.

Suggested replacement status paragraph:

> For positive integer polylogarithm orders, integer Mellin parameters on the
> full product convergence strip admit constructive finite multiple-
> polylogarithm expressions. The bilinear Mellin–Hurwitz continuation gives
> the explicit alphabet and a residue-weight law. At unit scales it also
> gives a finite double-Hurwitz master, every logarithmic moment at a=0,-1,
> and a terminating recurrence for all admissible integer parameters and
> denominator orders. The extension to arbitrary complex spectral orders
> and the question of arithmetic minimal depth remain separate research
> problems. This result does not change the status of the Gaussian S6/S8
> conjectures.

Do not mark all of Q10 solved: its arbitrary-order and minimal-depth parts
are not proved here.

## Canonical placement after analytic review

- Integration chapter: convergence, finite alphabet, connected master,
  both resonances, integer-kernel recurrence, and Gamma/harmonic base.
- Depth chapter or exact-sums subsection: binary primitives and the
  weighted multiple-zeta identity, with the distinction between a specific
  weighted reduction and a general depth theorem retained.
- Differentiation/integration chapter: Stieltjes order jets, discrete shift
  primitive, and continuous adjacent-index primitive.
- Research chapter: the revised Q10 scope plus selected new questions.

All theorem and equation labels in the article begin `bmh:`. The standalone
preamble defines prefixed macros `bmhC`, `bmhK`, `bmhH`, and `bmhM` for the
new connected and transform objects. This avoids a verified collision: the
canonical preamble already uses `CC` for the complex numbers. Reuse the
canonical definitions of standard macros such as `Li`, `Rea`, and `dd`
instead of loading a second article preamble. In
particular, keep the article's explicit semicolon convention for Hurwitz
zeta or rewrite it consistently to the manuscript's chosen notation.

## Reproduction and claims

`verify_exact.py` is a finite replay, not a proof-assistant formalization.
`verify_numerics.py` is an independent diagnostic suite, not a certificate
that arbitrary real constants are equal. The analytic proofs must remain
with the integrated statements. The exact identity catalogue can be
regenerated with `export_tables.py`; stored formula strings are not used
as axioms by the verifiers.

No files were pushed, committed, or overwritten in the user's repository.
The source pin and audit scope must be preserved even if main advances.
