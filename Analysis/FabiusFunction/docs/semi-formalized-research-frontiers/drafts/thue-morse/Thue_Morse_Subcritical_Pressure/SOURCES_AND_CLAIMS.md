# Sources, claim boundaries, and validation

## Pinned repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Snapshot: `458ccfb80b9940220819091da107e82bb970dcca`

Inspected 29 September 2026 through the GitHub connector.

The immediate predecessor is:

`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/thue-morse/Thue_Morse_Critical_Pressure/article.tex`

Git blob: `c5491a93464668a8e20dd9afcda664a1c4b6cb81`

Its section on subcritical response proves the formula for 1/2<s<1. The
subsection explaining the s=1/2 cutoff and the first further-research
question explicitly leave 0<s<=1/2 untreated because the strong
norm-square remainder is not o(|c|). The Thue-Morse branch README was
also inspected to distinguish this gap from the earlier integer,
supercritical, and critical results. Those manuscripts are described
there as unreviewed; their mathematical assertions were not assumed
without proof in the present article.

## External primary sources

1. Philipp Gohlke, Marc Kesseboehmer, and Tanja I. Schindler,
   *Generalized Thue-Morse measures: spectral and fractal analysis*,
   arXiv:2509.22109 (2025).
   https://arxiv.org/abs/2509.22109
   https://arxiv.org/html/2509.22109v1
   Relevant material: pressure framework, atomic pressure, and Theorem 2.7
   on order-two phase analyticity.

2. Philipp Gohlke, Georgios Lamprinakis, and Joerg Schmeling,
   *On a family of singular potentials: Parameter dependence of
   thermodynamic characteristics*, arXiv:2603.19001 (2026).
   https://arxiv.org/abs/2603.19001
   https://arxiv.org/html/2603.19001v1
   Relevant material: Theorem 2.2 on nonnegative-order phase continuity,
   Theorem 2.3, and the immediately following stronger-regularity question.
   Their sine convention places the atomic phase at 1/2; the article's
   cosine convention places it at zero. Neither their global question
   nor arbitrary nonzero phases are claimed to be completely settled.

3. NIST Digital Library of Mathematical Functions, Chapter 5, section 5.5.
   https://dlmf.nist.gov/5.5
   Used for beta/gamma/digamma reflection evaluations; the singular
   translation integral itself is derived in the article.

The searches and comparison above establish a contribution relative to
these identified sources. They do not prove worldwide priority.

## Claim classification

Proved in this draft:

- All fixed-subcritical exponents 0<s<1, including 0<s<=1/2, with error
  O(delta^(1+s-alpha)) for every fixed 0<alpha<s.
- Independent-zero, fixed-leading-coefficient l1 cusp.
- One-zero and multizero weak expansions, with Dirac and principal-value
  terms and a quantitative remainder.
- An O(delta) left-functional bound, despite an order
  |c|*log(1/|c|) continuous-dual norm for common translations.
- Atomic exponential spectral relaxation and the polynomial
  pressure-versus-moment comparison needed for the main theorem.
- Uniformity on compact exponent intervals, finite-size operator
  scaling, and explicit amplitude 2*tan(pi*s/2)/(pi*s).

Not established here:

- A sharp next asymptotic coefficient or removal of all Holder loss.
- A theorem uniform as s tends to zero or one.
- General phase-neighborhood two-point Lipschitz regularity.
- Universality for arbitrary atomic masks, or a critical independent-zero
  law at s=1.
- Lean/Rocq formal verification, interval spectral certificates, or
  independently validated novelty.

## Computational validation actually performed

The packaged full run:

- Evaluated the independent singular integral at 65 decimal-digit working
  precision for s=0.1, 0.25, 0.5, 0.75, 0.9, with discrepancies below 1e-30.
- Checked the signed weak response on a nonconstant test function for
  both displacement signs, four exponents, and three phase sizes.
- Compared collocation on 262144- and 524288-point periodic meshes for
  three binary subcritical exponents and an opposite-zero-motion
  base-three example. Matrix residuals are recorded.
- Checked finite-size moment scaling and the two amplitude formulas.

Adaptive quadrature produced a roundoff convergence warning in the weak
response diagnostics. It is included in `data/run.log`; the JSON retains
its error estimates. The computation does not supply rigorous error
bounds for the continuum operator or any theorem-level certificate.

## Document checks

The final source was compiled with pdfLaTeX through latexmk, with all
cross-references resolved. The PDF was rendered and visually inspected,
including its main theorem, distributional estimate, and numerical
comparison tables. Build intermediates and font files are not distributed.
