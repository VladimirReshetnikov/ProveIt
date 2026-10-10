# Delivery validation

Date: 10 October 2026.

## Exact and symbolic replay

The final source passed `python code/verify_exact.py` and `python -O code/verify_exact.py`. Both receipts are retained. Checks include three defining polynomial identities, 1542 strictly positive rational Bernstein coefficients on 82 cells, a rejected corrupted-polynomial control, 528 independent finite Euler weight comparisons, 282 integer-certified rational power brackets, three axis enclosures, the certified maximum bounds, and the scaled-error counterexample.

The final `python code/verify_sympy.py` replay independently derived both low-index rational kernels and their positive certificates, checked the fourth binomial envelope, compared 13 generating coefficients with the recurrence, and verified the three explicit elementary moment identities and `g_{-3,1}=1+pi/4`.

Numerical comparisons were executed at 100 decimal working digits. The separate numerical report and JSON retain their diagnostic status. They do not certify floating-point quadrature or the numerical optimizers.

The three displayed decimal rows of the axis table were separately checked to lie strictly outside the stored exact rational interval endpoints in the appropriate direction.

## PDF build and review

The standalone article was built with `latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex`, reaching a stable reference state. The final PDF has 20 pages. The final LaTeX log reports no undefined references, overfull/underfull boxes, or warnings.

All pages were rendered with the PDF rendering helper and reviewed in two contact sheets. Full-size review included the title, the main error-moment theorem page, and the changed reproduction pages. A table-of-contents spill was corrected before the final build; the contents now occupy one page. The reproduction command block was kept together. PDF text bounding boxes were checked to remain inside page boundaries.

This validates the delivered standalone report, not the entire source manuscript or the proposed insertion in the source manuscript's separate reference environment.

## Proof status

This is a computer-assisted ordinary proof with exact finite arithmetic and independent symbolic replay. The gamma integrals, analytic continuation, asymptotics and differentiation arguments remain ordinary mathematical proofs written in the article. They were not verified in Lean or another proof assistant, and the report has not undergone external peer review.
