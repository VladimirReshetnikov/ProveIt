# Asymptotic expansions of the Takeuchi numbers

Research report, 1 October 2026. The main deliverable is `takeuchi-asymptotics.pdf`; its editable source is `takeuchi-asymptotics.tex`.

## What the report establishes

Starting from Knuth's exact positive recurrence, the report gives full proofs of:

- A two-correction logarithmic asymptotic with error `O((1+W(n))^8/n^3)`
- A quantitative descending-chain stability theorem, using atomic endpoint-coupled smoothing blocks
- An arbitrary fixed-order asymptotic hierarchy, with canonically normalized coefficient functions computed by finite exact algebra and one convergent quadrature per order
- A common strictly positive normalizing constant defined by an exact limit
- An explicit third coefficient and sharper three-correction log error `O((1+W(n))^10/n^4)`
- Explicit inverse reversion with absolute error tending to zero, a controlled finite Newton hierarchy, real localization bounds, and rigorous ceiling brackets for the discrete threshold

The third coefficient has growth `p3(w) ~ w^4/72`. Thus the first two coefficients do not justify assuming `pj(w)=O(w^j)` at every order.

## Scope and limitations

This is a research manuscript with independent mathematical checking, not a peer-reviewed publication. The leading equivalent was already announced by Prellberg in 2002; higher formal coefficients were also already reported. No novelty claim is made for the displayed formulas, and the literature search is not proof of absence of another correction theorem.

The constant is not numerically enclosed. Historical decimal digits are used only in clearly labeled diagnostics. The report does not prove convergence of the infinite expansion, rationality of every coefficient, exponentially complete asymptotics, or unconditional exact rounding for arbitrary targets. A shrinking real-index error alone does not settle which side of a discrete threshold a target occupies.

## Files

- `takeuchi-asymptotics.pdf`: typeset report, with linked contents and references
- `takeuchi-asymptotics.tex`: complete self-contained mathematical source
- `code/derive_residual.py`: portable arbitrary-fixed-order exact residual generator; optional rational ODE solver
- `code/test_generator.py`: exact regression tests, including a symbolic-function triangular identity
- `code/check_independent.py`: independently organized fourth-order check and optional stored-data diagnostics
- `code/check_two_coefficients.py`: exact first- and second-coefficient derivation and cancellation
- `code/check_bell_comparison.py`: independently differentiated first three residual coefficients and Bell comparison identities
- `code/check_third_literal.py`: separate literal-formula check of H3, p3, and analytic growth degrees, importing none of the other checkers
- `replay.py`: one-command checksum verification and isolated computational replay, with optional PDF rebuild
- `code/check_inverse.py`: independent first-order inverse reversion, leading coefficient, and scaled derivative checks
- `code/check_numeric.py`: fresh exact recurrence integers and high-precision, non-certified diagnostics
- `receipts/`: actual symbolic/numerical run outputs, build log, mathematical review, and QA records
- `build.sh`, `requirements.txt`: reproduction entry points
- `SHA256SUMS`: digest manifest for the deliverable files

The distribution contains mathematical artifacts and reproducibility data only. It does not include conversation history or private personal notes.

## One-command replay

To verify every distributed checksum and rerun all symbolic and exact-recurrence checks without changing the delivered PDF or recorded receipts:

```sh
python3 replay.py
```

With a TeX distribution and a POSIX shell available, also rebuild the PDF in an isolated directory:

```sh
python3 replay.py --build-pdf
```

Replay results are written to a uniquely named directory under `.replay/`. The optional build also checks the page count and compares extracted layout text when Poppler is available; otherwise it explicitly records that those checks were unavailable. The separately differentiated Bell check can take a few minutes. PDF bytes may differ because of metadata and file identifiers; text equivalence is the reproduction criterion.

`SHA256SUMS` covers all distributed files except itself. Check it before modifying files; successful replay records the integrity result along with command exit statuses. The third-coefficient review and integrated mathematical review in `receipts/` are tied to the exact manuscript hashes.

## Reproduce the algebra

Python 3.10 or later and SymPy are sufficient; mpmath is used for the optional diagnostics. The recorded environment used Python 3.12.14 and SymPy 1.14.0. Install the requirements into an environment of your choice, then run from this directory:

```sh
python3 code/check_two_coefficients.py
python3 code/check_bell_comparison.py
python3 code/derive_residual.py --include-p3 --order 5 --output receipts/result-recomputed.json
python3 code/test_generator.py
python3 code/check_independent.py
python3 code/check_third_literal.py
python3 code/check_inverse.py
python3 code/check_numeric.py --max-n 1500 --output receipts/numeric-recomputed.json
```

The generator operates with exact rational expressions and finite Poisson polynomial moments. It can also accept general symbolic smooth coefficient functions, using SymPy's expression domain. It does not need a rational solution to exist: the report's quadrature is the general coefficient definition. The optional rational solver returns no solution when its specified ansatz is inconsistent or nonunique.

The order-five run confirms zero residual coefficients through order four after inserting `p1,p2,p3`, and computes the next nonzero residual. The numerical script constructs every sequence value used as an exact integer before evaluating logarithms. Its decimal constant is not a certified enclosure, so its small errors are checks of consistency only.

## Numerical consistency examples

A fresh exact recurrence computation gives these logarithmic errors when the historical decimal approximation to `C_T` is used:

- At `n=1000`: after two corrections, approximately `-3.1159408e-8`; after three, `-1.1301105e-10`
- At `n=1500`: after two corrections, approximately `-1.0533872e-8`; after three, `-2.4267707e-11`

These figures are reproduced in `receipts/numeric-recomputed.json` and are explicitly non-certified diagnostics. The proof does not depend on them.

## Rebuild the PDF

A complete TeX Live or MiKTeX installation with pdfLaTeX, Latin Modern, AMS packages, geometry, microtype, hyperref, xcolor, enumitem, and fancyhdr is sufficient:

```sh
sh build.sh
```

The document uses US Letter paper and embedded scalable fonts. No external figure files or bibliography processor are required. Cross-references and the contents are resolved with repeated pdfLaTeX runs. If a minimal read-only TeX installation contains the packages but lacks generated format files or font maps, the build script attempts to regenerate the required caches locally in `.build/`, without installing software or changing the TeX distribution.

For visual checking with Poppler:

```sh
pdfinfo takeuchi-asymptotics.pdf
pdftoppm -r 110 -png takeuchi-asymptotics.pdf page
```

Every page of the delivered PDF was rendered and visually inspected during report preparation. Intermediate render images and local TeX caches are not part of the distributable ZIP.

## Primary references

- Thomas Prellberg, *On the Asymptotics of Takeuchi Numbers* (2000): https://arxiv.org/abs/math/0005008
- Thomas Prellberg, FPSAC 2002 slides, *On the asymptotic analysis of a class of linear recurrences*: https://webspace.maths.qmul.ac.uk/t.prellberg/talks/recurrence.pdf
- Marni Mishna's summary of Prellberg's 23 September 2002 seminar, INRIA *Algorithms Seminar 2002–2004*, pp. 47–50: https://algo.inria.fr/seminars/summary/Prellberg2002a.pdf
- OEIS A000651: https://oeis.org/A000651

The report gives precise boundaries between the historical leading theorem, the earlier formal corrections, the new proof developed here, and remaining questions about effective constants and optimal truncation.
