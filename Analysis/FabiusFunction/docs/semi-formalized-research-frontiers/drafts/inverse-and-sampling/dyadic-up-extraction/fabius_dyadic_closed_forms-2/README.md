# Recurrence-Free Dyadic Values of the Fabius and Rvachev Functions

Research article prepared for Vladimir Reshetnikov, 4 September 2026.

## Archive contents

- `fabius_dyadic_closed_forms.tex`: self-contained LaTeX source.
- `fabius_dyadic_closed_forms.pdf`: compiled, 26-page article.
- `verify_closed_forms.py`: exact-arithmetic evaluators and verification suite.
- `verification_results.json`: output from the supplied verification run.
- `README.md`: this file.

## Main results

The article gives exact, recurrence-free finite formulas for F(m/2^n) and
up(a/2^n), with complete proofs. Its principal formula uses floor(n/2)+1
centered finite-spline values with explicit rational interpolation weights at
q=1/4. Each spline value is an explicitly bounded integer Thue--Morse power
sum. The proof identifies an exact polynomial in 4^(-N), rather than an
asymptotic expansion. A local-cell identity, an exact-degree theorem, and a
sharp grid-wide sample-count theorem explain the extraction mechanism.

Other forms use binary block compression, positive ordered compositions,
finite Bernoulli multiplicity sums, or finite-prefix moment extraction.
A separate certified-rounding formula, direct Rvachev spline formula, signed
global extension, and integer-base analogue are also included.

The bounded Fabius distribution, Rvachev bump, and signed global extension
have explicitly distinguished normalizations. The integer-base extension
concerns a different family of functions, not values of the original Fabius
function at arbitrary rational points. No global priority claim or completed
Lean formalization is asserted.

## Build the article

A standard TeX Live or MiKTeX installation with the packages in the preamble
is sufficient. No external figures or BibTeX database are required.

    pdflatex -interaction=nonstopmode -halt-on-error fabius_dyadic_closed_forms.tex
    pdflatex -interaction=nonstopmode -halt-on-error fabius_dyadic_closed_forms.tex

The source uses Libertinus when available and otherwise Latin Modern.
A third compilation may be used if cross-reference warnings remain locally.
The delivered PDF was compiled without LaTeX warnings, and all 26 pages
were rendered and visually inspected. No font files are included.

## Run the exact tests

Python 3.10 or later, standard library only:

    python verify_closed_forms.py --max-depth 8 --output verification_results.json

The supplied run passed:
- 520 dyadic grid representations with denominator depth at most 8;
- 88 shifted-depth extractions;
- 1005 local-cell checks;
- 134 direct Rvachev spline/folding checks;
- 9 moment-coefficient comparisons (indices 0 through 8);
- 520 common-denominator checks;
- 17 exact rounding checks;
- 146 integer-base consistency checks.

Additional assertions test reflection, reciprocal-coefficient signs,
exact-degree nonvanishing, and polynomial annihilation by the weights.
The compact implementation printed in Appendix A was separately executed
and compared on every grid representation through denominator depth 6.

The test suite contains one explicitly labelled recursive moment oracle
for independent verification. None of the closed-form evaluators calls it;
it is not an input to any evaluation formula. The base-three and base-four
tests compare shifted extractions and reflection, rather than a separate
probability-law oracle. The proofs, not finite tests, establish the general
identities.

## Computational cautions

Use exact integers and fractions for the signed power sums. Large positive
and negative terms can cancel severely in floating point. Exhaustive tests
and fully expanded closed forms grow rapidly in cost with the depth;
the rounding construction is especially expensive. Reduce dyadic arguments
and exploit reflection or the binary formula for repeated calculations.

## Source scope

References and source URLs are embedded in the article. The linked ProveIt
document was consulted on its live main branch on 4 September 2026; this is
not a commit-pinned repository audit. Established moment identities and the
idea of binary reduction are explicitly distinguished from the derivations
and extraction statements developed in this article.
