# Recurrence-Free Closed Forms for Dyadic Fabius and Rvachev Values

## Contents

- `fabius_dyadic_closed_forms.pdf`: the complete article.
- `fabius_dyadic_closed_forms.tex`: self-contained LaTeX source, including bibliography and core evaluator.
- `verify_formulas.py`: standard-library exact rational implementations and cross-checks.
- `verification_output.txt`: recorded output from a successful verification run.

## Build the article

With a standard TeX Live or equivalent installation:

    latexmk -pdf fabius_dyadic_closed_forms.tex

Alternatively, run `pdflatex fabius_dyadic_closed_forms.tex` twice (a third run may
be required after the initial table of contents changes the page count).
No external bibliography, figure, or font files are required.

## Run the exact checks

Python 3.10 or later; no third-party packages:

    python verify_formulas.py

Import for evaluation:

    from fractions import Fraction
    from verify_formulas import fabius, up, global_fabius
    print(fabius(Fraction(5, 16)))       # 305857/2073600
    print(up(Fraction(11, 16)))         # 305857/2073600
    print(global_fabius(Fraction(3)))   # -1

Use exact Fraction inputs. The bounded Fabius distribution `fabius` is clamped
to zero and one outside [0,1]; `global_fabius` is the signed extension. `up` is
supported on [-1,1]. These are different functions outside their common interval.

## Mathematical scope

The article supplies positive composition and cumulant-partition coefficients,
a binary-compressed dyadic formula, finite-prefix multinomial formulas, an exact
quarter-base spline double sum, and a bordered determinant/permutation formula.
All evaluation definitions are finite and recurrence-free. A separately isolated
recurrence is used only as a validation oracle in the verification program.
The proofs are mathematical, not newly Lean-formalized. Related ideas in the
linked ProveIt repository and prior literature are acknowledged in the article;
no exhaustive novelty or priority claim is made.

Verification includes 1033 bounded dyadic representations through denominator
2^9, 388 signed-global representations, normalized moments through index 12,
finite-prefix moments, Gaussian filters, refinement and reflection, determinant
comparisons through denominator 2^6, and selected exact spline scale laws.
The elapsed time in the recorded output is environment-dependent.
