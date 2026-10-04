# The Baker–Campbell–Hausdorff Formula
## Complete Expansions, Proofs, and Analytic Qualifications

The 44-page paper supplies proofs for the mathematical formulas and explicitly
stated results on the Wikipedia BCH page, using the fixed revision 1368909113
(accessed 16 September 2026). Appendix C is a claim-by-claim concordance.
Assertions that need qualifications are treated as corrected statements with
proofs or counterexamples, rather than repeated without their hypotheses.

## Contents

- `paper.pdf`: the complete typeset paper, with linked contents and references.
- `paper.tex`, `tex/*.tex`: all LaTeX sources, including the bibliography.
- `code/verify_bch.py`: exact sparse noncommutative algebra over rational numbers.
- `code/make_tables.py`: generates the printed coefficient-certificate appendix.
- `data/*.csv`: BCH, Zassenhaus, symmetric-splitting, and Bernoulli coefficients.
- `data/verification_report.json`: the actual finite verification results.
- `data/provenance.json`: the source revision and scope information.
- `build.py`: a portable paper-rebuild helper.

## Mathematical scope

The derivations include the primitive-element theorem, the Dynkin projection,
the full associative-word coefficient formula, Dynkin's complete commutator
series, the Poincare integral, Bernoulli recurrences and partial fractions,
all orders in the number of occurrences of Y, an explicit quadratic-in-Y
kernel, and a finite-at-each-order analytic recurrence at any regular fixed X.

Analytic results distinguish formal identities, convergence of a specific
series, and global identities after resummation. The paper includes explicit
remainder estimates, a classification of all logarithms in the source's sl2
counterexample, central and eigenvector commutator identities, all-order
Zassenhaus recurrences with a convergence majorant, and product-splitting
expansions. Geometry is developed through complete coframe, metric, and volume
formulas. Weyl and displacement identities are proved in concrete Hilbert-space
representations, with the domain issue for unbounded operators made explicit.

In particular, the coframe matrix is W = (1-exp(-ad_X))/ad_X interpreted as an
entire function, not ad_X itself. A Killing form can be degenerate, and a
pullback tensor need not be a metric. A canonical commutator on an arbitrary
dense invariant domain alone does not imply exponentiated Weyl relations.

Theorems merely named in the source's links, without being stated there, are
not additional proof obligations. The paper nevertheless derives Trotter and
arbitrarily high-order symmetric splitting formulas as additional consequences.

## Regenerate the data and run the exact checks

Python 3.9 or later is sufficient; no third-party Python packages are required.
From this directory run:

```text
python code/verify_bch.py --degree 12 --check-degree 10
python code/make_tables.py
```

The supplied run has 30 passed checks. Expansions and reconstructions extend
through degree 12. Independently organized word-cut, Poincare, primitive
coproduct, Dynkin-projection, quadratic-kernel, and dual Zassenhaus-construction
checks extend through degree 10. The report specifies the degree for each check.

These are exact finite algebraic checks, not floating-point sampling. They
support the explicit coefficient tables and detect transcription errors;
the paper's all-order proofs do not depend on extrapolating from finite tests.
No proof-assistant certification is claimed.

## CSV conventions

Except for the Bernoulli file, each row has:

```text
degree,word,numerator,denominator
```

In an associative file, a word means literal multiplication. In a `lyndon`
file, it means the standard recursively bracketed word L(w), with alphabet
X < Y and the longest proper Lyndon suffix convention. In the
`right_commutators` file it means R(w) = [a1,[a2,...,[a(n-1),an]...]].
These conventions must not be interchanged: R(XYY)=0, whereas
L(XYY)=[[X,Y],Y]. Missing coefficients are zero.

The right-commutator table is a redundant Dynkin-projection representation,
not a basis. Its coefficients are associative coefficients divided by the
degree. Rows for identically zero right brackets are omitted. All exported
Lyndon expansions are reconstructed and compared exactly with their
associative polynomials.

The Bernoulli data contain b_n = B_n^+/n!, with B_1^+ = +1/2, not B_n itself.
The other convention with B_1 = -1/2 is discussed in the paper.

## Rebuild the PDF

A TeX installation with the packages in `paper.tex` is required. Either run:

```text
python build.py
```

or, to regenerate and verify the data first:

```text
python build.py --verify
```

The helper uses `latexmk` when available, or runs `pdflatex` three times. It
places temporary files under `.build/` and copies the resulting PDF to
`paper.pdf`. A direct equivalent is:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
```

No external bibliography database, external figures, downloaded reference
papers, or separately supplied font files are needed. The prebuilt PDF is
included for immediate reading.
