# Dyadic descaling and delayed Pell sign recovery

Prepared for Vladimir Reshetnikov on 23 October 2026, with ChatGPT research,
implementation, and a separate AI-assisted proof review.

Start with `report/report.pdf`; `report/report.tex`, `report/dyadic.tex`, and
`report/direct.tex` are the editable LaTeX sources. Two complete fixed
polynomials are supplied.

| Equation | Domain | Unknowns | Exact degree | Further size |
|---|---|---:|---:|---|
| Dyadic norm | Strictly positive integers | 10 | **706** | **133 binary operations** |
| Direct certificate quartic | Unrestricted integers | **780** | **4** | **9,628 monomials**, coefficient height **2,445,790,974,704** |

Each zero-existence statement is equivalent to finite syntactic ZFC
refutability through the explicit inherited calibration stated in the
article. Negating gives the requested equivalence of unsolvability and
Con(ZFC). The new transformations have ordinary mathematical proofs
formalizable in ZFC. No new end-to-end Lean/Rocq or exported object-language
ZFC certificate is claimed.

## What improved

The ten-positive parent at the pinned snapshot has degree 816 and 124
operations. Making all four radicands units at 2 and weighting the roots
by 1, 2, 4, 8 removes the strong ordinate's extra factor mu. Three centers
and a quadratic transport weight give exact degree 706. This lowers degree
by 13.48% and increases the circuit length by nine operations; it is a
tradeoff rather than dominance in every measure.

The direct parent has 888 integer variables, 470 quadratic residuals, and
10,156 monomials at the same coefficient height. Its 167 nonnegativity
guards are reduced to 131: signs of power quotients are proved after their
arithmetic meaning, and frame signs are proved before index extraction.
The 303 exact signed eliminations then leave 780 variables and 434
quadratic residuals. This saves 108 integer variables (12.16%). The
direct route uses C222/Horn certificates, without K215 or Jones's
universal polynomial.

The repository already has nine-positive-variable equations and native
quartics with much fewer variables. Those use different degrees or
coefficient regimes. No global minimum or universal-variable record is
claimed here, nor priority for the general valuation or recurrence ideas.

## Complete equation data

- `dyadic10/p10_dyadic_degree706.json`: all literal arithmetic rows and
  fixed coefficient bindings. Named registers do not add unknowns.
- `dyadic10/coefficients/`: all four fixed numerals as authenticated
  compressed little-endian binary integers. They are not quantified ports.
- `dyadic10/PROOF.md`: complete new proof and exact-degree certificate.
- `direct780/equations/equation.json`: all 434 quadratic residuals and the
  exact ordered 780-variable list. Their sum of squares is the equation.
- `direct780/equations/expanded_polynomial.json`: every collected monomial
  of the same quartic, with fixed integer coefficients.
- `direct780/equations/domain_certificate.json` and `projection.json`:
  ordered sign proof and exact reverse coordinate restorations.
- `direct780/PROOF.md`: complete new domain and projection proof.
- Each component has an `INDEPENDENT_REVIEW.md` recording the scope of a
  separate AI-assisted review, including the inherited theorem boundary.

## Offline replay

Python 3.10 or newer with its standard library is sufficient:

```sh
python3 verify.py
python3 -O verify.py
```

The replay authenticates all delivered files, copies the package into a
temporary directory, checks the dyadic circuit and coefficient payloads,
and independently rebuilds and checks the complete direct quartic.
It rejects deliberate corruptions of sign and projection certificates.
The delivered files are not overwritten. The receipt `VERIFICATION.json`
records the delivery runs. These finite checks certify algebraic data and
proof premises, not unbounded unsolvability or Con(ZFC).

To rebuild the article:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

## Provenance

All research inputs are pinned to ProveIt commit
`ec80841c07e91be8956ce6ed4af9a9c0b782d3d9`. The immediate parents are
the in-repository `ten-positive-scaled-norm` candidate and the immutable
incoming archive `ConZFC_407_888_Quartics_2026-10-24.zip`.
The apparent date difference is the original archive's name, which is
preserved. This delivery uses the user's date, 23 October 2026.

The whole compact44 tuple and package61 calibration are retained with
exact source bindings. The direct parent archive is included unchanged.
New and inherited contributions, licenses, and limitations are separated
in the article and component notices.

## Further work

The article develops six concrete questions: remove further strong-Pell
scales with an explicit rank replacement; shorten the specialized norm
evaluator; infer more signs after semantic recovery; jointly optimize
sign proofs and monic eliminations; define a precise simplicity metric;
and formalize the new local lemmas before attempting the complete endpoint.
