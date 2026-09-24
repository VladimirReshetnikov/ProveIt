# Intrinsic ordinal approximations for finitary powersets

**Research date:** 19 September 2026  
**Article:** `article.pdf` (24 pages) and `article.tex`  
**Outcome:** a partial answer to a documented intrinsic-invariant question, with full proposed proofs, exact formulas, and a sharp obstruction to an unrestricted extension.

## Read this first

The selected question is in Section 6 of Abriola, Halfon, Lopez, Schmitz, Schnoebelen, and Vialard, *Measuring well-quasi-ordered finitary powersets*, arXiv:2312.14587v2 (17 July 2024). The present note treats one weakened invariant, not all the questions in that section. A limited literature/status search did not find a later resolution; this does not exclude unpublished or differently phrased work. No claim of priority, independent refereeing, or proof-assistant verification is made.

Write `Idl(B)` for nonempty directed downsets and `P_f(A)` for finite subsets modulo mutual Hoare domination. The proposed intrinsic invariant is

    a_o(A) = sup { o(B) + 1 : Idl(B) order-embeds into A }.

The note proves the universal lower bound `a_o(A) <= h(P_f(A))`, with equality when every finitely generated downset of `A` is an ideal completion. Equivalently, each such downset is an algebraic dcpo. This class includes all ordinal chains and finite posets and is closed under finite disjoint unions, Cartesian products, finite words, finite multisets under injective embedding, and finitary Hoare powersets. It is also closed under taking downsets.

For nonzero ordinal factors, the exact formula is

    h(P_f(product_i alpha_i))
      = sup_{a_i < alpha_i} (natural_product_i (1 + a_i) + 1).

The `1 + a_i` is ordinary ordinal addition in that order. Powers of omega and mixed open/closed endpoints yield closed formulas involving Milner–Rado sums.

The universal identity fails. If `lambda` is an infinite limit ordinal and `F` is a nonempty finite poset, then

    h(P_f(lambda + F)) = lambda + |F|,
    a_o(lambda + F)    = lambda + max_{x in F} |upper_F(x)|.

Thus a chain of type omega capped by two incomparable points has the two values `omega+2` and `omega+1`. This counterexample refutes the extension proposed in this note, not a conjecture asserted by the source authors.

## Contents

- `article.tex`, `article.pdf`: complete article, proofs, examples, references, and research boundaries.
- `ordinal_arithmetic.py`: exact recursive Cantor-normal-form arithmetic below epsilon_0; ordinary addition, natural sum/product, Milner–Rado sum, predecessor sampling, and the mixed product-height evaluator.
- `verify.py`: exhaustive finite-order and bounded-construction checks, plus exact ordinal examples.
- `verification_report.json`, `verification_output.txt`: successful run results.
- `finite_cap_examples.csv`: seven finite-cap examples. The omega-prefix columns are applications of the symbolic theorem, not finite simulations.
- `proof_audit.md`: proof dependencies, fragile points, and unresolved scope.
- `sources.md`: exact primary-source locations, versions, and status-search limitations.
- `build.sh`: regenerate checks and compile the article.
- `artifact_validation.txt`: technical PDF and package checks.

## Run the checks

Python 3.10 or later, standard library only:

```sh
python3 verify.py > verification_output.txt
```

Run without `-O`; the script rejects disabled assertions. Output files are written beside `verify.py`. The supplied run used Python 3.13.5.

The successful run covered 408 naturally labelled posets on at most five points, 5,231 downsets, 1,971 nonempty directed ideals, 376,293 Hoare/union comparisons, ten bounded word/multiset constructions, 1,947 exact ordinal or predecessor-sample assertions, and 28 finite-prefix cap checks. Every isomorphism type of finite poset through five points occurs, but labelled repetitions are retained.

These checks do not establish the infinite theorems. All finite posets have only principal ideals, so finite simulation cannot detect the nonprincipal ideal responsible for the cap obstruction. Likewise finitely many predecessor samples cannot establish a transfinite supremum.

## Build the PDF

With a reasonably complete TeX Live or MiKTeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Or, on a system with Bash:

```sh
bash build.sh
```

The article uses `newpxtext`/`newpxmath`, `amsmath`, `amsthm`, `geometry`, `microtype`, `mathtools`, `booktabs`, `array`, `longtable`, `enumitem`, `fancyhdr`, `titlesec`, `listings`, `tcolorbox`, `hyperref`, and `cleveref`. The bibliography is included directly in the TeX file; no BibTeX pass is required. Font files and third-party source PDFs are not redistributed. TeX supplies its installed fonts during rebuilding.

## Example

```python
from ordinal_arithmetic import ONE, OMEGA, Ordinal, monomial_product_height

# Factors omega^2 and omega^2: height omega^3.
print(monomial_product_height([Ordinal.finite(2)] * 2, []))

# Factors omega and omega+1: height omega^2.
print(monomial_product_height([ONE], [ONE]))

# Factors omega^omega and omega^omega: height omega^omega.
print(monomial_product_height([OMEGA, OMEGA], []))
```

Here printed `w` means omega. An open exponent `b` denotes the factor `omega^b`; a closed exponent `c` denotes `omega^c + 1`. Positive finite factors are supplied in a third argument. Zero finite factors give the empty product order, whose finitary powerset has height one. With no factors at all, the Cartesian product is a singleton and the height is two.

The mathematics allows arbitrary ordinal exponents. The code supports finite hereditary Cantor normal forms below epsilon_0 only and does not implement a general supremum oracle or an evaluator for every expression in the enlarged structural class.
