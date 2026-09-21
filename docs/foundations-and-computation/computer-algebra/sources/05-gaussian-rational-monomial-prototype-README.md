# Exact Symbolic Computation with Surreal and Surcomplex Numbers

Research and implementation article, 21 September 2026.

## Article

`surreal_surcomplex_cas.pdf` is the 34-page compiled article.
`surreal_surcomplex_cas.tex` is its self-contained LaTeX source, including the
bibliography. It discusses exact representations, decidable subdomains,
coefficient-on-demand series, higher-rank precision, algebraic extensions,
local functions, transseries, radius-free analytic germs, finite algebras,
residues, contour operations, and Wolfram Language architecture.

Compile from this directory with a standard LaTeX installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error surreal_surcomplex_cas.tex
```

Alternatively run `pdflatex` three times. The source uses standard TeX Live
packages and Latin Modern. No external bibliography processor is required.
The compiled PDF was rendered and visually inspected; the final build has
no overfull boxes or unresolved citations/references.

## Executable Wolfram Language prototype

`code/HahnRational.wl` implements exact rational functions in finitely many
independent monomials over the Gaussian rational field Q(i), with lexicographic
integer-vector valuations. It implements exact field arithmetic, equality,
real comparison, valuation, leading coefficient, conjugation, real and imaginary
parts, squared modulus, and standard part of finite values.

Use fresh, unassigned monomial symbols. For the parent `{u,t}`, the intended
valuation is `v(u)={1,0}`, `v(t)={0,1}`, with the leftmost coordinate most
significant. A concrete surreal interpretation is `t=omega^-1`,
`u=omega^-omega`; consequently `u<t^n` for every ordinary positive integer n.
A reversed variable list is a different parent.

```wl
Get["code/HahnRational.wl"];
Clear[u,t];
a = HCreate[{u,t}, 1/(1-t)+u];
b = HCreate[{u,t}, 1/(1-t)];
HValuation[HAdd[a,HScale[b,-1]]]
(* {1,0} *)
HCompare[HCreate[{u,t},u], HCreate[{u,t},t^100]]
(* -1 *)
```

Only `HCreate` is a public value constructor. Do not manufacture the internal
`HR` head directly. Other public operations expect successfully constructed
values. This is a research prototype, not a hardened parser for arbitrary or
untrusted Wolfram expressions. It intentionally uses explicit functions rather
than overloading global arithmetic operators. Integer exponent zero is handled
as the algebraic power operation and returns one.

The package does NOT implement general Hahn-series coefficient programs,
rational-exponent parent refinement, algebraic closure, arbitrary analytic
germs, transseries, global exponential extensions, or contour integration.
The article discusses those as extensions with separate mathematical and
computational requirements. `Infinity` is used only as valuation metadata
for zero, not as a surreal field element. Numerical specialization is not
an order-preserving interpretation of all surreal scales.

## Validation

Run the package checks:

```sh
wolframscript -file code/test_HahnRational.wl
```

The clean connected-kernel run passed 88 checks in Wolfram Language 15.0.1
for Linux x86 (64-bit), July 2, 2026. The package definitions and test body
were loaded via `Get[StringToStream[...]]`, preserving package-context parsing.
`verification_wolfram.txt` records the result and scope. Random polynomial
examples use `SeedRandom[20260921]`. `code/examples.wl` contains a few short demos.

Run the independent finite mathematical checks:

```sh
python code/verify_examples.py
```

The script requires SymPy. The recorded run used Python 3.13.5 and SymPy 1.14.0
and passed 323 exact checks. `verification_python.json` records the results.
Checks include quotient-algebra matrices, trace/residue identities, separating
denominators, radius-free coefficients, exact geometric remainders, local
power-series identities, and valuation-based contour counts.

Neither suite machine-verifies the general theorems imported from the supplied
manuscripts. Passing these finite tests is not a complete proof of a full CAS.

## Provenance

The article is based on the supplied manuscripts:

- `surcomplex_analysis(3).tex` (SA),
- `surcomplex_analytic_geometry.tex` (AG),
- `surcomplex_contours(2).tex` (CT).

Those source manuscripts are not duplicated in this archive. Their results
are attributed as manuscript inputs, and are distinguished from published
background, new implementation proposals, and independently executed checks.
The bibliography includes the 2026 D-algebraic transseries zero-test and official
Wolfram and Sage documentation. General analytic-germ and contour algorithms
remain conditional on the stated support, coefficient-effectivity, and category
hypotheses.
