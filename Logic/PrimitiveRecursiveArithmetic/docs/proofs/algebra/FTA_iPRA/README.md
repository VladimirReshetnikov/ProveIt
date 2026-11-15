# Fundamental theorem of algebra in intuitionistic PRA

This package contains a complete human-readable, non-formalized argument for
an arithmetized constructive fundamental theorem of algebra, together with a
concrete Lean formalization blueprint and exact rational reference programs.

## Start here

- `FTA_iPRA.pdf` — the compiled article, including the full proof, explicit
  constants, logical-strength audit, and formalization plan.
- `FTA_iPRA.tex` — its complete editable LaTeX source.
- `LEAN_PLAN.md` — module-by-module implementation and proof obligations.
- `lean/Specification.lean` — **uncompiled** finite specifications, explicit
  object-language formulas, and types of the eventual derivation certificates.
- `code/direction.py` and `code/descent.py` — exact rational implementations
  of the bounded direction construction and local polynomial descent.
- `code/test_direction.py`, `code/test_descent.py`, and their JSON result files
  — finite exact checks of those reference implementations.
- `SOURCE_MANIFEST.md` — inspected repository snapshot and source provenance.

## The theorem proved in the article

Fix a primitive recursive coefficient-name program A(i,s,parameters), and let
a_i(s) be its Gaussian-rational output for 0 <= i <= n. Assume

```text
|a_i(s)-a_i(t)| <= 2^(-s) + 2^(-t).
```

Supply n >= 1, 1 <= k <= n, and h with the finite rational certificate

```text
|a_k(h+2)| >= 2^(-h).
```

The explicit construction produces primitive recursive functions alpha and M
for which iPRA proves

```text
u >= t  -> |alpha(u)-alpha(t)| <= 2^(-t-2),
s >= M(t) -> |sum_(i=0)^n a_i(s) alpha(t)^i| <= 2^(-t).
```

Thus alpha is a coherent fast Cauchy name representing an exact root. The
upper degree n need not be the actual degree, and the apart coefficient need
not be the leading coefficient. The proof uses no real-equality decision,
compactness, countable choice, or Markov principle.

The first-order internal result is a schema for fixed PR coefficient programs,
with a single uniform first-order specialization for finite rational-polynomial
codes. No total PR universal evaluator for arbitrary PR programs is assumed.

## Formalization status

The human-readable proof is complete in the explicitly stated arithmetical
sense. The Lean formalization is **not complete**. The supplied file is an
uncompiled specification and interface; no Lean executable was available.
It asserts no missing FTA theorem as an axiom and supplies no derivation
certificate. The intended endpoint is a term of

```lean
Prf PRAAx [] (ftaSentence arithmeticCodes inputProgram outputProgram)
```

in ProveIt's deeply embedded intuitionistic arithmetic. An ordinary theorem
about mathlib's `Complex` would not certify this stronger logical-strength
claim. See the article and `LEAN_PLAN.md` for the exact remaining work.

The root program operates on coefficient names and may select different valid
roots for equivalent input names. No extensional single-valued global choice
of a root is claimed.

## Reproduce the finite checks

From this directory:

```sh
cd code
python3 test_direction.py
python3 test_descent.py
```

Only the Python standard library is needed. All construction and certificate
arithmetic uses exact fractions. The recorded seven direction cases and six
descent cases passed. These examples validate executable components, not the
universal theorem or an internal iPRA derivation.

The full worst-case root-name schedule is intentionally enormous. These
programs implement its local routines, not an efficient numerical root solver
or a practical run of the entire schedule.

## Rebuild the PDF

With a normal TeX Live installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error FTA_iPRA.tex
pdflatex -interaction=nonstopmode -halt-on-error FTA_iPRA.tex
```

Standard LaTeX packages used include `amsmath`, `amsthm`, `mathtools`,
`microtype`, `lmodern`, `geometry`, `booktabs`, `longtable`, `enumitem`,
`listings`, `hyperref`, `xcolor`, and `fancyhdr`.

The source records the inspected ProveIt commit. Repository contents were
read but not changed or independently rebuilt.
