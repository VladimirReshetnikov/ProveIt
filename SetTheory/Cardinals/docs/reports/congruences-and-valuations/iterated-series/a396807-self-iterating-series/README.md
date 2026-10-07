# Arithmetic of a Self-Iterating Generating Function

**An 18-page research article, dated September 19, 2026.**

Start with `article.pdf`. The editable source is `article.tex`.

The selected problem is the pair of congruences labelled as conjectures
in OEIS A396807. Here `F^[k]` denotes functional iteration, not an ordinary
power, and the generating function is defined by

    A(x) = x + A^[5](x) A^[6](x).

The article proves both conjectures, including negative integer iterates:

    A(x) = x/(1-x)                 (mod 10),
    A^[k](x) = x/(1-k*x)           (mod 10), for every integer k.

It then proves a sharp modulus theorem for the weighted family
`F = x + c F^[r] F^[s]`, constructs rational lifts at every selected
prime power, and proves that A396807 modulo 100 has **minimal period 46860**,
starting at index 1. Additional results concern compositional order,
p-adic-time iteration, factorial lower bounds, and neighboring OEIS entries.

## Reproduce the computations

Use Python 3.10 or later. The main suite uses only the standard library:

```sh
python code/verify.py
```

It regenerates the exact coefficient data, period data, and
`data/verification.json`. Times in that JSON naturally vary between runs.
The included run used Python 3.13.5 and passed all checks.

For independent symbolic rational-function identities, install the optional
dependency and run:

```sh
python -m pip install -r requirements-optional.txt
python code/symbolic_checks.py
```

The included symbolic run used SymPy 1.14.0 and passed all identities.
Do not run this optional script with Python's `-O` flag: it uses assertions.

To query a coefficient's last two digits without constructing the full
integer, use:

```sh
python code/query.py 1000000
```

The index is first reduced using the proved period. Work in the recurrence
is bounded by 46860 steps, independent of the size of the original index.
The function `last_two_digits_at(n)` is also available for direct import.

## Build the PDF

A TeX installation with pdfLaTeX, latexmk, and the packages named in the
source is required. In particular, `newtxtext` and `newtxmath` provide the
text and mathematical typography. No font files are distributed here.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The supplied PDF is already compiled. The optional Makefile supplies
`make report`, `make check`, `make symbolic`, and `make clean`.

## Files

- `article.tex`, `article.pdf`: full statements and detailed proofs.
- `code/series_tools.py`: exact coefficient construction, independent
  Horner composition, inversion, iterates, and rational recurrences.
- `code/verify.py`: standard-library finite verification suite.
- `code/symbolic_checks.py`: optional symbolic certificates, a reusable
  first-correction formula, and the rational linearized inverse.
- `code/query.py`: last-two-digit query command.
- `data/a396807_exact_400.txt`: 400 independently generated exact values.
- `data/a396807_mod100_period.txt`: one full period, in `n value` format.
- `data/verification.json`, `data/verification_console.txt`: finite-check
  results from the included run.
- `data/symbolic_verification.json`: symbolic identity results.
- `source_notes/status.md`: source attribution, status, and limitations.

All coefficient arrays in the code use ascending degree order and include
the constant term. The sequence and period files start at index 1.
The exact solver has O(N^3 + K*N^2) arithmetic cost and O(N^2 + K*N)
storage, where K=max(r,s,1). These are not bit-complexity claims.

## Evidence and scope

The proofs, rather than finite tests, establish the all-degree results.
The main suite generates 400 exact A396807 coefficients and compares only
the first 19 against the published OEIS initial list. Two complete
modulo-100 periods are generated from the proved rational formulas; they
are not an independent computation of 93720 full integer coefficients.

The code implements the first correction and the general linearized
inverse. The article proves and specifies recursive rational lifting at
arbitrary prime powers; an optimized arbitrary-exponent lifting engine is
not included.

The OEIS entries still displayed conjecture labels when checked on
September 19, 2026. A limited search did not find a separate proof. This
is not a guarantee of priority, an exhaustive literature review, external
peer review, or proof-assistant formalization. The distinction is explained
in the article and source notes.

## Related report (dated note, 7 October 2026)

See also the sibling report
[`a168362-lacunary-iterates-mod4`](../a168362-lacunary-iterates-mod4/),
Part II (batch 114). For the lacunary seed F_p(x) = sum_j x^(p^j) and every
prime p it proves that every coefficient of every integer iterate is
divisible by p^((s_p(N)-1)/(p-1)) (its Theorem 16.1), and it builds a
coefficientwise p-adic iteration group z -> F_p^(o z), z in Z_p, with a
sufficient period, in z, of each coefficient modulo p^q (its Theorems 24.1
and 24.2), as this report does for its own series under "p-adic-time
iteration". Different series; no shared theorem. That report names this one
as a methodological neighbour, not a source. This section is a pointer
added in the collection's cleanup pass; the rest of this README is the
delivered guide.
