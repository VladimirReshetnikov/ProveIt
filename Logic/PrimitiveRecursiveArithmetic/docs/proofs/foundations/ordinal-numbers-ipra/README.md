# Ordinal numbers in intuitionistic primitive recursive arithmetic

Open **ordinals.pdf** for the paper. **RESULTS.md** indexes its proofs by topic and lists the formal coverage. The main source is **ordinals.tex**. Its chapter files sit beside it.

The proofs use first-order intuitionistic arithmetic with a symbol for each primitive recursive definition and induction for quantifier-free formulas. Hereditary Cantor normal forms provide the main infinite presentation. A separate extension gives the fixed points of ordinal exponentiation with base omega through the first omega-many epsilon numbers.

## Rebuild the paper

Use a standard TeX Live installation with pdfLaTeX and latexmk. In this directory run

```sh
latexmk -pdf ordinals.tex
```

## Reproduce the checks

Use Python 3.10 or later and Lean 4.32.0 on PATH. Python and Lean use only their standard libraries. The supplied toolchain file selects the Lean release when using elan.

```sh
python3 check.py
python3 verify_lean.py
```

The optional environment variable `LEAN` selects a specific Lean executable. The verifier builds the imported modules into a temporary directory. **verification.txt** records the checks run for this edition.

## Scope of formalization

The Lean proofs cover finite rank/unrank and von Neumann recognition, tree comparison, successor, fundamental sequences and their least-index specification, tower levels, addition associativity and division by omega. The report also proves general division, ordinal power laws, the order type of finite-support functions, prime factorization and the results on the epsilon extension. The formalization section describes how to internalize the algorithms and proofs in ProveIt's `Prf PRAAx` calculus. The archive contains no claim of a completed object-language certification of the full paper.
