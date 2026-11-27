# Exact quarter-density support for disjoint products of small primes

Research package, 27 November 2026.

**Main contribution:** a complete support test at the article's critical quarter-density threshold, including a parity cut for the cyclic quotient of order four and three linear tests for the Klein four quotient. A general zero-sum completion theorem reduces the support problem at any fixed positive retention density to a bounded-quotient dynamic program. The GRH-conditional lifting is rederived, and a sharp arithmetic example excludes exactly one corrected joint pattern while every proper marginal remains fully supported.

## Files

- `quarter_density.pdf` — 13-page compiled mathematical note.
- `quarter_density.tex` — complete LaTeX source (bibliography embedded).
- `verify.py` — exact independent finite oracles, exhaustive tests, and DP test.
- `allocate.py` — constructive colour-table completion algorithm and tests.
- `verification.txt` — actual test output from this session.
- `SOURCE_AUDIT.md` — inspected GitHub sources and their blob identities.
- `SourceInterface.lean` — optional, uncompiled Lean upstream interface audit.
- `FORMALIZATION.md` — proposed formalization plan, not a formal proof.

## Reproduce

From this folder, with Python 3 and a standard LaTeX distribution:

```sh
python verify.py
python allocate.py
pdflatex -interaction=nonstopmode -halt-on-error quarter_density.tex
pdflatex -interaction=nonstopmode -halt-on-error quarter_density.tex
pdflatex -interaction=nonstopmode -halt-on-error quarter_density.tex
```

No Python package dependencies. The constructor works in the known finite quotient; it is not a search algorithm for the full prime representatives or a method for computing the quotient in time polynomial in the logarithm of the modulus.

## Scope

All arithmetic consequences are implications from the exact Dirichlet GRH statement exported by the vendored Lean package. The new finite combinatorial proofs are unconditional. The upstream Lean proof was inspected at the interface and selected reduction steps, not independently replayed. The new theorem is proved on paper, not kernel-checked. Finite computation is regression evidence only. The proof answers an explicit question in the supplied article; global publication priority has not been certified. The constants in the analytic argument are existence constants, not optimized numerical thresholds.
