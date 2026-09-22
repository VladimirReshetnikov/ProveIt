# Surreal Markov Generators at Every Valuation Scale

**Stochastic retracts, prescribed effective chains, relative stability, and rank-one realization**

Research manuscript prepared for Vladimir Reshetnikov, 22 September 2026.

## Contents

- `surreal_markov_hierarchies.tex`: complete, standalone LaTeX source, including bibliography.
- `surreal_markov_hierarchies.pdf`: the compiled 28-page article.
- `code/verify.py`: exact finite verification program; no network access or external data.
- `data/verification.json`: recorded passing output, including all 48 instance summaries.
- `SOURCE_AUDIT.md`: repository revision, inspection scope, literature comparison, and novelty limits.
- `requirements.txt`: Python dependency for the checks.
- `build.sh`: LaTeX build command with a pdflatex fallback.

## Main mathematical results

Theorem 7.4 and Corollary 7.5 give a forward/reverse classification of finite leading resolvent hierarchies. Any compatible nested family of stochastic projections and prescribed real effective Markov generators is realizable by an irreducible Hahn rate matrix at arbitrary prescribed ordered scales. The construction includes positivity corrections at intermediate edge scales that introduce no additional leading resolvent crossover.

Theorem 8.1 gives an entrywise relative perturbation bound uniform over every positive resolvent parameter, with no spectral-gap loss. It retains information about entries whose ordinary residue is zero.

Theorem 9.2 reproduces every finite marked-forest leading diagram in a rank-one real monomial model. This preserves the finite comparison and amplitude data, not the full order of the original value group.

Theorems 10.2 and 10.3 identify the effective characteristic polynomial, leading surcomplex eigenvalue amplitudes, and all eigenvalue valuations from the positive forest profile.

## Build the article

A normal TeX Live or MiKTeX installation with pdfLaTeX is sufficient. The source uses standard AMS, Latin Modern, geometry, microtype, hyperref, booktabs, and fancyhdr packages. It requires no external images or bibliography database.

```sh
sh build.sh
```

Equivalent command:

```sh
latexmk -pdf -halt-on-error -interaction=nonstopmode surreal_markov_hierarchies.tex
```

The build writes temporary LaTeX files locally. They are intentionally not included in this archive.

## Run the exact checks

Python 3.10 or newer is required. A virtual environment is recommended.

```sh
python -m venv .venv
# Activate the environment using the command appropriate for your system.
python -m pip install -r requirements.txt
python code/verify.py
```

The program uses exact rational arithmetic and a fixed seed (`20260922`). It overwrites `data/verification.json` with its results. The delivered run passed for 48 complete directed graphs on 2–5 vertices, enumerating 17,280 forests and checking 105 critical kernels, plus independent symbolic examples. SymPy 1.14.0 was used. These are finite tests, not a proof assistant verification of the general statements.

## Scope and originality

This manuscript takes the new-theorems alternative in the request. It does not claim to solve a named published open problem. Classical forest identities, stochastic-idempotent structure, rank-one metastability formulas, and the self-adjoint hierarchical-Laplacian background are credited rather than presented as new.

The exact arbitrary-rank realization and stability package is a candidate original contribution after a targeted, non-exhaustive comparison. Neither historical priority nor absence from every archive in the repository is certified. In particular, `docs/new` was inventoried but its 18 ZIP files were not expanded. See `SOURCE_AUDIT.md` for the exact audit boundary.

All general results have written proofs. No Lean formalization, infinite-state extension, global surreal stochastic process, or global surreal matrix exponential is claimed. The source repository was not modified.
