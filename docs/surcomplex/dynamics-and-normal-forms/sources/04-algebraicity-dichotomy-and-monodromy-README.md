# Infinitesimal Resonance and Hidden Monodromy in Surcomplex Dynamics

Research article prepared for Vladimir Reshetnikov, 21 September 2026.

## Contents

- `article.pdf`: the 23-page typeset article, including complete proofs,
  examples, a literature discussion, computational details, and references.
- `article.tex`: standalone LaTeX source with an internal bibliography.
- `code/verify.py`: exact finite verification, Python 3.9+, standard library only.
- `data/verification.json`: recorded verification result (2,764 assertions).
- `data/coefficients.csv`: sample exact Koenigs coefficients.
- `RESEARCH_NOTES.md`: provenance, scope of the literature comparison, and
  precise limits of the novelty and verification claims.
- `Makefile`: optional build/check commands.
- `SHA256SUMS.txt`: checksums for the package files, excluding this checksum file.

## Main results

For a complex polynomial V with V(0)=0 and V'(0)=mu != 0, consider
G_epsilon(w)=w+epsilon V(w), where epsilon=t^delta has positive Hahn
valuation. The article constructs the normalized common-domain Koenigs
coordinate and proves that it is algebraic over C(w)((t^Gamma)) if and only
if V is linear. At a simple zero a of V, its exact coefficientwise monodromy
exponent is Log(1+mu epsilon)/Log(1+V'(a) epsilon). A nonzero infinitesimal
part prevents every finite branched cover from removing the monodromy.

For f(z)=(1+epsilon)z+z^(q+1), the strong Taylor sum is defined exactly on
v(z)>delta/q. There it gives an invertible valuative-isometric conjugacy.
After rescaling, a common-domain coefficientwise continuation reaches the
critical scale and exposes monodromy invisible in the algebraic leading
coordinate.

These are statements about a specified strong Hahn function theory. They
are not assertions about ordinary topological convergence on all No[i].
"Transcendental" refers to functions over the rational-coefficient Hahn
field, not to an individual value being outside No[i].

## Build the article

From this directory, with a conventional TeX Live or MiKTeX installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Without latexmk, run the following command three times to resolve the table
of contents and cross-references:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

All mathematical source is in `article.tex`. No external bibliography,
images, custom font files, shell escape, or network access is needed.

## Reproduce the checks

```sh
python3 code/verify.py
```

On Windows, `python code/verify.py` is equivalent. No pip installation is
needed. Successful completion prints a JSON object with `"status": "PASS"`
and `"exact_assertions": 2764`, and regenerates both files under `data/`.
The Python version field will reflect the interpreter used. All coefficient
arithmetic uses `fractions.Fraction`; no approximate root computations or
floating-point tolerances are involved.

## Research status

This is an unrefereed, AI-generated research draft. It contains full
mathematical arguments but no proof-assistant formalization. The exact
finite tests check consistency; they do not prove the infinite theorems.
The principal algebraicity/monodromy results are proposed as new to the
present investigation, not as certified first publications. No named
published open conjecture is claimed solved. Existing formal-embedding and
ultrametric-linearization methods are explicitly acknowledged.
