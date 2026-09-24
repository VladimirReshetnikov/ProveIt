# Sparse Perfect Families in a Single Coarse Class

Research report prepared for Vladimir Reshetnikov, 18 September 2026.

## Result

The article attacks C1 in the supplied `turing_degrees_unified.tex`: whether
all nonuniform coarse-equivalence classes contain a least Turing degree.
The answer to that exact formula is **no**.

A source audit shows that the basic negative answer already follows from
Hirschfeldt–Jockusch–Kuyper–Schupp, Theorem 4.2 (preprint 2015; JSL 2016).
It is therefore **not claimed as a new resolution of an open problem**.
Gerdes's 2025 Question 7 explicitly prints the formula at issue.

The main independently developed proof is a quantitative strengthening:
for any computable nondecreasing unbounded sublinear h, there is a perfect
family P of individually 1-generic sets, every distinct pair forming a
Turing minimal pair, such that all members agree outside one common set V
with |V intersect [0,n)| <= h(n) for every n. The tree labeling and two
selected witnesses are computable in 0''. For example h(n) can be
floor(log_2(n+1)). Priority for this exact refinement is not established.

The article also proves an equality of the Turing spectra of density,
uniform coarse, and nonuniform coarse classes, and a block-code criterion
for existence of a least representative degree.

## Files

- `coarse_minimal_pair_attack.pdf`: complete 17-page article.
- `coarse_minimal_pair_attack.tex`: self-contained LaTeX source.
- `checks/verify_finite_core.py`: deterministic standard-library Python checks.
- `checks/results.json`: machine-readable results, including script hash.
- `checks/results.txt`: readable execution transcript.
- `sources/source_audit.md`: primary sources, version/page details, and status distinctions.
- `input/turing_degrees_unified.tex`: unchanged original supplied report.
- `build.sh`, `Makefile`: build and test commands.
- `SHA256SUMS`: hashes of the delivered files, excluding the manifest itself.

## Build

Requirements: Python 3.9 or newer; a standard TeX Live or MiKTeX installation
with pdfLaTeX, Latin Modern, AMS packages, microtype, enumitem, xcolor,
fancyhdr, listings, xurl, titlesec, hyperref, and bookmark.
No network access is needed to compile the article or run the checks.

On a system with Bash:

```sh
./build.sh
```

To run only the finite checks (also works from PowerShell):

```sh
python checks/verify_finite_core.py
```

To compile manually, run the following command three times in this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error coarse_minimal_pair_attack.tex
```

`make` runs the full build; `make check` runs the checks alone.
Builds may differ byte-for-byte in PDF metadata timestamps. The manifest
identifies the delivered edition, not every possible future rebuild.

## Verification boundary

The full theorem is supported by the mathematical proof, not by the finite
tests alone. The script checks hypercube connectivity, finite no-split models,
all-prefix variation budgets, lifting to multiple leaves, sparse coding,
and majority decoding. It does not decide halting, execute a 0'' oracle,
construct an infinite noncomputable path in ordinary finite time, or prove
genericity from finite examples.

No Lean certification or independent expert review is claimed. The article
states every noncomputable stage decision explicitly. The result is about
**least** degrees, not absence of minimal elements, and does not resolve
the effective-dense question C2.
