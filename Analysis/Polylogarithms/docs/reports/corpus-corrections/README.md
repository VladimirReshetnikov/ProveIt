# Polylogarithms research continuation

**Real Zeros and Exact Relation Spaces in the Polylogarithm–Stieltjes Programme**  
Prepared for Vladimir Reshetnikov, 8 October 2026.

This package continues the research in `Analysis/Polylogarithms/docs` of
[ProveIt](https://github.com/VladimirReshetnikov/ProveIt), pinned to commit
`3a6d80ed618d839915deb0d19ab687f45e81d995`. The source inventory contains
40 files: eight article sources, 31 reports, and the area README.
[PROVENANCE.json](PROVENANCE.json) records their paths and Git blob identifiers.
All eight articles were examined; the report review was targeted to the claims
discussed in the continuation, rather than an exhaustive audit of every formula.

## Start here

| File or directory | Purpose |
|---|---|
| [polylogarithms_research.pdf](polylogarithms_research.pdf) | Complete article, proofs, corrections, and further research questions. |
| [polylogarithms_research.tex](polylogarithms_research.tex) | Generated monolithic LaTeX source, including the bibliography. |
| [sections/](sections/) | Editable source fragments used to assemble the article. |
| [CORRECTIONS.md](CORRECTIONS.md) | Register of 22 proposed corrections, C01–C22, with source anchors and evidence. |
| [code/](code/) and [data/](data/) | Reproduction programs, exact finite witnesses, and numerical diagnostics. |
| [figures/](figures/) | Included plot assets; the article uses `stieltjes_profiles.pdf`. |
| [ENVIRONMENT.json](ENVIRONMENT.json), [requirements.txt](requirements.txt), [SHA256SUMS](SHA256SUMS) | Environment record, Python dependencies, and delivery checksums. |

The archive contains one top-level directory, `polylogarithms_research/`.
Run the commands below from that directory.

## Results and mathematical status

The principal analytic theorem proves that, for every Laurent index $n\geq0$
and parameter-derivative order $k\geq1$, $\gamma_n^{$k$}(a)$ has at most
$n$ positive real zeros, counted with multiplicity. For each fixed $n$,
all $n$ simple zeros occur for sufficiently large $k$. Their locations
have complete asymptotic expansions derived from the real, simple roots of
the reciprocal-gamma Appell polynomial. At $n=1$, uniqueness holds for
every $k\geq1$, with the explicit bracket

$$
e^{H_{k-1}}<a_k<e^{H_{k-1}}+\tfrac12.
$$

The algebraic development proves the previously unrestricted rational-grid
rank claims using primitive-conductor character coordinates. It also proves
freeness of complete finite-jet distribution modules over coefficient
algebras, including nilpotents and resonant weights. These are ranks of
specified **formal presentations** with a stated background inventory;
they do not prove independence of evaluated constants. The article also
supplies the precise factor $1/2$ in the functional-equation bridge at
trivial Dirichlet-$L$ zeros.

The all-even-weight Gaussian reduction is reconstructed with attribution
to Olaikhan’s 2022 derivation. Coffey’s earlier derivative formulas and
the $n=k=1$ zero result, and Kubert’s universal-distribution results,
are credited explicitly. This is an unrefereed research draft, without
a Lean formalization or an exhaustive historical-priority assessment.
Neither unsuccessful integer-relation searches nor finite computations
are used as proofs of numerical independence.

## Build the PDF

The supplied figure allows rebuilding without rerunning numerical calculations.
Use Python 3 and a LaTeX installation providing `pdflatex` and the packages
listed in `sections/preamble.tex`, including Latin Modern, the AMS packages,
`mathtools`, `microtype`, `hyperref`, and `xurl`.

```bash
cd polylogarithms_research
bash BUILD.sh
```

The build script runs `code/assemble_article.py`, compiles three LaTeX passes,
and checks for undefined references and overfull boxes. Inspect
`polylogarithms_research.log` and `build-console.log` if it fails. The assembler
concatenates the 13 named fragments into the monolithic source. Edit those
fragments: rebuilding overwrites direct edits to the generated `.tex` file.

## Reproduce the checks

The recorded environment uses Python **3.12.14** with mpmath **1.3.0**,
SymPy **1.14.0**, NumPy **2.3.5**, SciPy **1.17.0**, and Matplotlib **3.10.8**.
For example, create an isolated environment and install the pinned requirements:

```bash
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
python code/run_checks.py --exact-only
python code/run_checks.py
```

The first runner invocation selects four exact-arithmetic programs. Their
recorded outputs cover 486 weighted distribution cases, 160 finite-jet cases,
the rank-seven shuffle matrix with its annihilators, and five cubic
class-number certificates. The full invocation additionally runs the bridge,
Gaussian, correction, and Stieltjes-zero checks, and regenerates the profile
figures. Individual scripts can also be invoked directly from the package root.

The JSON files preserve the actual parameters and results. In particular,
the Stieltjes run records eight kernel comparisons, 40 moving zeros, and eight
global brackets. High-precision residuals are diagnostics, not interval-certified
errors in every printed digit. The article explains the distinct role of
the analytic proofs, exact finite certificates, and numerical checks.

## Integrate into ProveIt

Import the complete folder beneath `Analysis/Polylogarithms/docs/` to preserve
its relative figure and script paths, and link the new article from the existing
index. Review C01–C22 individually before applying their proposed edits to the
historical drafts. The register supplies snapshot-specific locations, preferred
LaTeX labels, replacements, and supporting proofs. **The original source files
have not been modified by this package.**

Keep the provenance, correction register, code, and data with the article.
Check `sha256sum -c SHA256SUMS` before regeneration; rerunning programs can
change timing metadata or PDF metadata even when mathematical outputs agree.
After integration edits, rebuild the article and regenerate the relevant
witnesses and checksums.
