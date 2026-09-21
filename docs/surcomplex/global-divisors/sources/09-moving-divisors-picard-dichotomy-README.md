# Global Support Obstructions in Surcomplex Analysis

**Moving Divisors, Mittag–Leffler Theory, and a Picard-Group Dichotomy**  
Research manuscript dated September 21, 2026.

## Contents

- `surcomplex_global_support.pdf`: the complete 28-page article, including its title page, contents, proofs, examples, support audit, verification notes, and references.
- `surcomplex_global_support.tex`: self-contained LaTeX source; bibliography is included in the file.
- `verify_examples.py`: exact symbolic checks of six groups of illustrative identities.
- `verification_report.txt`: the successful output from those checks.
- `requirements.txt`: the SymPy version used for the checks.
- `build.sh`: optional POSIX build script.

## Principal results

Theorem 5.2 gives a necessary and sufficient common-support condition for a discrete Hahn Mittag–Leffler problem. Theorem 6.2 gives the corresponding exact criterion for global realization of finite infinitesimal zero clusters over a discrete ordinary divisor. The controlling supports belong to the monic cluster-polynomial coefficients, not separately labeled roots.

Theorem 4.3 proves that ordinary-base stalks of the coefficient sheaf are principal ideal domains, generally nonlocal. Theorems 10.3 and 10.4 establish the Picard-group vanishing dichotomy and its exact complex dimension for countable noncyclic value groups. Example 7.2 gives an explicit construction of infinitely many root clusters of unbounded degrees; Corollary 7.3 gives a nonprincipal effective sub-divisor of a principal divisor.

The coefficient sheaf is defined over the ordinary complex plane, in a fixed set-sized ordered subgroup of the surreal value group. These are not assertions about ordinary complex line bundles or fine-topological cohomology on the entire surreal class.

## Build the PDF

Use a TeX Live or MiKTeX installation with the packages listed in the source. The article uses standard Latin Modern fonts supplied by the TeX installation; no font files are included in this archive.

Run the following command three times, in this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error surcomplex_global_support.tex
```

Alternatively, on a POSIX shell:

```sh
sh build.sh
```

No bibliography processor or external images are required. The delivered PDF was built with pdfTeX. Its final compilation had no LaTeX warnings, undefined references, or overfull/underfull boxes.

## Run the symbolic checks

Python 3.10+ is required. The delivered report was generated with SymPy 1.14.0.

```sh
python -m pip install -r requirements.txt
python verify_examples.py --output verification_report.txt
```

These tests verify exact finite symbolic identities. They do not verify the arbitrary-support theorems, compute infinite cohomology groups, establish the failure of well ordering of an infinite support, or certify novelty. The all-order proofs are in the article.

## Provenance and research status

This is a continuation of the user-supplied manuscript `surcomplex_analysis(3).tex`. Its terminology, evaluation framework, gluing mechanism, preparation, and local root counts are attributed in the article. The original file is not duplicated in this archive.

The global support criteria and Picard-group conclusions are proposed new results for the specified framework. The literature check did not locate those formulations, but is not an exhaustive priority certification. No named established open conjecture is claimed to have been settled, and no independent peer review or proof-assistant verification is claimed.
