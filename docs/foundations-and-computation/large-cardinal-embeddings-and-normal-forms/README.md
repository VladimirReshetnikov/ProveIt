# Critical-Point Defects in Surreal Arithmetic

**Large-cardinal embeddings, exact support thresholds, surcomplex fields, and omnific integers**

Research article prepared for Vladimir Reshetnikov with ChatGPT, 23 September 2026.

## Repository placement

Placed in `21375f8`. Independent proof review and formalization are pending.

The current [article.tex](article.tex) is source 07, the critical-point-defects
base. Sources 06 and 09 remain separate manuscripts in the placement archive
history; their assembly and comparison with this base are pending. No
maintained PDF is installed yet. The current source-07 files are
[proof status](07-critical-point-defects-PROOF_STATUS.md),
[build helper](code/07-critical-point-defects-build.sh), and
[finite verifier](code/07-critical-point-defects-finite_regression.py), with
prefixed recorded outputs under [data/](data/). The delivery description
below uses the original filenames. Build `article.tex` separately in scratch;
the delivered helper assumes the original package layout.

## Contents

- `critical_point_defects.pdf`: the 32-page article, including the title page, two front-matter pages, 29 numbered pages, and bibliography.
- `critical_point_defects.tex`: standalone LaTeX source with an internal bibliography.
- `PROOF_STATUS.md`: assumptions, claim inventory, novelty boundary, and verification limitations.
- `build.sh`: builds the PDF and reruns the finite regression checks.
- `code/finite_regression.py`: exact finite algebraic checks using Python's standard library.
- `data/finite_regression_results.json`: recorded successful check results.
- `data/finite_regression_console.txt`: readable output from the same run.
- `data/build_validation.json`: basic PDF/build validation facts.

## Central construction

Assume an amenable elementary embedding j: V -> M into a transitive inner class, with critical point kappa. A normal ultrapower arising from a measurable cardinal supplies an instance.

The map J applies j to surreal sign codes. The companion H_j instead applies J to the exponents in a Conway normal form, leaving its real coefficients unchanged and summing term by term. The article determines their exact difference, equalizer, and image intersection.

The common domain is the real-closed field of surreal numbers with fewer than kappa OUTER normal-form terms. This is not the birthday-bounded field No_{<kappa}. The two image fields are incomparable but canonically isomorphic as ordered valued fields over their common intersection. They are respectively the logarithmic field closure and the external strong-sum closure of that intersection.

A coefficient of the defect of a Boolean mask records whether the encoded subset of kappa belongs to the normal measure derived from j. The article gives omnific and surcomplex versions, an exact positive-family summation threshold, an exponential compatibility formula, and a supercompact seed extension. It ends with twelve proposed research questions and a formalization plan.

## Reading route

For the main theorem package, read Sections 1–7. Section 8 treats derived measures and the Hadamard mask algebra. Sections 9–10 give the omnific and surcomplex transfers. Sections 11–13 address logarithms, exponentiation, the two closures, and supercompact seeds. Sections 14–16 locate the results and propose further work. The appendices record proof dependencies and review priorities.

## Build

A TeX distribution with `latexmk`, pdfLaTeX, `newtxtext`, `newtxmath`, and the other packages named in the source is required. Python 3.10 or later is sufficient for the finite checks; no Python dependencies need to be installed.

Run:

```sh
./build.sh
```

Or separately:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error critical_point_defects.tex
python3 code/finite_regression.py
```

The source uses only standard installed TeX packages. No font files or third-party papers are included in this archive.

## Status and scope

The central results have written proofs relative to the explicitly identified classical inputs. They are proposed original contributions, not a certified breakthrough or a claim to have solved a named published conjecture. Publication priority has not been established. No Lean formalization or independent referee review is claimed.

The finite program checks finite algebraic identities only. It does not verify elementary embeddings, measurability, normal-form absoluteness, transfinite summation, or the proofs in this article.

Repository context was inspected at commit:

`0865f043aec113c14c69ef45006bbc7546a4e75a`

The inspection covered selected root documentation, the report catalogue, the README summaries of the across-universes and birthday-cutoff reports, and a source preamble. It was not a full proof audit of the repository or an exhaustive novelty search. None of the repository's proposed new theorems is used as an unproved premise of this article. The repository was not modified.
