# Every Countable Turing Ideal as Coarse Common Information
## Exact spectra and Turing-cone embeddings with a fixed core

Research manuscript prepared for Vladimir Reshetnikov, 28 September 2026.

## Main results

- **Theorem 5.1:** The possible coarse common-information cores of binary sets
  are exactly the countable Turing ideals. A concrete column construction
  realizes an arbitrary presented ideal.
- **Theorem 6.2:** The representative spectrum of the construction is exactly
  characterized by a computable array with eventually correct whole rows.
  The order of quantifiers is essential.
- **Theorems 8.2 and 8.4:** Joining any base set with a set of coarse computability
  bound 1 preserves the base core. Joining with the dyadic code of H intersects
  its spectrum with the degrees whose jumps compute H.
- **Theorem 9.2:** Above every coarse degree, a join-preserving copy of a full
  Turing upper cone occurs without changing the core. This holds for both
  uniform and nonuniform coarse reducibility, with distinct spectra for distinct
  input degrees.
- **Corollary 9.4:** Each prescribed-core collection has no maximal member and
  no countable cofinal subset.

The paper also gives an arithmetic-ideal example whose representative spectrum
has no infimum and eight further research questions.

## What is, and is not, claimed

The ideal-realization result resolves an explicit question in the inspected
ProveIt synthesis. Its construction has a close published antecedent in
Hirschfeldt–Jockusch–Schupp (2021), and its upper bound uses the
Hirschfeldt–Jockusch–Kuyper–Schupp cone-avoiding compactness principle. Those
antecedents are credited; they are not relabeled as new discoveries.

This is an unrefereed research manuscript with explicit mathematical proofs.
It is not a Lean-verified development, and global novelty has not been
established by an exhaustive literature search. It does not resolve the general
effective-dense least-representative problem or characterize all possible
coarse spectra. Absence of a least member is not confused with absence of
minimal members.

## Files

- `article.pdf`: compiled 22-page article.
- `article.tex`: complete LaTeX source, including bibliography.
- `build.sh`: three-pass PDF build.
- `PROOF_AUDIT.md`: dependency and quantifier audit.
- `SOURCE_LEDGER.md`: repository revision and published antecedents.
- `checks/finite_checks.py`: standard-library Python finite checks.
- `checks/results.json`: results from the delivered run.
- `validation.json`: document and build checks.

## Rebuild

A normal TeX Live or MiKTeX installation must provide the packages listed in
`article.tex`, including `newpxtext`, `newpxmath`, `tcolorbox`, and `xurl`.
No bibliography download, external `.bib` file, figures, or network connection
is required.

On a system with Bash:

```sh
./build.sh
```

Alternatively run this command three times, from the directory containing the
source (also suitable for a Windows terminal with pdflatex on PATH):

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Run the finite checks with Python 3.10 or newer:

```sh
python checks/finite_checks.py
```

The checks test finite arithmetic and coding geometry, not infinite-oracle
computations, Baire category, jump inversion, or entire mathematical theorems.
Re-running them replaces only `checks/results.json` by default.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit: `1a1396d4d3a2ac6812692df520517d86ba3a4785`

Primary source:
`Computability/TuringDegrees/Research/CoarseDegrees/research-synthesis/Turing_Degrees_Synthesis.tex`

The repository was read, not modified.
