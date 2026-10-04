# Self-Embeddings of the Surreal Numbers
## Rigidity, Hahn lifts, topology, and size-safe foundations

Research article prepared for Vladimir Reshetnikov, 3 October 2026.

## Files

- `article.pdf`: the compiled research article.
- `article.tex`: complete, self-contained LaTeX source, including references.
- `verify.py`: exact finite regression tests; Python standard library only.
- `verification.json` and `verification.txt`: output from the executed tests.
- `build.sh`: LaTeX build command with basic dependency checking.
- `SOURCE_AUDIT.md`: pinned sources, scope of inspection, and verification limits.

## Main content

The article distinguishes order, simplicity, birthday, field, normal-form,
valuation, exponential, elementary, definability, omnific, differential,
and universe-relative interpretations of self-embedding.

It gives a two-stage Hahn lift from arbitrary increasing class embeddings
into strongly real-linear field embeddings. This yields proper cofinal
continuous embeddings fixing all reals, all ordinals, and any prescribed
set of additional surreal numbers, with closed nowhere-dense images.
It also constructs bounded field copies fixing prescribed set-sized data.

Further results include weighted monomial classification, fixed fields,
reversible cores, the cofinality/continuity dichotomy, closed simplicity
substructures and their fixed points, controlled unit and coefficient
perturbations, exponential valuation rigidity, and uniqueness of cofinal
exponential embeddings having the same value-group action.

The final sections give a universe-sensitive formalization architecture
and 18 proposed research questions.

## Build

A TeX Live installation with the standard packages used by `article.tex`
(including newtx, amsmath, amsthm, mathtools, tcolorbox, xurl, hyperref,
and cleveref) is sufficient.

```sh
./build.sh
```

Equivalently:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

To run the finite regression checks with Python 3.10 or later:

```sh
python3 verify.py
```

No external images or custom font files are needed. Fonts are not distributed
as separate files in this package.

## Evidence and limitations

This is a research synthesis with mathematical proofs in the text, not a
claim of publication priority or of independent peer review. It separates
standard literature, generic repository theorems, arguments developed in
the article, and unresolved directions.

No new Lean verification and no independent build of ProveIt were performed.
The inspected generic exponential-profile Lean module explicitly identifies
its actual surreal-exponential instantiation as pending. The corresponding
bridge is supplied here as a conventional mathematical proof, not as a
machine-checked theorem.

The 195,579 exact finite checks passed. They detect transcription errors;
they are not proofs about arbitrary ordinal-length signs, proper classes,
all real coefficients, or all reverse well-ordered supports.

Repository snapshot:
`b0d4af4f30b24529fec877e2ad4a5952888146e9`.
