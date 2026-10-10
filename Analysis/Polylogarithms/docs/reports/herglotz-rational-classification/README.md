# Rational Herglotz Companion Values

**Dyadic descent, complete formal classification, and explicit dilogarithm identities**

Research continuation for the ProveIt Polylogarithms manuscript. The package contains a 22-page article, all LaTeX sources, a standalone source variant, reproducible exact and numerical checks, frozen results, and additive integration material. No repository write or commit has been made.

## Main result

For the companion

`J(x) = integral_0^1 log(1+t^x)/(1+t) dt`,

reduce `p/q` to lowest terms.

* For mixed parity, let `e` be the even entry and `o` the odd entry. Formal logarithmic reduction and formal rational-dilogarithmic reduction coincide. They hold exactly when `e^2 = +/-1 (mod o)` and `o^2 = 1 (mod 2e)`.
* For two odd entries, formal rational-dilogarithmic reduction holds exactly when both entries belong to `{1,3,5}`. Formal logarithmic reduction holds only at `p=q=1`.

Thus the six rational-dilogarithmic but non-logarithmic formal exceptions are `1/3, 3, 1/5, 5, 3/5, 5/3`.

“Formal” refers to the rationalized pre-Bloch/five-term calculus specified in the article. This is **not** a classification of all possible numerical identities between transcendental constants. No period-injectivity, numerical-independence, or proof-assistant verification claim is made.

## Further proved results

The article gives an exact odd-conductor doubling law, a new dyadic-layer rigidity theorem, a complete even-coefficient quadratic-recurrence parametrization of all logarithmic pairs, and a height expansion to every fixed order. With `N(B)` counting unordered logarithmic pairs of height at most `B`,

`N(B) = (3/2) B + sum_{r=2}^R B^(1/r) + O_R(B^(1/(R+1)) log B)`.

There is a full real-logarithmic formula for every neighboring ratio `J(n/(n+1))`. In particular, with `phi=(1+sqrt(5))/2`,

`J(3/5) = Li_2(1/3) - (1/2)Li_2(1/5) + (1/2)log(2)^2 + (1/2)log(3)^2 - (1/4)log(5)^2 + log(phi)^2 - 7*pi^2/180`.

The analytic proof retains every logarithmic and pi-squared term and uses Rogers identities only on `(0,1)`. The article also includes an exact prime-seven counterexample to a finite-field assertion in the reviewed Radchenko–Zagier preprint. See `AUDIT.md` for the precise scope; the manuscript's direct rational boundary formula remains valid.

## Read and build

`article.pdf` is the compiled article. `article.tex` uses the files in `sections/` and `references.tex`. `article-standalone.tex` is a mechanically flattened version with no project-local input dependencies; either source builds the same mathematical text.

```sh
python -m pip install -r requirements.txt
python code/verify_exact.py --bound 500
python code/verify_numeric.py --dps 90 140
python code/classify.py 3 5
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, use `make check` and `make pdf`. The TeX build requires a standard LaTeX installation with the packages declared in the source. Python 3.10 or later is recommended; the recorded run used Python 3.13.5, SymPy 1.14.0 and mpmath 1.3.0. No network calls are made by the verification scripts after dependencies have been installed.

The classifier accepts positive integers and reduces the fraction automatically. For example, `python code/classify.py 8 3` returns a failed new-layer test: checking only modulo the even entry, rather than twice that entry, would be wrong.

## Verification evidence

The frozen exact run checks 50,700 first differences, 50,700 second differences, 50,828 new-layer group-ring witnesses, and 2,106 free-exterior conductor-doubling instances. It compares the congruence classifier with an independent recurrence generator on 76,115 coprime unordered pairs. It also checks 500 exact height counts, 62 recurrence-polynomial coefficient instances, the prime-seven defect, and the symbolic substitutions behind the analytic identities.

The independent numerical run performs 38 defining-integral comparisons at 90 decimal digits and repeats all 38 at 140 digits. These are arbitrary-precision diagnostics, **not interval-certified error bounds**. The proofs of equality and of the all-parameter statements are in the article.

The package includes `data/exact_results.json`, `data/numeric_results.json`, `data/logarithmic_pairs.csv`, `data/counts.csv`, and a theorem ledger. `VALIDATION.md` records the build and visual checks. `MANIFEST.sha256` records checksums of the deliverable files.

## Provenance and integration

The reviewed manuscript snapshot is:

`cc34f73596336f2466d9754cb0f3635bd2bedade`

The principal source chapter is `Analysis/Polylogarithms/docs/manuscript/chapters/09-herglotz.tex`, Git blob `b372a62797ae9161ddcfd9f4edd036ecfd87df36`. The discovery chapter explicitly lists the general rational `J` symbol problem as open. The existing all-conductor symbol theorem and classical Herglotz/Hecke identities are attributed inputs, not claimed as new here.

A suggested destination is:

`Analysis/Polylogarithms/docs/reports/herglotz-rational-classification/`

See `integration/README.md` for a proposed additive manuscript fragment and bibliography entry. The original manuscript files have not been modified. This package does not change the status of Gaussian, `S_6`, or unrelated polylogarithmic conjectures.

The proofs and computation records are provided for mathematical review before integration. Newness is relative to the reviewed manuscript; no exhaustive priority claim is made.
