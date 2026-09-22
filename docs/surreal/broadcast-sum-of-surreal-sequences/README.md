# A Number-Valued Broadcast Sum of Surreal Sequences

**Commuting truncations and an exact failure of monotonicity**  
Research manuscript prepared with ChatGPT, September 20, 2026.

## Main result and scope

The paper analyzes the sign-truncation game proposed in Paolo Lipparini,
*Monotone infinitary operations on ordinals (extended version)*,
arXiv:2505.00424v2, Remark 7.6(3), in connection with Problem 7.5.
The underlying rule is Lipparini's. “Broadcast sum” and the notation B are local
to this manuscript.

The manuscript gives proofs that the game always has a surreal-number value,
that it agrees with finite surreal sums and with Lipparini's ordinal operation
on their respective domains, and that it fails weak coordinatewise monotonicity.

For d >= 2 and E a subset of the nonnegative integers, let

    s[n] = 3 * 2^(-n-d-1)  when n belongs to E,
           2^(-n-d)        otherwise.

The proved formula in the manuscript is

    B(s) = |E| + 1       when E is finite,
           sqrt(omega)   when E is infinite.

For example:

    B(3/8, 3/16, 3/32, ...) = sqrt(omega),
    B(1/2, 1/4, 1/8, ...)  = 1.

Every term of the first sequence is smaller than its counterpart in the second.
The square root here is in the surreal field, not an ordinal fractional power.

**Research status:** These are unrefereed research claims with full written
proofs, not proof-assistant-certified results. The finite tests are not proofs
of the infinite statements. No claim of established priority is made, and no
alternative weakly monotone summation theory is constructed or ruled out.

## Proof review corrections

The September 22, 2026 repository review makes the index-set hypotheses
explicit. The finite-short-perturbation corollary compares a family with the
constant family on the **same index set**. The constant-dyadic theorem applies
to every infinite index set, and the cofinite leading-scale corollary requires
that infinitude hypothesis. Without it, even the singleton `(1)` would
incorrectly be assigned a value within a finite distance of omega.

The rule now includes a limit-ordinal threshold example and a proof of the
no-moves criterion. A position has no options for either player exactly when
all coordinates are zero; normal play can end earlier when the current player
has no move. Ordinal thresholds do not introduce turns at limit times. The
termination discussion also gives actual alternating plays of unbounded
finite length from `(omega, -omega)`.

The code and recorded finite-test data are preserved. This proof review and PDF
rebuild do not constitute a new run of those tests or a Lean formalization.

## Files

- `article.pdf`: the 20-page article, including title page and contents.
- `article.tex`: complete editable LaTeX source.
- `references.bib`: bibliography with source identifiers.
- `article.bbl`: generated bibliography, retained for easy LaTeX-only viewing.
- `build.sh`: reproducible PDF build script.
- `code/broadcast_finite.py`: exact finite sign/game implementation.
- `code/verify.py`: exhaustive finite checks and example-data generation.
- `verification/test_report.json`: actual finite test results.
- `verification/partial_sums.csv`: exact finite partial sums; infinite-value
  columns are explicitly labeled as theorem-derived.
- `verification/proof_audit.md`: mathematical scope and proof-dependency audit.
- `verification/document_check.json`: preserved original PDF build and layout
  record; see the proof audit for validation of the revised PDF.

No source papers or font files are redistributed.

## Reproduce the finite checks

Python 3.10 or newer, standard library only:

```sh
python code/verify.py
```

All rational calculations use `fractions.Fraction`. No floating-point comparison
is used to evaluate games. The evaluator recursively constructs the actual
finite game cuts; it does not simply return the ordinary coordinate sum.

The checked finite families are pairs of strings of length at most 4 and triples
of strings of length at most 3. Separate tests cover 135,156 truncation
commutations, 3,378 legal opposite-move diamonds, and the dyadic sign formulas.

**Do not extrapolate finite game values to the infinite operation.** The paper
proves that this can give a different answer, even for positive convergent real
series. The program intentionally has no “infinite sequence evaluator.”

## Build the PDF

A LaTeX installation with Latin Modern, AMS packages, geometry, microtype,
xcolor, booktabs, enumitem, fancyhdr, titlesec, hyperref and bookmark is needed.
All are standard TeX packages.

```sh
sh build.sh
```

The script uses `pdflatex` and either `bibtex` or `bibtex8`. On systems without a
shell, run these commands in the project directory:

```text
pdflatex article.tex
bibtex article
pdflatex article.tex
pdflatex article.tex
```

An additional `pdflatex` pass is harmless if page references change after edits.
A prebuilt `article.bbl` is included, so a direct LaTeX compile can display the
existing bibliography even before regeneration.

## Primary problem source

Paolo Lipparini, arXiv:2505.00424v2 (April 30, 2026), Problem 7.5 and Remark
7.6(3), printed pages 36–37:

https://arxiv.org/abs/2505.00424v2

The exact sign rule was checked against printed page 37. The arXiv record says
that v2 is an extended version of the published *A Monotone Infinitary Operation
on Ordinals*, Mathematical Logic Quarterly 72 (2026), DOI 10.1002/malq.70019.
The extended source, not merely the shortened published article, is the target.
