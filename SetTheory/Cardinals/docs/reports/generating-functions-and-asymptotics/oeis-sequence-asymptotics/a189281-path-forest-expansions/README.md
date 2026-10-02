# Unconditional All-Orders Asymptotics for Two OEIS Permutation Sequences

**Stable path forests, Poisson expansions, and index inversion for A189281 and A110128**

This research report is dated 1 October 2026. It was built from one manuscript, manuscript 60 of batch 73 of ProveIt's incoming-reports intake. The manuscript's author line is "Prepared for Vladimir Reshetnikov" (PDF metadata: "Research report prepared for Vladimir Reshetnikov").

| Source | Batch-73 manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| sole | 60 (cluster O2) | `oeis_path_forests.zip` (main file `article.tex`, 21-page PDF *Unconditional all-orders asymptotics for two OEIS permutation sequences*) | none | `aa43cc555` | `6e193dd4f` | the whole article |

The manuscript pins no repository revision. It cites the repository only by the path `Analysis/FabiusFunction/docs/ASYMPTOTIC_COMPLETION_AUDIT.md`, as an editorial example of separating a printed approximation, a correction and an all-orders theorem, and calls it "not a dependency". The archive arrived in `aa43cc555`; the placement commit `6e193dd4f` deleted it from `docs/incoming`, and it survives in `aa43cc555`.

**Status: AI-assisted, unrefereed, not formalized.** The intake reran every shipped program on a copy and spot-checked the mathematics (see "Checks by the intake"). It did not re-derive every proof.

## Files

```
README.md                          this guide
SOURCES.md                         the manuscript's source and novelty audit, as delivered
article.tex                        the report (LaTeX, internal bibliography)
article.pdf                        the compiled report, 23 pages
code/build.sh                      the delivered PDF build helper (does not work from code/; see below)
code/path_forests.py               exact coefficient formula, stable moments, full path-tiling enumerator (standard library)
code/validate.py                   brute-force distributions, OEIS values, stabilization, degree and coefficient checks
code/certify.py                    exact rational Bonferroni enclosures and scaled-residual certificates
code/check_collapse.py             finite symbolic tests of the rational-collapse conjecture, h = 4..16 (SymPy)
code/inverse.py                    numerical inverse diagnostics from exact values (mpmath); not certified
data/coefficients_order16.json     exact B_J and c_J through order 16; keys "1" (oriented) and "2" (absolute)
data/exact_values.json             n = 0..21 for both sequences, by full tiling enumeration
data/validation.json               counts and outcomes of the validation checks
data/validation.txt                standard output of validate.py
data/bonferroni_certificates.json  exact rational certificate endpoints
data/bonferroni_certificates.txt   standard output of certify.py
data/collapse_checks.txt           standard output of check_collapse.py (13 lines, h = 4..16, all True)
data/inverse_diagnostics.txt       standard output of inverse.py
data/requirements-optional.txt     sympy==1.14.0, mpmath==1.3.0 (for check_collapse.py and inverse.py only)
```

Every file except `README.md`, `article.tex` and `article.pdf` is byte-identical to the delivery. `article.pdf` is a build of this `article.tex`, not the delivered PDF. `data/coefficients_order16.json` has no final newline, as delivered.

## Labels

Every label carries the prefix `spf:`. The manuscript's 78 labels are kept, unchanged after the prefix. The write added three: `spf:rem:offsets-one-one`, `spf:rem:inverse-apparatus` and `spf:app:provenance` (81). A later reciprocal note added `spf:rem:clique-analogue` (82 in all).

## What is claimed

- **All-orders theorem** (Theorem 1.1, `spf:thm:main`). For fixed positive offsets r, s and θ ∈ {1, 2} (oriented or absolute differences), E(1+u)^X = e^{θu} Σ_{J≤M} B_J(u) n^{-J} + O(n^{-M-1}), uniformly for |u| ≤ U, with a finite formula for every B_J (`spf:eq:Bformula`). Also deg B_J ≤ 2J, B_J(u; r, s) = B_J(u; s, r), (2J)! B_J ∈ ℤ[u], and c_1 = θ(r+s−θ).
- **Structure.** An exact profile identity (Spahn–Zeilberger's matching-of-tilings formula at u = −1, reproved), a stable tiling polynomial independent of the individual path lengths (`spf:thm:stable`), the uniform factorial-moment bound μ_k ≤ (θe²)^k/k! (`spf:lem:moment-bound`), and total-variation universality with error exp(−η′ n log n + O(n)) (`spf:thm:universality`).
- **The whole law.** An all-orders signed Charlier approximation of the full distribution in ℓ¹ (`spf:cor:distribution`).
- **The two OEIS sequences.** A189281 (θ = 1) and A110128 (θ = 2), (r, s) = (2, 2), through n^{-10}. These recover, without the guessed recurrences, the expansions the OEIS entries attribute to those recurrences; Table 1 extends both to n^{-16}.
- **Inversion.** An all-orders Lambert-W index inversion along the sequence values (`spf:thm:inverse-first`, `spf:thm:inverse-all`), and Bonferroni certificates at n = 80, 160, 320.
- **Added in the write** (Remark 7.2): at (r, s) = (1, 1) the coefficient formula gives c_J^{(1)} = 1, 1, 0, 0, … (no successions, A000255(n−1) = D_n + D_{n−1}) and reproduces the Abramson–Moser expansion of A002464 (Hertzsprung's problem), as displayed in the OEIS entry, through n^{-10}. The intake checked this with the shipped generator and against exact counts to n = 800.

## What is not claimed

- **The rational collapse is a conjecture** (`spf:conj:collapse`): R_h(n) = 24 (n−h+1)^{\underline{h−4}} / n^{\underline{2h}} for h ≥ 4, checked as a rational-function identity for h = 4, …, 16 only. The integrality of every c_J^{(1)}(2, 2) is conditional on it (`spf:prop:collapse-implication`).
- Neither guessed OEIS recurrence (A189281's order-8, degree-11 recurrence; A110128's order-24, degree-64 operator) is proved.
- Only the algebraic asymptotic sector: no exponentially improved transseries, no geometry-dependent exponential sector, no optimal truncation (the expansion is a Poincaré statement with M fixed).
- Nothing uniform in growing offsets or for forests with a bounded short path.
- The inverse diagnostics are numerical, not certified integer thresholds.
- No peer review, no Lean or Rocq formalization, no historical priority beyond the sources reviewed. The leading Poisson behaviour, Tauraso's first correction in the diagonal absolute case and the inclusion–exclusion framework are credited, not claimed.
- Padhi's preprint (arXiv:2608.11290) is not a dependency. The intake confirmed that the record exists with the cited title but did not check its content.
- **The inversion method is not new.** Section 9 re-derives the canonical transseries volume's gamma-carrier inversion (`p6:thm:gamma`, `p0:thm:perturbed-inversion` in `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`), and its integer-threshold remark is an instance of that volume's `p0:thm:staircase`. Remark 9.1 cites them; no novelty is claimed there.

## Relation to neighbouring material

- **Sibling report** [`a330266-balanced-smirnov-poisson`](../a330266-balanced-smirnov-poisson/) (batch 73, manuscript 57): the same chain of method (exact marked-subset generating function, Poisson limit, all-orders 1/n expansion of E(1+v)^X, Lambert-W inversion) for a different model, equal-rank adjacencies in balanced multiset words with limit Poisson(k−1). Neither theorem specializes to the other, so the two are separate reports. That report's tail estimate is a sketch; its README names this report's uniform factorial-moment bound (`spf:lem:moment-bound`) as the device that would make it rigorous. Remark 7.4 here (`spf:rem:clique-analogue`, a reciprocal note) points to that report's first-order local law for P(X = j) (its Corollary 8.3, `bsw:cor:local`) as the clique-model analogue of the case M = 1 of Corollary 7.3 here.
- **Transseries volume** `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`: the inversion apparatus cited above, and its chapter "The subfactorial" (`p8:sec:top`), the closest analogue (derangements, by citing the same gamma carrier).
- **Fabius audit** `Analysis/FabiusFunction/docs/ASYMPTOTIC_COMPLETION_AUDIT.md`: cited by the manuscript as context only; not continued.
- **Formal status.** Placement in the collection confers no formal status, and no formal development continues this report; none of its statements is formalized. The only Lean declaration the report mentions (in a bracketed note at the end of Section 9), `Fabius.staircase_separation` (`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`), formalizes the separation step of the staircase theorem in general; it verifies nothing specific to this report.

## Building

From a scratch copy of `article.tex`, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX) produced the shipped `article.pdf`: 23 pages, with no errors, no warnings, no undefined references or citations, no multiply defined labels, no duplicate destinations, and no overfull or underfull boxes. Copy back only `article.pdf`.

The delivered `code/build.sh` changes into its own directory and runs `pdflatex` on `article.tex` there three times, writing `build/`. In the shipped layout it sits in `code/`, where there is no `article.tex`, so it fails; use the command above.

## Rerunning the programs

`validate.py` and `certify.py` write their JSON outputs into `../data/` relative to themselves (`data/exact_values.json`, `data/validation.json`, `data/bonferroni_certificates.json`), so running them in place overwrites the shipped records. Run every program on a copy of the report directory. Use `py` (or `uv run --no-project --with …`) without Python's `-O` flag, since the checks use assertions:

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a189281-path-forest-expansions
W=$(mktemp -d); cp -r "$R/code" "$R/data" "$W/"; cd "$W"
py code/path_forests.py --order 16 --output data/coefficients_order16.json   # about 7 s
py code/validate.py > data/validation.txt                                    # about 4 s; rewrites exact_values.json, validation.json
py code/certify.py > data/bonferroni_certificates.txt                        # about 2 min; rewrites bonferroni_certificates.json
uv run --no-project --with sympy==1.14.0 python code/check_collapse.py > data/collapse_checks.txt   # about 50 s
uv run --no-project --with mpmath==1.3.0 python code/inverse.py > data/inverse_diagnostics.txt     # about 1 s
py code/path_forests.py --r 1 --s 1 --order 10 --output offsets_1_1.json      # the (1,1) check of Remark 7.2
```

Compare the outputs with the shipped `data/` files. On Windows the regenerated text files have CRLF line endings, while the shipped ones are LF, so compare ignoring line endings (JSON as parsed). The intake's run on a copy matched in this sense; `collapse_checks.txt` differs only in its timings, and `coefficients_order16.json` also in its final newline, which the regenerated file has and the delivered one lacks.

## Checks by the intake

- Every shipped program rerun on a copy: all passed, outputs as described above.
- Both sequences recounted by brute force for n ≤ 9; equal to `data/exact_values.json`.
- The two order-ten expansions compared with the current OEIS entries: equal digit for digit (A189281: 3, 2, 1, 0, 3, 26, 101, 124, −1409, −13266; A110128: 4, 8, 68/3, …, 32213578294/14175).
- The coefficient d_1 of `spf:thm:inverse-first` rederived by hand (71/24 = 3 − 1/24, 95/24 = 4 − 1/24).
- The (1, 1) checks of Remark 7.2.

## Disclosures and discrepancies

- **Not shipped:** the delivered README (replaced by this one), the delivered 21-page PDF (replaced by a build of the edited text) and the checksum ledger `SHA256SUMS` (verified 19/19 at placement and retired).
- **Moved files.** The delivered `build.sh` is shipped as `code/build.sh` and `requirements-optional.txt` as `data/requirements-optional.txt`. The delivered README placed both at the archive root.
- **Delivery wording in shipped text.** The article's "the archive", "the accompanying JSON" and "the archive's README" mean this directory, `data/coefficients_order16.json` and this README; bracketed notes say so. `SOURCES.md` refers to "Section 11" for the rational collapse, which is still Section 11.
- **Edited text.** `article.tex` is the delivered manuscript with the label prefix, the editorial note after the status paragraph, Remarks 7.2 and 9.1, bracketed notes marked "[Added 1 October 2026, batch 73O2]", three bibliography entries (A000255, A002464, the transseries volume) and Appendix B (provenance), and, in a separate reciprocal note, Remark 7.4. Nothing was removed.
- **Overloaded letters** (kept, listed in Appendix B): C, K, d and D each carry two or more meanings in different sections.
