# Unconditional All-Orders Asymptotics for Two OEIS Permutation Sequences

**Stable path forests, Poisson expansions, and index inversion for A189281 and A110128 — Part II: fixed-gap asymptotics, a second derivation and its own results**

This research report is dated 1 October 2026. It was built from two manuscripts of ProveIt's incoming-reports intake, written independently of each other: manuscript 60 of batch 73 (Part I, the base) and manuscript 03 of batch 74 (Part II). Both prove the same main theorems; Part II prints only what manuscript 03 adds. Manuscript 60's author line is "Prepared for Vladimir Reshetnikov" (PDF metadata: "Research report prepared for Vladimir Reshetnikov"); manuscript 03's title page reads "Prepared for Vladimir Reshetnikov" and its PDF metadata names "ChatGPT, research report prepared for Vladimir Reshetnikov".

| Source | Manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| base | batch 73, no. 60 (cluster O2) | `oeis_path_forests.zip` (main file `article.tex`, 21-page PDF *Unconditional all-orders asymptotics for two OEIS permutation sequences*) | none | `aa43cc555` | `6e193dd4f` | Part I (Sections 1–13) and Appendix A; Appendix B added in the writes |
| addition | batch 74, no. 03 | `ProveIt_Fixed_Gap_Asymptotics.zip` (*All-Orders Asymptotics and Boundary Universality for Fixed-Gap Permutations*, 25-page PDF, 14 files) | `291fbe6bb` | `c664fc2f0` | `b669cff87` | Part II (Sections 14–22); files prefixed `02-fixed-gap-` |

Manuscript 60 pins no repository revision. It cites the repository only by the path `Analysis/FabiusFunction/docs/ASYMPTOTIC_COMPLETION_AUDIT.md`, as an editorial example of separating a printed approximation, a correction and an all-orders theorem, and calls it "not a dependency". Manuscript 03 pins `291fbe6bb4477e0cb2131f1e041b12a9abe363fd` (2026-10-01 18:10, "Index the387-operation C2 construction and both new degree frontiers"). That commit already held manuscript 60's archive, unopened, in `docs/incoming`; the two texts share about 1.1 % of their word 8-grams (bibliography entries and coefficient digits). Each placement commit deleted its archive from `docs/incoming`; the archives survive in the arrival commits `aa43cc555` and `c664fc2f0`.

**Status: AI-assisted, unrefereed, not formalized.** The intakes reran every shipped program of both manuscripts on copies and spot-checked the mathematics (see "Checks by the intake"). They did not re-derive every proof.

## Files

```
README.md                          this guide (replaces both delivered READMEs)
SOURCES.md                         manuscript 60's source and novelty audit, as delivered
02-fixed-gap-sources.md            manuscript 03's source audit and provenance, as delivered
article.tex                        the report (LaTeX, internal bibliography)
article.pdf                        the compiled report, 36 pages
code/build.sh                      (60) the delivered PDF build helper (does not work from code/; see below)
code/path_forests.py               (60) exact coefficient formula, stable moments, full path-tiling enumerator (standard library)
code/validate.py                   (60) brute-force distributions, OEIS values, stabilization, degree and coefficient checks
code/certify.py                    (60) exact rational Bonferroni enclosures and scaled-residual certificates
code/check_collapse.py             (60) finite symbolic tests of the rational-collapse conjecture, h = 4..16 (SymPy)
code/inverse.py                    (60) numerical inverse diagnostics from exact values (mpmath); not certified
code/02-fixed-gap-fixed_gap.py     (03) exact tiling enumerator and finite-defect coefficient engine (SymPy)
code/02-fixed-gap-verify.py        (03) its checks; regenerates the six 02-fixed-gap- data files below (SymPy, mpmath)
data/coefficients_order16.json     (60) exact B_J and c_J through order 16; keys "1" (oriented) and "2" (absolute)
data/exact_values.json             (60) n = 0..21 for both sequences, by full tiling enumeration
data/validation.json               (60) counts and outcomes of the validation checks
data/validation.txt                (60) standard output of validate.py
data/bonferroni_certificates.json  (60) exact rational certificate endpoints
data/bonferroni_certificates.txt   (60) standard output of certify.py
data/collapse_checks.txt           (60) standard output of check_collapse.py (13 lines, h = 4..16, all True)
data/inverse_diagnostics.txt       (60) standard output of inverse.py
data/requirements-optional.txt     (60) sympy==1.14.0, mpmath==1.3.0 (for check_collapse.py and inverse.py only)
data/02-fixed-gap-coefficients.csv (03) c_j of A189281 and A110128, orders 0..12, exact rationals
data/02-fixed-gap-component_weight_polynomials.txt (03) the coefficients at r = s = 2 with symbolic orientation weight
data/02-fixed-gap-general_pgf_first_three.txt (03) B_1, B_2, B_3 in symbolic r, s, for both orientations
data/02-fixed-gap-numerics.csv     (03) unscaled errors of the A189281 expansion and of the inverse at n = 20, 40, 80, 120
data/02-fixed-gap-selected_oeis_values.csv (03) the A189281 b-file values used as inputs (n = 20, 40, 80, 120)
data/02-fixed-gap-verification.txt (03) the delivered run's summary output
data/02-fixed-gap-requirements.txt (03) sympy==1.14.0, mpmath==1.3.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is byte-identical to its delivery. `article.pdf` is a build of this `article.tex`, not either delivered PDF. `data/coefficients_order16.json` has no final newline, as delivered. Manuscript 03's three CSV files are CRLF as delivered and are kept so by `-text` lines in `SetTheory/Cardinals/.gitattributes`.

## Labels and numbering

Part I's labels carry the prefix `spf:`. The manuscript's 78 labels are kept, unchanged after the prefix. The batch-73O2 write added three: `spf:rem:offsets-one-one`, `spf:rem:inverse-apparatus` and `spf:app:provenance` (81), and a later reciprocal note added `spf:rem:clique-analogue` (82). The batch-74 write added **49** labels with the prefix `fga:`, all in Part II: **131** labels in all. No existing label was renamed or removed, and no existing section, statement, equation or table number changed (checked against the `.aux` of the previous build): Part II follows Part I's conclusion as Sections 14–22 and Tables 3–6, before the appendices. In new text, references to Part I's lemmas, propositions, corollaries, definitions, conjectures and remarks are written with explicit names, because Part I's shared theorem counter makes `\cref` print them as "theorem".

## What is claimed

**Part I** (manuscript 60):

- **All-orders theorem** (Theorem 1.1, `spf:thm:main`). For fixed positive offsets r, s and θ ∈ {1, 2} (oriented or absolute differences), E(1+u)^X = e^{θu} Σ_{J≤M} B_J(u) n^{-J} + O(n^{-M-1}), uniformly for |u| ≤ U, with a finite formula for every B_J (`spf:eq:Bformula`). Also deg B_J ≤ 2J, B_J(u; r, s) = B_J(u; s, r), (2J)! B_J ∈ ℤ[u], and c_1 = θ(r+s−θ).
- **Structure.** An exact profile identity (Spahn–Zeilberger's matching-of-tilings formula at u = −1, reproved), a stable tiling polynomial independent of the individual path lengths (`spf:thm:stable`), the uniform factorial-moment bound μ_k ≤ (θe²)^k/k! (`spf:lem:moment-bound`), and total-variation universality with error exp(−η′ n log n + O(n)) (`spf:thm:universality`).
- **The whole law.** An all-orders signed Charlier approximation of the full distribution in ℓ¹ (`spf:cor:distribution`).
- **The two OEIS sequences.** A189281 (θ = 1) and A110128 (θ = 2), (r, s) = (2, 2), through n^{-10}. These recover, without the guessed recurrences, the expansions the OEIS entries attribute to those recurrences; Table 1 extends both to n^{-16}.
- **Inversion.** An all-orders Lambert-W index inversion along the sequence values (`spf:thm:inverse-first`, `spf:thm:inverse-all`), and Bonferroni certificates at n = 80, 160, 320.
- **Added in the batch-73O2 write** (Remark 7.2): at (r, s) = (1, 1) the coefficient formula gives c_J^{(1)} = 1, 1, 0, 0, … (no successions, A000255(n−1) = D_n + D_{n−1}) and reproduces the Abramson–Moser expansion of A002464 (Hertzsprung's problem), as displayed in the OEIS entry, through n^{-10}. The intake checked this with the shipped generator and against exact counts to n = 800.

**Part II** (manuscript 03). Its re-derivations of Part I's theorems are listed as second routes in Table 5 and not reprinted; its coefficients of A189281 and A110128 through order 12 equal Part I's and are **not new** (Part I already has orders 11–16). New:

- **Uniformity over forest shapes** (Theorem 16.6, Corollary 16.7): the expansion holds with a constant independent of the individual path lengths for every pair of forests whose shortest path has at least K_n = ⌊(M+4) log n/log log n⌋ vertices — in particular whenever L_min log log n/log n → ∞ — but only on the disk |1+u| ≤ 1, i.e. |u| ≤ 2, which is weaker in u than Part I. (Remark 16.8, an observation of the write, notes that Part I's own proof gives the shape-uniform statement on every disk |u| ≤ U.)
- **Comparison bounds** (Theorem 16.3): for two forest pairs with the same path counts and all paths of at least K vertices, bounds on the difference of the whole generating functions and of the avoidance probabilities, and a second total-variation bound; and an n = 12 example (Remark 16.4) whose moments agree through k = 4 while the counts differ.
- the sharper moment bound μ_k ≤ θ^k (1−2k/n)^{−2k}/k! and a defect-sensitive bound (Lemmas 16.1, 16.5);
- **B_J as a polynomial in the offsets** of total degree at most J in (r, s) (Proposition 17.1), and **closed forms of c_3^{(θ)}(r, s)** for both orientations (Proposition 17.2);
- **proved all-orders integrality for the oriented one-path family**: if r = 1 or s = 1, then B_J^{(1)}(u; r, s) ∈ ℤ[u] for every J (Proposition 18.1, Corollary 18.2). This does **not** cover A189281, whose offsets are (2, 2);
- explicit first-order local laws P(X = j) for both sequences (Section 19);
- the inverse in a coordinate that absorbs κ_θ, with explicit terms through N^{−3} (Proposition 20.1), and a_2 = 0, a_3 = 4319/360 for A110128;
- six research questions not in Part I (Section 22).

**Not new here:** the inversion method (both Parts; see below), the leading Poisson behaviour, Tauraso's first correction in the diagonal absolute case and the inclusion–exclusion framework, which both manuscripts credit.

## What is not claimed

These are both manuscripts' own limits, kept in full (manuscript 60's article, `SOURCES.md` and delivered README; manuscript 03's abstract, its "Scope and priority" paragraph, the remarks after its theorems, `02-fixed-gap-sources.md` "What the computations do not establish" and its delivered README).

- **The rational collapse is a conjecture** (`spf:conj:collapse`): R_h(n) = 24 (n−h+1)^{\underline{h−4}} / n^{\underline{2h}} for h ≥ 4, checked as a rational-function identity for h = 4, …, 16 only. The integrality of every c_J^{(1)}(2, 2) is conditional on it (`spf:prop:collapse-implication`). **All-orders integrality for A189281 is not claimed.** What Part II proves is integrality for the oriented one-path subfamily (r = 1 or s = 1) only; manuscript 03 itself warns against extrapolating it to two paths on both sides.
- Neither guessed OEIS recurrence (A189281's order-8, degree-11 recurrence; A110128's order-24, degree-64 operator) is proved, by either manuscript.
- Only the algebraic asymptotic sector: no exponentially improved transseries, no geometry-dependent exponential sector, no Borel summability, Stokes data or optimal truncation (the expansion is a Poincaré statement with M fixed).
- Nothing uniform in growing offsets; Part II's shape uniformity needs every path to have at least K_n ≍ log n/log log n vertices, and the threshold is not claimed to be sharp.
- The inverse diagnostics and manuscript 03's numerical tables are uncertified decimals; manuscript 03's values of A189281 at n = 80 and 120 are b-file inputs, not regenerated. Part I's Bonferroni intervals are the certified counterpart.
- No peer review, no Lean or Rocq formalization, no historical priority beyond the sources reviewed by either manuscript.
- Padhi's preprint (arXiv:2608.11290) is not a dependency of either manuscript. The intake confirmed that the record exists with the cited title but did not check its content.
- **The inversion method is not new.** Section 9 re-derives the canonical transseries volume's gamma-carrier inversion (`p6:thm:gamma`, `p0:thm:perturbed-inversion` in `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`), and its integer-threshold remark is an instance of that volume's `p0:thm:staircase`. Remark 9.1 cites them. Manuscript 03's inverse (Section 20) is another instance of the same apparatus, in coordinates shifted by κ_θ; no novelty is claimed for either.
- Neither manuscript submitted anything to the OEIS. Manuscript 03's proposed OEIS additions (orders 11 and 12) are already exceeded by Part I's Table 1.

## Relation to neighbouring material

- **Sibling report** [`a330266-balanced-smirnov-poisson`](../a330266-balanced-smirnov-poisson/) (batch 73, manuscript 57): the same chain of method (exact marked-subset generating function, Poisson limit, all-orders 1/n expansion of E(1+v)^X, Lambert-W inversion) for a different model, equal-rank adjacencies in balanced multiset words with limit Poisson(k−1). Neither theorem specializes to the other, so the two are separate reports. That report's tail estimate is a sketch; its README names this report's uniform factorial-moment bound (`spf:lem:moment-bound`) as the device that would make it rigorous. Remark 7.4 here (`spf:rem:clique-analogue`, a reciprocal note) points to that report's first-order local law for P(X = j) (its Corollary 8.3, `bsw:cor:local`) as the clique-model analogue of the case M = 1 of Corollary 7.3 here.
- **Transseries volume** `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`: the inversion apparatus cited above, and its chapter "The subfactorial" (`p8:sec:top`), the closest analogue (derangements, by citing the same gamma carrier). Its repair box already lists several sources that re-derive the gamma-envelope inverse; manuscript 03 is another.
- **Fabius audit** `Analysis/FabiusFunction/docs/ASYMPTOTIC_COMPLETION_AUDIT.md`: cited by manuscript 60 as context only; not continued.
- **Formal status.** Placement in the collection confers no formal status, and no formal development continues this report; none of its statements is formalized. The only Lean declaration the report mentions (in a bracketed note at the end of Section 9), `Fabius.staircase_separation` (`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`), formalizes the separation step of the staircase theorem in general; it verifies nothing specific to this report.

## Building

From a scratch copy of `article.tex`, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX) produced the shipped `article.pdf`: 36 pages, with no errors, no warnings, no undefined references or citations, no multiply defined labels, no duplicate destinations, and no overfull or underfull boxes. Copy back only `article.pdf`.

The delivered `code/build.sh` changes into its own directory and runs `pdflatex` on `article.tex` there three times, writing `build/`. In the shipped layout it sits in `code/`, where there is no `article.tex`, so it fails; use the command above.

## Rerunning the programs

Run every program on a copy, never in the report directory, and without Python's `-O` flag (the checks use assertions).

**Manuscript 60.** `validate.py` and `certify.py` write their JSON outputs into `../data/` relative to themselves (`data/exact_values.json`, `data/validation.json`, `data/bonferroni_certificates.json`), so running them in place overwrites the shipped records:

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

**Manuscript 03.** `02-fixed-gap-verify.py` imports its sibling by the delivered name (`from fixed_gap import …`), which fails under the prefixed name, and writes six **unprefixed** files into `../data/` relative to itself, which in the report directory would land beside manuscript 60's data. Restore the delivered names in a scratch directory:

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a189281-path-forest-expansions
W=$(mktemp -d); mkdir -p "$W/code"
cp "$R/code/02-fixed-gap-fixed_gap.py" "$W/code/fixed_gap.py"
cp "$R/code/02-fixed-gap-verify.py"    "$W/code/verify.py"
cd "$W"; uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python code/verify.py --order 12
# writes data/{coefficients.csv, component_weight_polynomials.txt, general_pgf_first_three.txt,
#              numerics.csv, selected_oeis_values.csv, verification.txt}; compare with $R/data/02-fixed-gap-*
```

At the batch-74 write (Windows, Python 3.14, SymPy 1.14.0, mpmath 1.3.0) this order-12 run took 104 s; all eight checks passed; the three CSV files were byte-identical to the shipped ones, the two `.txt` polynomial files equal apart from CRLF line ends, and `verification.txt` equal apart from line ends and its timing line. At the intake, on the same machine under load, the order-12 run exceeded 170 s and was stopped; `--order 9` passed all checks in 72 s, and the order-11 and order-12 coefficients were recomputed separately and equal the shipped ones. A smaller `--order` rewrites the data files with shorter tables.

## Checks by the intake

- Batch 73O2: every shipped program of manuscript 60 rerun on a copy (all passed, outputs as described above); both sequences recounted by brute force for n ≤ 9, equal to `data/exact_values.json`; the two order-ten expansions compared with the current OEIS entries, equal digit for digit (A189281: 3, 2, 1, 0, 3, 26, 101, 124, −1409, −13266; A110128: 4, 8, 68/3, …, 32213578294/14175); the coefficient d_1 of `spf:thm:inverse-first` rederived by hand (71/24 = 3 − 1/24, 95/24 = 4 − 1/24); the (1, 1) checks of Remark 7.2.
- Batch 74: manuscript 03's coefficients of both sequences at orders 0–12 equal Part I's `data/coefficients_order16.json` exactly; its general B_2 equals Part I's for both orientations identically in r, s, u (SymPy); its B_1, B_2, B_3 at (2, 2) equal Part I's; its closed forms of c_1, c_2, c_3 (Proposition 17.2) equal the values of Part I's generator at (r, s) = (1, 1), (1, 3), (2, 3), (3, 3), (2, 5) for both orientations; its third inverse coefficient reduces, in the pure-gamma case, to the corresponding block of `p6:thm:gamma`; its uncertified errors at n = 80, 120, scaled by n^{11} and n^{13}, approach Part I's c_11 and c_13 (Section 21); its program rerun as above. These checks do not replace an independent review of the proofs.

## Disclosures and discrepancies

- **Not shipped:** both delivered READMEs (replaced by this one), both delivered PDFs (replaced by a build of the edited text), manuscript 03's `article.tex` (merged as Part II), and the checksum ledgers `SHA256SUMS` of manuscript 60 (19/19) and `SHA256SUMS.txt` of manuscript 03 (13/13), verified at placement and retired.
- **Moved and renamed files.** Manuscript 60's `build.sh` is shipped as `code/build.sh` and `requirements-optional.txt` as `data/requirements-optional.txt`; its README placed both at the archive root. Manuscript 03's `code/X` is `code/02-fixed-gap-X`, its `data/X` is `data/02-fixed-gap-X`, its `requirements.txt` is `data/02-fixed-gap-requirements.txt`, and its `sources.md` is `02-fixed-gap-sources.md`.
- **Delivery wording in shipped text.** Manuscript 60's "the archive", "the accompanying JSON" and "the archive's README" mean this directory, `data/coefficients_order16.json` and this README; bracketed notes say so. `SOURCES.md` refers to "Section 11" for the rational collapse, which is still Section 11. `code/02-fixed-gap-verify.py` and `02-fixed-gap-sources.md` use manuscript 03's delivery names (`code/fixed_gap.py`, `code/verify.py`, `data/…`, `requirements.txt`).
- **Stale sentence.** `02-fixed-gap-sources.md` says a GitHub code search for A189281 "returned total_count=0" at the pinned commit; manuscript 03's article says the same. The pin already held manuscript 60's archive, which code search cannot read (bracketed note in Section 14.1).
- **Run time.** Manuscript 03's README promises "tens of seconds" for `verify.py --order 12`, and `data/02-fixed-gap-verification.txt` records "Completed in 22.44 seconds"; here it took 104 s to more than 170 s (above).
- **Edited text.** `article.tex` is manuscript 60's text with the label prefix, the batch-73O2 editorial note, Remarks 7.2 and 9.1, bracketed notes marked "[Added 1 October 2026, batch 73O2]", three bibliography entries (A000255, A002464, the transseries volume), Appendix B (provenance) and, in a separate reciprocal note, Remark 7.4; and, from the batch-74 write, the two part headings, a batch-74 editorial note, bracketed notes marked "[Added 1 October 2026, batch 74]" (after the proof of Theorem 1.1, in research questions 1 and 5, in Appendix B), Part II, two bibliography entries (the A189281 b-file and manuscript 03's pinned repository) and a table-of-contents line "Appendices". Nothing was removed. Manuscript 03's text is restated in Part I's notation, with some proofs condensed.
- **Overloaded letters.** Part I's C, K, d and D each carry two or more meanings in different sections (listed in Appendix B, kept). Manuscript 03 overloads D, w, T, A and B and swaps several of Part I's letters (η and θ, H_h and Q, S_k, K, d_j); Part II renames all of them into Part I's notation, as listed in its Table 4.

## Provenance

Appendix B of the article records both sources, their pins, where the batch-74 merge had to choose and what each write changed. The placement commit `6e193dd4f` records the batch-73O2 decisions; the placement commit `b669cff87` records the batch-74 decision: manuscript 03 proves this report's main theorems in independent text, with every shared number equal, so it is added as Part II holding only its own results, with its re-derivations as marked second routes.
