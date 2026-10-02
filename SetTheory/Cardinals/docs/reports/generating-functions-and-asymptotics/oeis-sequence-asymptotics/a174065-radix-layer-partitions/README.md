# Log-Periodic Factors in Radix-Layer Partition Asymptotics

**The OEIS equivalents of A174065 and A393565 omit a nonconstant
log-periodic factor: an expansion of `∏_{j≥0,i≥1}(1 + z^(i b^j))` to every
fixed order with explicit differential operators, the interval of
subsequential ratio limits, exact radial reciprocity, inverse formulas,
integer enclosures, eventual increase and log-concavity**

A research report dated 2 October 2026, built from one manuscript. Its
author line reads only "Research report"; the delivery names no author and
no tool.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 60 (cluster P4) | `radix-partition-reproducibility.zip` (wrapper directory `radix-partition-report/`), arrival commit `096ee7b87`; main file `radix_partition_report.tex`, now `article.tex` | `4b874cea0` (full `4b874cea0012c51a6841ad9c58f6e20fa57c71da`, the arrival commit of batch 75; `provenance-SOURCES.md` and Section 10) | `d0e6008d9` | the whole report |

**Status:** presumed AI-assisted (the delivery names neither an author nor a
tool), unrefereed, not formalized. The proofs are analytic; the shipped
programs check exact integer identities and high-precision (not interval)
numerics.

## What it proves

`a_b(n)` is the coefficient of `z^n` in `F_b(z) = ∏_{j≥0,i≥1}(1 + z^(i b^j))`
(a part of size `k` comes in `1 + v_b(k)` colours, each used at most once).
For `b = 2^m` it is the partition function restricted to parts with
`v_2(k) ≡ 0 (mod m)`: `b = 2` gives ordinary partitions, `b = 4` A174065,
`b = 8` A393565.

- **Theorem 1.1 (every fixed order).** With `N = n - d`,
  `u = log_b √(N/A)`, `a_b(n) = K N^(-κ) e^(2√(AN)) {Σ_{j≤J} (AN)^(-j/2)
  R_j(D) H(u) + O(N^(-(J+1)/2))}` uniformly in `u mod 1`, where `H = e^P` is
  positive, 1-periodic and analytic, and `R_j(D)` are explicit differential
  operators of degree `2j`.
- **Proposition 2.2.** `H` is nonconstant for every integer `b > 2` (the
  first Fourier coefficient `c_1 ≠ 0`, by the zero-free line of `ζ`, no RH
  needed); `H ≡ 1` for `b = 2`; for `b = 2^m` exactly the modes `m | k`
  vanish.
- **The OEIS correction (Section 1.2, Section 4).** The plain equivalents
  recorded in A174065 and A393565 have the correct smooth constants but must
  be multiplied by `H(log_b √(n/A))`; Section 4 shows, independently of
  Theorem 1.1 (by an Abelian argument), that no constant-only equivalent of
  that shape can hold.
- **Theorem 3.1 and Corollary 3.2 (exact radial reciprocity).** For real
  `t > 0`, `log F_b(e^(-t)) = G_b(t) + log F_b(e^(-B/t))` with `B = 2π²b`, so
  the radial remainder is `e^(-B/t) + O(e^(-2B/t))`; reflection symmetry
  gives `(min H)(max H) = 1`.
- **Corollary 6.1.** The subsequential limits of `a_b(n)/(K n^(-κ)
  e^(2√(An)))` form exactly `[min H, max H]`, nondegenerate for `b > 2`; the
  OEIS constant is its geometric centre, not an equivalent. The first
  correction is explicit (6.3)–(6.4).
- **Section 7 (inverses).** Logarithmic form with periodic coefficients
  `ℓ_j(v)`; a contraction algorithm to every fixed order; the periodic
  inverse term is of order `log y` in the index; **Corollary 7.1**: the first
  `n` with `a_b(n) ≥ y` lies between two ceilings.
- **Corollary 8.1.** `a_b(n)` is eventually strictly increasing and eventually
  strictly log-concave.

## What is not claimed

- The analytic methods are classical (Flajolet–Gourdon–Dumas Mellin
  analysis; Madritsch–Wagner 2010 is "an important precedent"); the claim is
  the correction and explicit treatment of this family, "not worldwide
  priority for the underlying methods". The bounded literature and
  repository search "does not establish worldwide priority".
- Bridges–Brindle–Bringmann–Franke (2024) is said not to apply directly
  (real-pole hypotheses); this is "a scope distinction, not a claim that the
  paper's theorems are incorrect".
- The integer enclosure is asymptotic: no numerical remainder constants or
  starting thresholds, hence no effective certificate; an exact single
  ceiling is not justified.
- The exact positive-real reciprocity does not give an exponentially
  complete coefficient expansion.
- Numerical checks use 60–90 digits without interval arithmetic: "sanity
  checks, not rigorous remainder certificates"; the decimals of `c_1` are
  not the proof of nonconstancy.
- No OEIS edit or submission was made (the manuscript, Section 1.2, and
  `provenance-SOURCES.md`).
- No formal proof-assistant verification (Section 10).
- **Inversion: no novelty for the smooth skeleton or the integer step.**
  With `P` and the `ℓ_j` set to zero, `X - ν log X = Y - c_0` is
  `p0:thm:lambert-core` (`a = 1`, `b = -ν`, branch `W_{-1}`), and for
  `b = 2` the all-orders inverse is `p0:thm:lambert-centered`; for `b > 2`
  the periodic coefficients depend on `log X`, so that theorem does not apply
  as stated. The integer step of Corollary 7.1 is `p0:thm:backward-error`
  and `p0:thm:staircase` (1)–(2) (`x_* = x_J`, `η = C_{b,J} x_J^(-J/2)`),
  all in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
  A dated `[write]` note at the end of Section 7 says so.

## Relation to the repository

**Claims about OEIS text, not about ProveIt.** The missing-factor statement
concerns the OEIS revisions the manuscript retrieved (A174065 revision #34,
A393565 revision #12; formulas attributed there to Václav Kotěšovec). At
intake, untruncated searches of the research-report collection, the
transseries volumes, `Oeis/` and `docs/reports/` for A174065 and A393565
returned no file, so no repository claim is refuted and nothing was
retracted.

**The manuscript's repository search.** Section 10 and
`provenance-SOURCES.md` describe a bounded inspection of ProveIt at the pin
`4b874cea0` (four subtree inventories and a content scan of 129 files under
`generating-functions-and-asymptotics/`). The intake search above, made at
`096ee7b87`, is the authoritative one; a dated note at the end of Section 10
says so.

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status; the
manuscript used no ProveIt theorem. The generic order-theoretic steps named
in the inverse note are formalized for an arbitrary monotone function, not
for `a_b(n)`: `Fabius.staircase_ceil` and `Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`, and
`Fabius.abs_sub_right_inverse_le_div` in
`Analysis/FabiusFunction/Lean/FabiusFunction/MeanValueBracket.lean`.

**Neighbouring work.**
- `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a033552-catalan-partitions`
  (partitions into Catalan numbers): the same mechanism, Mellin poles on a
  vertical lattice giving a periodic phase of a logarithm, for a different
  product; no theorem is shared.
- `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/spectra-and-arithmetic/Digital_Spectral_Geometry_and_Log_Periodic_Saddles/`
  (a Fabius drafts-tree report, not part of this collection): credited by
  the manuscript for its digital spectral zeta function, valuation
  multiplicity, Mellin periodic functions and saddle analysis; it does not
  treat this product or the two OEIS formulas.
- `a301981-unitary-divisor-partitions` (same batch): another pure OEIS
  equivalent that misses a nonconstant factor, there driven by zeta zeros.
- (Pointers made here only; those reports are not edited. A one-line
  reciprocal pointer in `a033552-catalan-partitions` is proposed for a
  separate commit.)

## Notation

The manuscript reuses letters heavily: `c_k` (Fourier coefficients) vs the
constants `c, c_0, c_1` in the proof of Lemma 5.1 (that `c_1` is **not** the
Fourier coefficient `c_1`), `c(θ)` and `c_0` of Section 7; `D` (operator) vs
`𝒟` (distinct-part logarithm); `B` (reciprocity constant) vs `B(q,x,u)`;
`M` three ways, including the threshold `M(y)`; `u` uses the shifted
`N = n - d`, `θ_n` the unshifted `n`; `v`, `q`, `T`, `x` several ways each.
Table 1 (a `[write]` float in Section 1) fixes every such symbol. No symbol
was renamed.

## Labels

Every label carries the prefix `rlp:`. The manuscript's 63 labels in
`article.tex` were prefixed before anything cited them (49 `\ref`/`\eqref`
updated), and three section labels (`rlp:sec:constants`, `rlp:sec:oeis`,
`rlp:sec:replay`) and the notation table's `rlp:tab:notation` were added:
67 labels in `article.tex`. The two labels of the delivered
`numerical_tables.tex` (`tab:counts`, `tab:inverse`) are left untouched in
that file and become `rlp:tab:counts`, `rlp:tab:inverse` through a wrapper
around its `\input` (which also maps its `\eqref{eq:reciprocitylog}` to the
prefixed label): 69 labels in the built document, all prefixed. The writing
step also added four dated `[write]` notes (end of Section 1.2: provenance,
OEIS-facing claims, neighbouring work, the notation table; end of Section
7: the inverse note; end of Section 9.2: the shipped files; end of Section
10: the repository search), three bibliography entries (`rlp-tai`,
`rlp-a033552`, `rlp-fabius`), set the bibliography ragged-right (the long
repository paths of the new entries otherwise gave underfull lines), and
restored the diacritic in "Kotěšovec" (two places, printed "Kotesovec" in the
delivery). Because the notation table is a float numbered first, the two
delivered tables are now Tables 2 and 3 (nothing in the delivered text cites
them by number). No statement, proof or number of the manuscript was
changed.

## Files

```text
README.md                               this guide (replaces the delivery README)
article.tex                             the report (delivered as radix_partition_report.tex)
article.pdf                             compiled report, 16 pages
numerical_tables.tex                    delivered table source, \input by article.tex (generated by checks-make_tables.py)
provenance-SOURCES.md                   delivered sources and bounded-search record (names the pin)
provenance-REVIEW_AND_VALIDATION.md     delivered review and validation record
code/checks-check_exact.py              exact dynamic programs (n ≤ 10000 for b = 4, 8) and three-way identity (n ≤ 400); writes exact-checks.json beside itself
code/checks-check_radix.py              Mellin/Fourier checks; writes mellin-checks.json beside itself
code/checks-check_coefficients.py       order 0–4 coefficient tests (SymPy, mpmath); writes coefficient-checks.json beside itself
code/checks-check_inverse.py            inverse tests; reads coefficient-checks.json, writes inverse-checks.json beside itself
code/checks-check_reciprocity.py        positive-real reciprocity checks; writes reciprocity-checks.json beside itself
code/checks-make_tables.py              regenerates numerical_tables.tex from the JSON results
code/checks-verify_results.py           compares a run with the recorded JSON (tolerance 1e-40) and asserts the stated bounds
code/replay.sh                          the delivered replay driver (expects the delivery layout; see below)
code/build_pdf.sh                       the delivered PDF build (expects radix_partition_report.tex; see below)
code/verify_manifest.py                 checks the delivered SHA256SUMS (not shipped)
data/recorded-exact-checks.json         recorded output of check_exact.py
data/recorded-mellin-checks.json        recorded output of check_radix.py
data/recorded-coefficient-checks.json   recorded output of check_coefficients.py
data/recorded-inverse-checks.json       recorded output of check_inverse.py
data/recorded-reciprocity-checks.json   recorded output of check_reciprocity.py
data/provenance-OEIS_extracted_facts.txt  factual transcription of the two OEIS revisions
data/validation.json                    delivered validation summary (14 pages, 588 comparisons, delivered PDF hash)
data/requirements.txt                   mpmath==1.3.0, sympy==1.14.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Placement renamed
`radix_partition_report.tex` to `article.tex`; moved `checks/<name>` to
`code/checks-<name>`, `recorded/<name>` to `data/recorded-<name>`,
`provenance/<name>` to `provenance-<name>` (the `.txt` to `data/`),
`replay.sh`, `build_pdf.sh` and `verify_manifest.py` to `code/`, and
`requirements.txt` and `validation.json` to `data/`; `numerical_tables.tex`
stays beside the article, which `\input`s it. Not shipped: the delivered
14-page PDF `radix_partition_report.pdf` and `SHA256SUMS` (a checksum
ledger, verified 24/24 at placement). Both survive in the archive:
`git show 096ee7b87:docs/incoming/radix-partition-reproducibility.zip > <scratch>/radix-partition-reproducibility.zip`.

Delivered text that names the delivery layout or unshipped files:
`code/replay.sh` (runs `verify_manifest.py`, which needs `SHA256SUMS`; uses
`checks/`, `recorded/`, `radix_partition_report.tex` and the PDF beside it;
creates `replay-output/` in its own directory); `code/build_pdf.sh`
(compiles `radix_partition_report.tex` in its own directory, writing
`.build/` and the PDF there); `code/verify_manifest.py`;
`provenance-SOURCES.md` (refers to `OEIS_extracted_facts.txt`, now
`data/provenance-OEIS_extracted_facts.txt`); `data/validation.json` and
`provenance-REVIEW_AND_VALIDATION.md` (hashes and page count of the
delivered PDF and TeX); the article's Section 9.2 (a dated note there says
what is shipped). The README the article mentions is the delivery README,
replaced by this guide; it survives in the archive.

## Rerun the checks (on a scratch copy)

Every check script writes its JSON next to itself, so never run them in
`code/`. The recorded files carry a `recorded-` prefix, so give
`checks-verify_results.py` a reference directory with the delivered names.
Git Bash, from this directory:

```sh
D=$PWD; R=$(mktemp -d); mkdir "$R/run" "$R/ref"
for f in code/checks-check_*.py; do b=$(basename "$f"); cp "$f" "$R/run/${b#checks-}"; done
for f in data/recorded-*.json; do b=$(basename "$f"); cp "$f" "$R/ref/${b#recorded-}"; done
cd "$R"; export PYTHONUTF8=1
PY="uv run --no-project --with mpmath==1.3.0 --with sympy==1.14.0 python"
for t in exact radix coefficients inverse reciprocity; do $PY run/check_$t.py > run/$t.log; done
$PY "$D/code/checks-verify_results.py" ref run
$PY "$D/code/checks-make_tables.py" --data run --output numerical_tables.tex
diff --strip-trailing-cr numerical_tables.tex "$D/numerical_tables.tex" && echo tables identical
```

On Windows Python writes CRLF, so the delivered `replay.sh` byte comparison
(`cmp`) of the regenerated tables fails on line endings alone; the `diff`
above ignores them. Alternatively use the delivered layout: extract the
archive above and run `bash replay.sh` there (it also verifies the manifest
and rebuilds the PDF). At intake (2 October 2026, Python 3.13.5, mpmath
1.3.0, SymPy 1.14.0) the computation steps took 136 s; `verify_results.py`
printed "PASS: 588 recorded values agree; exact, count, inverse and
reciprocity checks pass", and the regenerated tables equalled the shipped
file apart from CRLF line endings. The PDF rebuild was not run. At this
write the commands above were run on a scratch copy: the same PASS line,
"tables identical", 2 min 37 s in all.

## Build the PDF

pdfLaTeX with lmodern, geometry, amsmath, amssymb, amsthm, mathtools,
booktabs, array, graphicx, microtype, hyperref and enumitem; `article.tex`
`\input`s `numerical_tables.tex`. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 16 pages, no
errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull
boxes. (The delivered source builds to 14 pages, also without warnings.)
`code/build_pdf.sh` is kept as delivered; to use it, copy it to a scratch
directory together with `article.tex` renamed to
`radix_partition_report.tex` and `numerical_tables.tex`.

## Provenance

- OEIS A174065 (revision #34, 24 February 2026) and A393565 (revision #12,
  7 March 2026), retrieved 2 October 2026; Flajolet–Gourdon–Dumas, Theoret.
  Comput. Sci. 144 (1995); Madritsch–Wagner, Monatsh. Math. 161 (2010);
  Bridges–Brindle–Bringmann–Franke, Math. Ann. 390 (2024); DLMF; see the
  article's bibliography and `provenance-SOURCES.md`.
- Repository input: ProveIt at `4b874cea0` (bounded inspection; the Fabius
  digital-spectral report credited for methodological overlap).
- Batch 77 of `docs/incoming`, manuscript 60 (cluster P4); arrival
  `096ee7b87`, placement `d0e6008d9`, written in the batch-77 write phase
  (2 October 2026). Single source, so the write made no merge choices.
