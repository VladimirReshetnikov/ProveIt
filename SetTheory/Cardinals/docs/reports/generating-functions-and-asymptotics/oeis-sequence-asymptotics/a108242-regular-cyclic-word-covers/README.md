# Regular Cyclic Word Covers

**Full asymptotic expansions and critical degree crossover (OEIS A108242,
A110105, A110104, A110106)**

A research report dated 2 October 2026, built from one manuscript. Its
author line reads only "Research article and reproducibility companion";
the delivery names no author and no tool.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 61 | `regular-cyclic-word-covers-reproducibility.zip` (wrapper directory `regular-cyclic-word-covers/`), arrival commit `096ee7b87`; main file `article/regular-cyclic-word-covers.tex`, now `article.tex` | none: no ProveIt commit is named and no repository path is continued | `d0e6008d9` | the whole report |

**Status:** presumed AI-assisted (the delivery names neither an author nor
a tool), unrefereed, not formalized. Exact finite, symbolic and
high-precision (not interval-certified) checks corroborate the formulas;
the uniform remainders rest on the written proofs.

## What it proves

`A^s_{n;r,ℓ}` counts sets (`s = -1`) or multisets (`s = +1`) of rotation
classes of words of length `ℓ ≥ 3` on the alphabet `[n]` in which every
letter occurs exactly `r` times in total; letters may repeat inside a word,
and a word is not identified with its reversal. The exact carrier is
`B_{n;r,ℓ} = (rn)! / (ℓ^{rn/ℓ} (rn/ℓ)! (r!)^n)`.

- **Proposition 2.1 (exact slot-partition identity)** for `A/B` from the
  cycle index of `C_ℓ`.
- **Theorem 3.1 (fixed degree).** For fixed `r, ℓ, s` and every `K`,
  `A/B = Σ_{k≤K} c_k n^{-k} + O(n^{-K-1})`, `c_0 = 1`, all `c_k` rational
  with a finite algorithm and an absolute majorant (also for `s = -1`).
- **Section 4 (the OEIS sequences).** `A108242(n) = A^+_{n;3,3}`,
  `A110105(n) = A^-_{n;3,3}`, `A110106(m) = A^+_{3m;2,3}`,
  `A110104(m) = A^-_{3m;2,3}` (the manuscript notes that some OEIS titles
  are inconsistent with these parameters and follows the examples and
  Mishna's source); exact triple sums; corrections through `n^{-5}`
  (`A^+/B_n = 1 + 8/(9n) + 104/(81n²) + …`, `A^-/B_n = 1 - 16/(243n³) - …`);
  the posted carriers `F_n`, `H_n` versus `B_n`, with the corrections each
  induces; degree two.
- **Theorem 5.1 (uniform cubic bridge).** Uniformly for `1 ≤ r ≤ C√n`,
  `A^s_{n;r,3}/B_{n;r,3} = exp(τ + sμ)(1 + O_C(1/n))`.
- **Theorem 6.1 (critical degree, every length).** At `r = λ n^{(ℓ-2)/2}`,
  uniformly for `λ` in a compact positive interval, an expansion to every
  fixed order in `h = n^{-1/2}` with multiplier
  `exp(sλ²/(2ℓ) + 1_{2|ℓ} λ/ℓ)` (the even-length term is a half-turn
  symmetry effect); Lemmas 6.2–6.4 give the weighted-tail, collision-forest
  and Taylor estimates.
- **Section 7.** A finite Newton-difference algorithm for the coefficients;
  explicit cubic coefficients through `h³`; Corollary 7.1 (even `ℓ`: only
  integer powers of `1/n`); the quartic case; Corollary 7.2 (the first
  surviving correction for odd prime and composite `ℓ ≥ 6`).
- **Theorem 8.1 (fixed-degree inverse).** A `W_0` (factorial-phase) smooth
  inverse with corrections and a two-ceiling enclosure of the threshold on
  the admissible lattice `q_0 Z`, with an unspecified constant `C_K`.

## What is not claimed

Kept from the manuscript and its package:

- The leading equivalents of the four OEIS sequences were posted by
  Kotěšovec (2016, 2023; the manuscript spells "Kotesovec"); the sequences
  are Mishna's (the cyclic-cover discussion is in version 1 of her 2005
  preprint). No priority is claimed for those constants.
- The literature comparison (de Panafieu; Blinovsky–Greenhill;
  Kamčev–Liebenau–Wormald; Greenhill–McKay; Kuperberg–Lovett–Peled) is "an
  applicability conclusion, not a proof of priority", targeted chiefly at
  cyclic triples; a broader decorated-configuration or species theorem "may
  subsume parts of this argument". No external submission, publication or
  OEIS edit is implied.
- All expansions are Poincaré expansions: no convergence of the infinite
  series, no uniform critical expansion down to `λ = 0`, no scalar inverse
  for an unspecified varying-degree path, no certified finite-input
  threshold (`C_K` is not explicit), no growth of the coefficients in `k`.
- Numerical diagnostics are 80-digit floating values, not interval bounds;
  the finite sample "cannot prove boundedness".
- **The inversion is an instance of repository results, with no novelty
  claimed for the method.** Its core `a x log x + b_0 x = Y` is
  `p0:prop:factorial-core` (`κ = a = r(1-1/ℓ)`, `d = b_0`), equivalently
  `t2:eq:unbalanced-core`; its corrections are `p0:thm:core-reversion`
  (equivalently `t2:prop:scaled`); the enclosure is the separation
  condition, part (2) of `p0:thm:staircase`, on the rescaled index
  `n/q_0`; part (1) (exact rounding) does not apply. The volumes are
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`
  and
  `Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/Combinatorial_Transseries_Inverses.tex`.
  (The linear–logarithmic `p0:thm:lambert-core` is *not* the relevant core
  here: the phase is factorial.) The write step rechecked the displayed
  third-order inverse by direct series expansion (SymPy, residual zero
  through `x_0^{-3}`) and the table `d_1, d_2, d_3` from the Section 4
  expansions. A dated `[write]` note at the end of Section 8 says so.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status; the
manuscript used no ProveIt theorem. The generic staircase arithmetic named
in the Section 8 note is formalized as `Fabius.staircase_ceil` and
`Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
those lemmas concern an arbitrary monotone function.

**Neighbouring reports.** None shares a result; the intake's untruncated
searches found none of the four OEIS numbers or the objects elsewhere in the
collection, the transseries volumes, `Oeis/` or `docs/reports/`.
`oeis-sequence-asymptotics/a330266-balanced-smirnov-poisson` lists the open
question "Cyclic words and Hamiltonian cycles" (Smirnov words with the last
letter also distinct from the first). This report does **not** answer it:
there the object is one word with no equal cyclically adjacent letters;
here it is a set or multiset of rotation classes in which letters may
repeat. A note in Section 1 says so; the a330266 report is not edited.

## Notation

Letters with several meanings (`E_3` both a coefficient polynomial and a
numerical remainder; `B_{n;r,ℓ}`, `B_n`, `D_m`, `B_h`; the posted carriers
`F_n`, `H_n` versus `H`, `F`, `F_s(e)`; `b, c, d` as mode counts versus
`b_0` and the logarithmic coefficients `d_k`; `a`, `D`, `Q`, `W`/`W_0`,
`w`, `v`, `u`, `C`, `N`, `ρ`, `Λ`, `g`; and the OEIS index `m` versus the
alphabet size `n = 3m`) are fixed by a table in the Section 1 `[write]`
note, with the tempting false readings. No symbol was renamed.

## Labels

Every label carries the prefix `rcw:`. The manuscript's 58 labels were
prefixed before anything cited them (53 `\ref`/`\eqref` targets updated),
and three section labels `rcw:sec:scope`, `rcw:sec:model`,
`rcw:sec:further` were added: 61 labels in all. The writing step also added
three dated `[write]` notes (Section 1: provenance, the a330266 distinction,
notation table; Section 8: the instance note; Section 9: the files in the
collection), two bibliography entries (`rcw-tai`, `rcw-cti`), and set the
bibliography ragged-right. No statement, proof, number or table of the
manuscript was changed.

## Files

```text
README.md                                 this guide (replaces the delivery README)
REPRODUCIBILITY.md                        delivered run record (as delivered)
SOURCES.md                                delivered source attribution (delivered as data/SOURCES.md)
article.tex                               the report (delivered as article/regular-cyclic-word-covers.tex)
article.pdf                               compiled report, 19 pages
code/reproduce.sh                         the delivered replay (delivered layout only; see below)
code/build_pdf.sh                         the delivered PDF build (expects article/regular-cyclic-word-covers.tex)
code/verify_manifest.py                   checks MANIFEST.sha256 (not shipped)
code/fixed/cyclic_covers.py               fixed-degree triple sums, 54 OEIS terms, order-8 coefficients (standard library)
code/models/check_models.py               30 literal-necklace vs logarithmic-product comparisons
code/critical/check_symbolic.py           independent cubic symbolic coefficients through h^3
code/critical/check_exact.py              exact counts and critical-window diagnostics; compiles exact_counts.cpp
code/critical/exact_counts.cpp            C++17 exact counter (GMP: -lgmpxx -lgmp)
code/general/check_quartic.py             quartic symbolic and finite-object diagnostic
code/general_coefficients.py              finite general-length coefficient algorithm (standard library)
code/check_additional_critical_grades.py  16 extra length-5/6/8/9 regressions, 34 partition counts
code/check_degree_two_and_inverse.py      degree-two normalization and inverse formal checks
data/fixed-A108242.seq                    OEIS term excerpt (delivered as code/fixed/A108242.seq), 18 terms
data/fixed-A110105.seq                    OEIS term excerpt (code/fixed/A110105.seq), 18 terms
data/fixed-A110104.seq                    OEIS term excerpt (code/fixed/A110104.seq), 9 terms
data/fixed-A110106.seq                    OEIS term excerpt (code/fixed/A110106.seq), 9 terms
data/expected-fixed-checks.json           frozen expected coefficients (data/ in the delivery)
data/fixed-results.json                   release output of cyclic_covers.py (results/)
data/model-checks.json                    release output of check_models.py (results/)
data/symbolic-results.json                release output of check_symbolic.py (results/)
data/exact-results.json                   release output of check_exact.py --extended (results/)
data/critical-extended-exact-count.json   saved exact (n,r) = (48,7) counts (code/critical/extended-exact-count.json)
data/quartic-results.json                 release output of check_quartic.py (results/)
data/general-algorithm-results.json       release output of general_coefficients.py (results/)
data/additional-critical-grades.json      release output of check_additional_critical_grades.py (results/)
data/degree-two-inverse-results.json      release output of check_degree_two_and_inverse.py (results/)
data/release-validation.json              delivered release record (results/)
data/requirements.txt                     sympy==1.14.0, mpmath==1.3.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Not shipped, all recoverable from the
archive (`git show 096ee7b87:docs/incoming/regular-cyclic-word-covers-reproducibility.zip > <scratch>/rcw.zip`):

- the delivered 18-page PDF `article/regular-cyclic-word-covers.pdf`;
- `MANIFEST.sha256` (a checksum ledger, verified 38/38 at placement);
- five byte-identical in-archive copies of release outputs, which the
  scripts rewrite beside themselves on every replay:
  `code/critical/exact-results.json` (= `data/exact-results.json`),
  `code/critical/symbolic-results.json` (= `data/symbolic-results.json`),
  `code/general/quartic-results.json` (= `data/quartic-results.json`),
  `code/models/model-checks.json` (= `data/model-checks.json`) and
  `code/fixed/cyclic-checks.json` (= `data/fixed-results.json` =
  `data/expected-fixed-checks.json`; the latter two are both shipped, one
  as the frozen comparison input of `reproduce.sh`, one as the release
  output).

No delivered file was excluded for size (the largest is
`data/exact-results.json`, 24.7 KB).

Delivered text that names the delivery layout or unshipped files:
`code/reproduce.sh` (changes to its own directory and calls
`code/...` and `data/expected-fixed-checks.json` relative to it, so it
cannot run from `code/`); `code/build_pdf.sh`
(`article/regular-cyclic-word-covers.tex`); `code/verify_manifest.py`
(`MANIFEST.sha256` beside it); the scripts themselves (each `.seq` file,
`cyclic-checks.json` and `extended-exact-count.json` are read from beside
the script under their delivered names, and results are written beside the
scripts and into a `results/` directory next to `code/`); `SOURCES.md`
("The four .seq files in code/fixed"); `REPRODUCIBILITY.md`
(`results/exact-results.json`, the fresh-extraction and manifest checks,
"18 pages"); `data/model-checks.json` (records SHA-256 hashes of
`cyclic_covers.py` and `cyclic-checks.json`); and the article's Section 9
(the checksum manifest and "the README"; a dated note there gives the
collection layout).

## Rerun the checks

Never run the scripts from this directory: they write into `code/` and
into a new `results/` directory here, and they look for their inputs under
the delivered names. Use the delivered layout. The scripts call `python3`;
on Windows put a shim first on `PATH` (Git Bash):

```sh
git show 096ee7b87:docs/incoming/regular-cyclic-word-covers-reproducibility.zip > "$TMP/rcw.zip"
cd "$TMP" && unzip -q rcw.zip && cd regular-cyclic-word-covers
uv venv "$TMP/v" && uv pip install -p "$TMP/v" sympy==1.14.0 mpmath==1.3.0
mkdir -p "$TMP/shim" && printf '#!/bin/sh\nexec "%s" "$@"\n' "$TMP/v/Scripts/python.exe" > "$TMP/shim/python3"
export PATH="$TMP/shim:$PATH" PYTHONUTF8=1
bash reproduce.sh                # needs g++ with GMP for code/critical/check_exact.py
```

Without a GMP toolchain, run the other steps of `reproduce.sh` one by one
(`python3 code/fixed/cyclic_covers.py`, `code/models/check_models.py`,
`code/critical/check_symbolic.py`, `code/general/check_quartic.py`,
`code/general_coefficients.py`, `code/check_additional_critical_grades.py`,
`code/check_degree_two_and_inverse.py`) and compare their outputs with the
release outputs in `results/` (JSON by value; on Windows the regenerated
files have CRLF line endings, and `model-checks.json` then records a
different hash of the regenerated `cyclic-checks.json`).
`bash reproduce.sh --extended` recomputes the `(48,7)` case: 6,727,282
memoized states and several GB of memory (recorded 71.7 s and 75.2 s on the
author's machine); do not run it on a memory-constrained machine.

At intake (2 October 2026, pinned SymPy 1.14.0 and mpmath 1.3.0, on a copy
of the delivered layout) the seven Python steps passed in 33 s in all, with
every output equal to the release output up to line endings except that
recorded hash; `check_exact.py` could not run, because this machine has no
GMP development toolchain, so neither the smaller exact counts nor the
`(48,7)` case was recomputed.

## Build the PDF

pdfLaTeX with geometry, lmodern, microtype, amsmath, amssymb, amsthm,
mathtools, booktabs, array, longtable, xcolor (dvipsnames), hyperref and
enumitem. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 19 pages,
no errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull
boxes. (The delivered source builds to 18 pages with the same clean log.)
`code/build_pdf.sh` is kept as delivered; to use it, recreate the
delivered layout as above and run it there.

## Provenance

- Mishna, arXiv:math/0507249v1 (2005; J. Integer Seq. 10 (2007)); OEIS
  A108242, A110105, A110104, A110106 (accessed 2 October 2026); de
  Panafieu, arXiv:2408.12459v2; Blinovsky–Greenhill, European J. Combin. 51
  (2016); Kamčev–Liebenau–Wormald, Adv. Comb. 2022:1; Greenhill–McKay, Adv.
  Appl. Math. 41 (2008); Kuperberg–Lovett–Peled, GAFA 27 (2017).
- Repository input: none recorded; no pin.
- Batch 77 of `docs/incoming`, manuscript 61 (cluster P4); arrival
  `096ee7b87`, placement `d0e6008d9`, written in the batch-77 write phase
  (2 October 2026). Single source, so the write made no merge choices.
