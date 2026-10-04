# Gamma Constants and Scaling Limits for Rounding Extinction

**Cloitre's power-rounding conjecture (OEIS A082528) for every real `m > 0`,
smooth-weight universality, and the limits of regular variation**

A research report dated 3 October 2026, built from one manuscript. Its author
line, and its PDF author field, read "Research report prepared for Vladimir
Reshetnikov with OpenAI": the package names OpenAI as the tool that prepared
it and names no human author.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 85, manuscript 05 | `Rounding_Extinction_OEIS.zip` (wrapper directory `Rounding_Extinction/`, 1,632,826 bytes), arrival commit `317c1ce2e`; main file `article.tex` with its `\input` files `body.tex`, `extensions.tex`, `computation.tex`, `questions.tex`, `bibliography.tex` | `ce37e13f4` (`ce37e13f4aa16819c87c3ccc611362d15758f2ac`, quoted in Section 2.3 and in the bibliography entry for ProveIt) | `713149ded` | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. The package says its
proofs were reviewed twice internally, which "are not a substitute for peer
review or formal verification". Exact integer computations check the finite
definitions on recorded ranges; Gamma values, plots and forward-path error
sizes are numerical diagnostics, not interval bounds.

## What it proves

Fix a real `m > 0`. From an integer `n ≥ 0` set `x_1 = n` and
`x_k = k^m ⌊x_{k−1}/k^m⌋` for `k ≥ 2`; `τ_m(n)` is the first `k` with
`x_k = 0` (`τ_m(0) = 1`). For `m = 1, 2, 3` these are OEIS A073047, A082527 and
A082528. `T_m(K)` is the least initial value that survives through stage `K`.

- **Theorem 1.1 (power-rounding extinction).**
  `τ_m(n) ~ (c_m n)^(1/(m+1))` and `T_m(K) ~ L_m K^(m+1)`, with
  `c_m = m Γ(m/(m+1))^(m+1)` and `L_m = 1/c_m`. This proves the real-`m`
  conjecture recorded by Benoit Cloitre in A082528 and identifies the
  numerically conjectured constants `c_2 = 2Γ(2/3)³ = 4.965917162430455473…`
  (A082527) and `c_3 = 3Γ(3/4)⁴ = 6.764822981008760234…` (A082528).
- **Theorem 1.2 (full extinction trajectory).** With `J = τ_m(n)`, the
  rescaled path `x_{⌊Jt⌋}/n` converges uniformly on `[0,1]` to
  `F_m(t) = c_m t^m y_m(t)`, where `y_m` is the explicit piecewise-linear
  profile with slopes `−1, −2, −3, …` between the crossing times
  `t_j = ∏_{r ≤ j}(1 − 1/((m+1)r)) = Γ(j+a)/(Γ(a)Γ(j+1))`, `a = m/(m+1)`.
- **Theorem 1.3 (smooth-weight universality).** For weights `w_1 = 1`,
  `w_k > 0` with `k(w_k/w_{k−1} − 1) → m`: `T_w(K) ~ L_m K w_K`,
  `L_m τ_w(n) w_{τ_w(n)} ~ n`, and the same limiting trajectory `F_m`.
- Section 3: the backward quotient array (Definition 3.1), survival duality
  (Lemma 3.2), the exact inverse `τ_m(n) = 1 + max{K : T_m(K) ≤ n}`
  (Corollary 3.3), and the two rounding-error estimates; Section 4:
  compactness (Lemma 4.1), passage through the ceiling discontinuities
  (Lemma 4.2), the explicit profile and its uniqueness (Proposition 4.3);
  Section 5: the beta-integral asymptotic of `t_j` and the small-time
  weighted limit (Lemma 5.1).
- **Proposition 6.1:** rational product certificates bracketing `c_m`, with
  upper/lower ratio exactly `1 + m/((m+1)j)`; **Corollary 6.2:** the limiting
  distribution of rounding losses (density `c_m t^m [C(my_m/t) − my_m/t]`);
  **Proposition 6.3:** `c_m` strictly increasing, `c_m → 1` as `m ↓ 0`,
  `log c_m = log m + γ + Σ_{r≥2} ζ(r)/(r(m+1)^(r−1))`, and
  `c_m = e^γ m (1 + π²/(12(m+1)) + O(m^(−2)))`.
- Lemma 7.1 (regular variation from the ratio hypothesis), Corollary 7.2
  (logarithmic modifiers `w_k = A k^m (log k)^b`), Corollary 7.3 (regular
  variation of the stopping index).
- **Proposition 8.1 (repeating each modulus):** block weights
  `w_k = ⌈k/r⌉^m` are regularly varying of index `m` but give
  `T_w(K)/(K w_K) → L_m/r`, so regular variation alone does not determine the
  constant.
- Section 9: exact integer and rational-exponent algorithms, the recorded
  checks, Tables 1–2 and Figures 1–3; Section 10: nine research questions;
  Appendix A: proof dependencies and source audit; Appendix B: a **draft** of
  OEIS update text (see below).

## What is not claimed

- **The case `m = 1` is classical and credited, not claimed:** `c_1 = π`,
  `T_1(K) ~ K²/π` (A002491, the Tchoukaillon or Mancala sieve) and
  `τ_1(n) ~ √(πn)` are due to Erdős and Jabotinsky (1958), who also proved
  `T_1(K) = K²/π + O(K^(4/3))`; the increment-regime method is theirs (Brown's
  and Lehéricy's related work is cited). The new claims are the case `m ≠ 1`,
  the square and cube constants, and the extensions.
- No bounded error: `τ_1(n) = √(πn) + O(1)`, recorded as presumptive in
  A073047, is **not** proved; no quantitative rate of convergence is claimed
  for any `m` (the compactness argument gives none). The Broline–Loeb
  sharpening is not used, because of Knuth's 2021 criticism recorded in
  A002491.
- All limits are for fixed `m`; nothing is uniform in a moving `m = m(n)`.
- Theorem 1.3 needs the local ratio hypothesis; Proposition 8.1 shows that
  regular variation alone is not enough.
- The exact-arithmetic program handles positive rational `m` only; the
  real-parameter theorem is broader than the code. The exact checks cover only
  the recorded finite ranges; the rational certificates of record are the exact
  fractions in `data/constant_certificates.json`.
- Priority rests on a targeted, not exhaustive, search ("The historical search
  was targeted, not exhaustive"). The intake confirmed the absence of any
  repository treatment, but did not search the external literature for an
  earlier general-`m` theorem.
- **Appendix B is a draft OEIS update, marked "not posted" in the article,
  and it stays so.** Nothing was submitted to OEIS by the package's author
  (`VERIFICATION_NOTES.txt`: "No OEIS updates or repository modifications have
  been submitted") or by the intake; a dated `[write]` note at Appendix B says
  so. Any submission is a human editor's decision after review.

## Checks made at intake

On 3 October 2026 the intake read the OEIS entries on `oeis.org` and
confirmed the manuscript's statements about them: A082528 records Cloitre's
conjecture for real `m > 0` with the constant 6.76…; A082527 records 4.96…,
and its `n = 10` example prints the intermediate value 2 where
`4⌊10/4⌋ = 8` is meant (the stopping index 3 is right), the slip Section 2.1
reports; and A002491 carries Knuth's 2021 comment on the accumulating error
terms of Broline and Loeb. An independent integer implementation reproduced
`T_1(1..10) = 1, 2, 4, 6, 10, 12, 18, 22, 30, 34` (A002491), all 79/105/105
fixture terms of A073047/A082527/A082528, and
`c_m T_m(3000)/3000^(m+1) = 0.999998, 1.00048, 1.00052` for `m = 1, 2, 3`.
The delivered program passed on scratch copies (see "Rerun the checks").

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or Rocq,
no formal development in ProveIt treats the subject, and the report's place in
the collection confers no formal status. The manuscript uses no repository
theorem.

**Neighbouring reports.** None. A search of the whole tracked tree at
placement (all reports; the `Oeis`, number-theory and combinatorics projects;
the Lean and Rocq developments) found no treatment of A073047, A082527,
A082528, A002491, Tchoukaillon, Mancala, Jabotinsky or Broline, as the
manuscript's own bounded search at the pin had found. Its batch-85 sibling on
OEIS A306631
(`Analysis/Transseries/docs/series-and-transseries/Partition_Function_Exact_Inversion_OEIS_A306631/`)
also speaks of "rounding", but of an inverse of the partition function:
unrelated mathematics, no shared notation.

**Stale claims.** The manuscript's repository statements (Section 2.3:
"Exact searches … returned no matching treatment", the 59-entry
`oeis-sequence-asymptotics` and 58-entry `series-and-transseries` directories)
are true at the pin and stay as dated provenance; the only treatment the
repository now has is this report.

## Notation

The manuscript reuses some letters with local meanings (`y_K` vs `y_m`;
`q_k^(K)`, `Q_k`, and `q` as the denominator of `m = p/q`; `a = m/(m+1)` vs
the increments `a_k`; `b_k` vs `b`; `t` vs the crossing times `t_j`; the
positive ceiling `C(u)` vs the constant `c_m`; `r` as block length and as an
index; `δ`, `δ_u`, `δ_m`; `z`, `ρ_m`, `J`). A table in the first `[write]`
note (end of Section 2) fixes each one, with the tempting false readings, for
example that the curve `y_3` of Figure 2 is the `m = 3` limit and not the
array at `K = 3`. No symbol was renamed.

## Labels

Every label carries the prefix `rex:`. The manuscript's 99 labels (50 in
`body.tex`, 34 in `extensions.tex`, 9 in `computation.tex`, 6 in
`questions.tex`) were prefixed before anything cited them, and every
reference to them was updated (98 `\cref` items, 5 `\ref`, 4 `\eqref`); no
label was added, so the report has 99 labels. `article.tex` and
`bibliography.tex` define none.

The writing step also:

- added three dated `[write]` notes: end of Section 2 (provenance, pin and
  repository claims, the `m = 1` credit, the intake's OEIS checks, the
  notation table), end of Section 9.6 (shipped layout, intake replay, the OEIS
  licence), and Appendix B (the draft is not posted; nothing submitted);
- added to the preamble the `writenote` environment and six
  `\crefalias` hooks. MiKTeX's current LaTeX kernel makes `cleveref` print
  every environment sharing the theorem counter as "theorem" (a plain rebuild
  printed "theorem 3.2" for Lemma 3.2); the delivered PDF, built with
  pdfTeX 1.40.25, did not, and the hooks restore its names;
- set the two `--` of the command line `python reproduce.py --exact-only --out
  replay_exact` in Section 9.6 as `-{}-`: the delivered PDF printed them as en
  dashes (a typewriter ligature), which a reader could not paste.

No statement, proof or number of the manuscript was changed;
`extensions.tex` differs from the delivery only by its label prefixes, and
`bibliography.tex` not at all.

## Files

```text
README.md                         this guide (replaces the delivery's README.txt)
article.tex                       the report: preamble, title, abstract (delivered main file)
body.tex                          Sections 1-5, \input by article.tex (labels prefixed; first [write] note)
extensions.tex                    Sections 6-8, \input by body.tex (labels prefixed)
computation.tex                   Section 9, \input by body.tex (labels prefixed; second [write] note)
questions.tex                     Section 10 and Appendices A-B, \input by body.tex (labels prefixed; third [write] note)
bibliography.tex                  the eleven references, \input by body.tex (as delivered)
article.pdf                       compiled report, 27 pages
VERIFICATION_NOTES.txt            the package's review and build notes (as delivered; see below)
code/reproduce.py                 all exact checks, tables and figures (delivered at the package root)
data/requirements.txt             mpmath==1.3.0, matplotlib==3.10.8 (delivered at the package root)
data/verification.json            recorded run: scope and outcome of every check (delivered at the package root)
data/oeis_prefixes.json           OEIS fixture terms, A073047/A082527/A082528 (third-party, CC BY-SA 4.0; see below)
data/gamma_constants.json         c_m for m = 1/2, 1, 2, 3, 5 at 60 digits (numerical)
data/threshold_table.csv          exact T_m(K), m = 1/2, 1, 2, 3, 5, K = 10 ... 100000 (25 rows; CRLF)
data/threshold_table.tex          Table 1 (K <= 10000), \input by computation.tex
data/threshold_convergence.csv    exact thresholds behind Figure 1 (1842 rows; CRLF)
data/constant_certificates.json   exact rational products and endpoints (the certificates of record)
data/constant_intervals.csv       numerical display of the intervals (CRLF)
data/constant_intervals.tex       Table 2 (j = 1000, outward rounding), \input by computation.tex
data/backward_profiles.csv        exact backward q_k, m = 3, K = 20, 100, 1000 (CRLF)
data/limiting_profile.csv         breakpoints of y_3 on [0.12, 1] (CRLF)
data/forward_profiles.csv         exact forward x_k, m = 3, n = 10^3, 10^6, 10^9 (CRLF)
data/limiting_forward_profile.csv F_3 on a grid of [0, 1] (numerical; CRLF)
figures/normalized_thresholds.png Figure 1
figures/backward_profiles.png     Figure 2
figures/forward_paths.png         Figure 3
```

Every file except `README.md`, `article.tex`, `body.tex`, `extensions.tex`,
`computation.tex`, `questions.tex` and `article.pdf` is byte-identical to the
delivery. Placement moved `reproduce.py` to `code/` and `requirements.txt`
and `verification.json` to `data/`, and staged the delivery's `README.txt` as
`README.md`, which this guide replaces. Not shipped: the delivered 25-page
`article.pdf` (941,186 bytes). It and the delivery README survive in the
archive:
`git show 317c1ce2e:docs/incoming/Rounding_Extinction_OEIS.zip > <scratch>/Rounding_Extinction_OEIS.zip`.
The package has no checksum manifest, and nothing was excluded as heavy.

**Third-party data.** `data/oeis_prefixes.json` holds initial terms of
A073047, A082527 and A082528 copied from The On-Line Encyclopedia of Integer
Sequences (https://oeis.org; each record gives its source URL and the
retrieval date 2026-10-04, the package's UTC date). OEIS content is
published by The OEIS Foundation Inc. under the Creative Commons
Attribution-ShareAlike 4.0 licence (CC BY-SA 4.0); this file is third-party
data under that licence, **not** MIT-0 like the rest of the repository. The
sequence definitions and the conjectures are due to Benoit Cloitre, as
attributed in the entries. The program reads the file and never contacts OEIS.

Delivered text that names the delivery layout or a file not shipped:
`code/reproduce.py` (sets `ROOT` to its own directory, reads
`ROOT/data/oeis_prefixes.json`, and defaults `--out` to `ROOT`, writing
`verification.json` at the output root and the rest under `data/` and
`figures/`); Section 9.6 of the article ("From the archive's root directory
… `python reproduce.py`", "this PDF", "The README"; a dated note there says
so); `data/verification.json` (figure paths relative to the package root);
and `VERIFICATION_NOTES.txt` ("Final PDF: 25 A4 pages, three figures, 11
bibliography entries" describes the delivered PDF; the shipped rebuild has 27
pages because of the notes).

**Byte-level notes.** The seven CSV files are CRLF throughout (Python's `csv`
module); seven lines
`docs/reports/…/a082528-rounding-extinction/data/<name>.csv -text` in
`SetTheory/Cardinals/.gitattributes` keep their bytes. The
program writes JSON and `.tex` files in text mode, so on Windows a rerun emits
them with CRLF where the shipped ones are LF; compare after stripping `\r`.

## Rerun the checks (on a scratch copy)

Never run `code/reproduce.py` in place: from `code/` it cannot find
`data/oeis_prefixes.json`, and without `--out` it overwrites the files beside
it. Rebuild the delivered layout on a copy and write into a separate output
directory (Git Bash, from this directory):

```sh
T=$(mktemp -d); X="$T/Rounding_Extinction"
mkdir -p "$X/data" "$X/figures"
cp code/reproduce.py data/requirements.txt data/verification.json "$X/"
for f in data/*; do case ${f#data/} in
  requirements.txt|verification.json) ;; *) cp "$f" "$X/data/";; esac; done
cp figures/* "$X/figures/"
cd "$X"
py reproduce.py --exact-only --out "$T/replay_exact"     # standard library only
py reproduce.py --threshold 1000 --m 2/3                # T_{2/3}(1000) = 39828
py reproduce.py --stop 12345 --m 3/2                    # tau_{3/2}(12345) = 75
uv run --no-project --with mpmath==1.3.0 --with matplotlib==3.10.8 \
  python reproduce.py --out "$T/replay_full"            # full replay, K up to 100000
for f in "$T"/replay_full/data/*; do
  tr -d '\r' < "$f" | cmp -s - <(tr -d '\r' < "data/$(basename "$f")") \
    && echo "same  $(basename "$f")" || echo "DIFF  $(basename "$f")"; done
```

(On a POSIX host use `python3` for `py`.) At intake (3 October 2026, Windows)
the exact-only replay printed `Exact verification: PASS` in about 1 s and
reproduced `data/constant_certificates.json` up to CRLF; the two queries
returned 39828 and 75. The full replay (Python 3.12.13, mpmath 1.3.0,
matplotlib 3.10.8) passed in 92.5 s on a loaded machine (the package recorded
6.2 s): all eleven data files matched the shipped ones (seven CSV files byte
for byte, the two JSON and two `.tex` files after CRLF stripping),
`verification.json` differed only in `elapsed_seconds` and `python_version`,
and the three PNG figures differed only in rendering. The recorded run checks
90,009 integer-root cases, 27,555 rational-root cases, the forward/backward
agreement for `m = 1, 2, 3` and `n ≤ 2000` and for `m = 1/2, 2/3, 3/2, 5/3`
and `n ≤ 200`, the three OEIS prefixes, the block identities for `r = 3`, and
the twelve certificate intervals (`m = 1, 2, 3, 5`; `j = 10, 100, 1000`).

## Build the PDF

pdfLaTeX (amsmath, amssymb, amsthm, mathtools, booktabs, longtable, graphicx,
xcolor, enumitem, fancyhdr, hyperref, xurl, cleveref, lmodern, microtype). The
article inputs `data/threshold_table.tex`, `data/constant_intervals.tex` and
`figures/*.png` relative to this directory. Build in a scratch copy:

```sh
B=$(mktemp -d); cp -r *.tex data figures "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX: 27 pages; no errors or
warnings, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, no overfull or underfull boxes. The delivered
source, built the same way, gives 25 pages, also without warnings, but with
the "theorem" cross-reference names described under Labels.

## Provenance

- Sources cited by the manuscript: OEIS A073047, A082527, A082528, A002491;
  Erdős–Jabotinsky, Indag. Math. 20 (1958) 115–128; Broline–Loeb,
  arXiv:math/9502225; Brown, "Rounding up to π" (MathPages); Lehéricy, Math.
  Stack Exchange answer 4705436 (2023); Li, arXiv:2608.17517 (2026); DLMF
  Chapter 5.
- Repository input: the pin `ce37e13f4` (3 October 2026), used for a bounded
  non-duplication search; no repository theorem is used.
- Batch 85 of `docs/incoming`, manuscript 05; arrival `317c1ce2e`, placement
  `713149ded` (batch 85A), written in the batch-85 write phase
  (3 October 2026). Single source, so the write made no merge choices.
