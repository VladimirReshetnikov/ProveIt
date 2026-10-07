# Decorated Logarithmic Eta Products (OEIS A330499 and A330498)

**Uniform oscillatory asymptotics and threshold inverses for
`Σ_k log(1 + L(z)^k)`; the harmonic Lambert decoration `Σ_k k⁻¹ log(1 + L(z)^k)`
and the `log 2` constant of A330498**

A merged research report in two Parts, built from two manuscripts of one
external research session (the session bundle of Reports 1–243, arrival commit
`60f54ea06`), placed by `8622ca7e5` (batch 110, cluster 110-ETA) and written on
7 October 2026. Neither manuscript names an author, a tool or an addressee;
both PDF author fields read "Research report".

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Decorated logarithmic eta products and OEIS A330499: Uniform oscillatory asymptotics and threshold inverses* (title block "Report185", 3 October 2026); the base | 185 | `Decorated_Eta_Oscillatory_Asymptotics_and_Inverses_Source.zip` (687,806 bytes, 38 files; `Report185.tex`, 1,376 lines, 21 pp.) | none | `8622ca7e5` | Part I, Sections 1–12 |
| *Harmonic Lambert decoration and OEIS A330498: All fixed order oscillations and threshold inverses* (title block "Report211", 4 October 2026; the "repro-v1" edition) | 211 | `Report211-repro-v1.zip` (661,485 bytes, 18 files in `Report211/`; `Report211.tex`, 948 lines, 16 pp.) | none | `8622ca7e5` | Part II, Sections 13–23, plus the write's Section 24 |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status. Both manuscripts state that their
remainder constants and starting indices are existential; their decimal
tables are floating-point diagnostics, not interval bounds.

## What the report proves

Let `L(z) = −log(1 − z)`, `ρ = 1 − e^(−1)`, `M = e − 1`. Both Parts also treat
any analytic decoration `B` with nonnegative coefficients, `B(ρ) = 1` inside
its disk, difference span one (`gcd{j − k : b_j b_k > 0} = 1`) and positive
variance `v` of the size law `Pr(K = j) = b_j ρ^j` (mean `μ`).

**Part I (Report 185), A330499, `a_n = n! [z^n] Σ_k log(1 + L^k)`.**

- **Theorem 1.1:** for every `N`,
  `a_n ρ^n/n! = C + Σ_{j<N} n^(−3/4−j/2) H_j(√n) + O(n^(−3/4−N/2))` with
  `C = π²/(12(e − 1)) = 0.47865665562074963706…`; `H_0, H_1, H_2` explicit
  (Section 6). The OEIS entry records only the decimal `c = 0.478656...`.
- Lemma 2.1, Proposition 2.2: `Σ_k log(1 + q^k) = Σ_m (σ(odd m)/m) q^m`; the
  Stirling transform; labelled cycles of cycles with odd-divisor colours;
  `a_{n+1} > n a_n`.
- **Theorem 3.1:** the transfer for every admissible decoration, leading term
  `π²/(12μ)`, mode damping `exp(−π² m v/μ²)`, a finite recipe for every `H_j`.
  Proof: the Dedekind eta transformation, a pole-subtracted boundary integral
  and a uniform stationary-phase estimate (Lemma 5.1) summed over all modes.
- Lemma 7.1, **Theorem 7.2:** signed subsequences at scale `n^(−3/4)`; there is
  no refinement `C + c_1/n + O(n^(−2))`.
- Proposition 8.1, Corollary 8.2: odd-order root-of-unity cusps; no standard
  Delta-domain at `ρ`.
- **Theorem 9.1**, Proposition 9.2: two-ceiling threshold envelopes at every
  fixed order; the first oscillatory inverse shift; Lambert seed and Lagrange
  reversion.

**Part II (Report 211), A330498, `a(n) = n! [z^n] Σ_k k⁻¹ log(1 + L^k)`.**

- **Theorem 13.1:** for every `J`,
  `n ρ^n a(n)/n! = log 2 + Σ_{j<J} n^(−1/4−j/2) H_j(√n) + O(n^(−1/4−J/2))`, with
  `P_0, …, P_3` explicit (Section 13.1). In particular
  `a(n) ~ log 2 · (n − 1)! ρ^(−n)`: **this proves the conjecture `c = log 2`
  that Václav Kotěšovec records in A330498** (16 December 2019; the entry's
  formula field reads "a(n) ~ n! * c / (n * (1 - exp(-1))^n), where c =
  0.6931..., conjecture: c = log(2)."; live revision #13, read 7 October 2026).
- **Theorem 15.1:** the transfer for every admissible decoration, leading term
  `log 2`; proof by a Schwartz-space renewal interpolation (Lemma 16.1), a signed
  divisor Voronoi identity (Section 17) and a uniform all-harmonic Hankel
  estimate (Lemma 18.1); a finite recipe (Section 19).
- Section 20: signed subsequences at scale `n^(−1/4)`.
- **Corollary 21.1, Theorem 21.2:** eventual positivity, increase and strict
  log-convexity; two-ceiling inverse envelopes; a first inverse correction.

**The write** (front matter, "Guide to this report", with proof): the two
leading oscillatory functions have the same frequencies `2β_m = 2π√(2m/μ)`,
the same damping `exp(−π² m v/μ²)` and the same phase (`−cos(x + π/4) =
sin(x − π/4)`), and differ only in their amplitudes:
`σ(odd m)/m · (2π²m/μ)^(1/4)/√π` in Part I and `τ(odd m) · (8μ/m)^(1/4)` in
Part II. Neither manuscript states this; neither theorem follows from the
other.

(Section, statement and equation numbers are those of the committed PDF; the
numbering table below maps them to the manuscripts.)

## What the report does not claim

- No effective constants, cutoffs or onsets: every `O`-constant and starting
  index is existential (both Parts); no certified inverse algorithm; the
  positivity, increase and log-convexity onsets of A330498 are not computed.
- Nothing uniform as the decoration varies, the variance tends to zero, the
  support span changes or the order grows; no optimal truncation, no
  exponentially improved expansion, no global transseries.
- Part I does not classify all cusps or continuation domains; Part II asserts
  no Delta-domain and classifies no singularities.
- The signed subsequences give neither the exact `limsup`/`liminf` nor a
  limiting distribution of the oscillation.
- No single-ceiling inverse at every jump: both inverse theorems are
  two-ceiling envelopes, and the smooth charts are not canonical interpolations
  of the integer staircase.
- Classical inputs are credited, not claimed: the eta transformation (DLMF
  23.18; Ardehali–Rosengren's equation (15)), stationary phase, labelled
  supernecklaces (A003713; Flajolet–Sedgewick IV.28), Lambert initialization
  and Lagrange reversion (Part I); the compact-support divisor Voronoi formula
  (cited from Egger–Steiner, Theorem 1.1 (8), credited there to Hejhal, whose
  original Report 211 could not read), Hankel asymptotics (DLMF 10.17, 10.40),
  Fourier local-limit and renewal ideas (Part II).
- Priority: both source comparisons are bounded; Part II makes "no worldwide
  first-proof claim". The write searched the repository only.
- Report 211 tied its OEIS statements to the saved revision #13 because it
  could not reopen the live entry; the write read the live entries (A330499
  #11, A330498 #13, unchanged). Nothing was submitted to the OEIS.

## Further questions, and the standing rule

Section 24 gathers, under Vladimir's standing rule of 4 October 2026, every
question and unproved claim of both manuscripts with its source, sketch and
what is missing: effective constants and onsets; other support spans;
vanishing variance; joint phases, extremes and error laws; growing orders and
exponentially improved expansions; singularities and continuation domains;
other weights (Part I's item 6, answered for the weight `1/k` by Part II and
otherwise open); one ceiling at the jumps. No claim of either manuscript was
found to be false, so nothing is refuted.

## The inverses and the transseries volume

Classified statement by statement in the front matter against
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`:
the Lambert seeds (Part I (68), Part II (128)) are instances of
`p0:prop:factorial-core` (`κ = 1`, `d = −(1 + log ρ)`); Part I's Lagrange
reversion (70) is, as a formal series, an instance of `p0:prop:operator-form`
(its use at `ε = 1` is Part I's own argument); the one-step corrections (69),
(66) and (127) are analogues of that series' first term; the two-ceiling
Theorems 9.1 and 21.2 are proved directly at the integers and are **not**
instances of `p0:thm:staircase` (they reach the conclusion of its item (2) when
the ceilings agree).

## Relation to the repository

No other placed report treats A330499, A330498 or A003713. Part II's
"Other bounded comparisons" names `a301746-divisor-weighted-asymptotics`
(A301746, A294363) and `a124380-signed-moment-asymptotics` (A124380) of this
collection; its descriptions are accurate, and neither shares a theorem with
this report. No Lean or Rocq development treats these sequences.

## Labels and numbering

All labels carry the prefix `dep:`: Part I `dep:eta:` (Report 185's 97 labels),
Part II `dep:hl:` (Report 211's 79 labels), and the write's 19 (`dep:sec:` for
the front sections and Section 24, `dep:q:` for its eight questions,
`dep:eta:part`, `dep:hl:part`); 195 in all. The delivered labels were prefixed
before anything cited them (every `\ref` and `\eqref` updated; the delivered
texts use no `\cref`).

| Part | Manuscript | Sections | Statements | Equations | Tables |
|---|---|---|---|---|---|
| I | Report 185 | 1–12, unchanged | `k.j`, unchanged | (1)–(71), unchanged | 1–3 |
| II | Report 211 | `k + 12` (13–23) | `(k + 12).j` | `(k + 71)` (72–129) | 4–5 |

Both manuscripts number equations continuously, not by section; the merge
keeps that. Checked against the `.aux` files of separate builds of the two
delivered sources: every Part I number is unchanged, and every Part II number
is shifted exactly as in the table.

## Notation

No symbol was renamed. Common to both Parts: `L`, `ρ`, `M`, `B`, `K`, `μ`, `v`,
`κ_r`, `odd(m)`, the Stirling brackets, `u` as the argument of `H_j`,
`r = e^(−π²/M)`, the cutoffs `χ`, `δ`. The front-matter table "Notation across
the two Parts" lists every symbol that changes meaning, with the tempting false
readings: for example the two Parts' `P_j` are different functions of
different variables; Part II's `W` is the Lambert function, not Part I's germ
`W(θ)`; Part II's `ψ` is `log B(ρe^{iθ})`, not the digamma function; `H_j`,
`K_m`, `Φ_m`, `C`, `E`, `J`, `N` differ between the Parts.

## The write's additions

The front matter (Guide, status table, OEIS entries, inverses, notation,
provenance and merge decisions, what was checked, neighbours), the
`\partsource` blocks, Section 24, eleven dated `[write]` notes (Sections 1, 9,
10, 11, 12, 13, 21, 22, 23), the label prefixes, the bibliography keys
`oeisA330499` and `oeisA330498` (both delivered as `oeis`) and the entry
`tsvol`. The preamble is the union of the two delivered preambles plus
`longtable`, `xurl` and `mathrsfs`. Everything else is delivered text.

## Files

```text
README.md                                     this guide (replaces Report 185's delivered README)
article.tex                                   the merged report (delivered Report185.tex, merged with Report211.tex)
article.pdf                                   compiled report, 43 pages
185-eta-README_REPRODUCIBILITY.md             Part I: integrity and reproducibility limits (delivered README_REPRODUCIBILITY.md)
185-eta-optional-README.md                    Part I: optional numerical diagnostics (delivered optional/README.md)
code/185-eta-verify_exact.py                  Part I: mandatory exact kernel (delivered code/verify_exact.py)
code/185-eta-test_exact_guards.py             Part I: guard tests (delivered code/test_exact_guards.py)
code/185-eta-test_reproduction_guards.py      Part I: reproduction-guard tests (delivered code/test_reproduction_guards.py)
code/185-eta-reproduce.py                     Part I: reproducer, normal and -O (delivered reproduce.py)
code/185-eta-build.py                         Part I: offline release builder (delivered build.py)
code/185-eta-test_build.py                    Part I: build tests (delivered test_build.py)
code/185-eta-verify_manifest.py               Part I: manifest verifier (delivered verify_manifest.py; the generic helper)
code/185-eta-verify_frozen_sources.py         Part I: frozen-source hash check (delivered verify_frozen_sources.py)
code/185-eta-verify_diagnostic_provenance.py  Part I: diagnostic provenance check (delivered verify_diagnostic_provenance.py)
code/185-eta-optional-<name>.py               Part I: optional mpmath/NumPy/SciPy diagnostics (delivered optional/<name>.py): _common, _mp,
                                              check_two_point_decoration, diagnostics, fft_experiment, inverse_experiment, laguerre_check, run_all
code/211-harmonic-repro-verify_exact.py       Part II: exact checker (delivered repro/verify_exact.py)
code/211-harmonic-repro-verify_coefficients.py Part II: independent symbolic check of P_0..P_3 (delivered repro/)
code/211-harmonic-repro-derive_coefficients.py Part II: coefficient generator (delivered repro/)
code/211-harmonic-repro-diagnostics.py        Part II: 80/100-digit diagnostics (delivered repro/)
code/211-harmonic-repro-build_tables.py       Part II: TeX table builder/checker (delivered repro/)
code/211-harmonic-build_pdf.py                Part II: PDF builder (delivered Report211/build_pdf.py)
code/211-harmonic-verify_package.py           Part II: package verifier (delivered Report211/verify_package.py)
code/211-harmonic-verify_zip.py               Part II: ZIP verifier (delivered Report211/verify_zip.py)
data/185-eta-fixture21.json                   Part I: the 21 OEIS terms of A330499 (third-party, CC BY-SA 4.0)
data/185-eta-certificates-exact_checks.json   Part I: recorded output of the exact kernel (delivered certificates/exact_checks.json)
data/185-eta-provenance.json                  Part I: fixture and source provenance (delivered data/provenance.json)
data/185-eta-diagnostic_provenance.json       Part I: diagnostic provenance (delivered data/)
data/185-eta-FROZEN_SOURCE_HASHES.json        Part I: frozen source hashes (delivered data/)
data/185-eta-generated-<name>.json            Part I: BUILD_INFO, build_guards, verification (delivered generated/)
data/185-eta-optional-historical-<name>       Part I: historical numerical outputs (delivered optional/historical/): check_two_point_decoration.txt,
                                              explore.json, fft_experiment.json, inverse_experiment.json, replay.json
data/185-eta-optional-receipts-all_optional.json Part I: optional-run receipt (delivered optional/receipts/)
data/185-eta-optional-requirements.txt        Part I: optional stack pins (delivered optional/requirements.txt)
data/211-harmonic-repro-b330498.txt           Part II: Kotěšovec's OEIS b-file of A330498, n = 0..400 (third-party, CC BY-SA 4.0)
data/211-harmonic-repro-exact.json            Part II: recorded output of the exact checker
data/211-harmonic-repro-coefficients.json     Part II: P_0..P_3 exact
data/211-harmonic-repro-coefficients_check.txt Part II: recorded output of the coefficient check
data/211-harmonic-repro-diagnostics.json      Part II: recorded diagnostics (Tables 4-5)
data/211-harmonic-repro-requirements.txt      Part II: sympy==1.14.0, mpmath==1.3.0 (the generic file)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. Not shipped (verified at intake, retrievable
from `60f54ea06`): both delivered PDFs; `Report211.tex` and Report 211's
`README.md` (Report 185's `README.md` was staged and is replaced by this
guide); the checksum manifests `SHA256SUMS.json` (Report 185, 37 entries) and
`MANIFEST.json` (Report 211, 17 entries), each verified with full coverage.

```sh
git show 60f54ea06:docs/incoming/Decorated_Eta_Oscillatory_Asymptotics_and_Inverses_Source.zip > <scratch>/r185.zip
git show 60f54ea06:docs/incoming/Report211-repro-v1.zip > <scratch>/r211.zip
```

**Delivered text that names the delivery layout or a file not shipped.**
Report 185's programs import each other and the generic helper by their
delivered names (`verify_exact.py` imports `verify_manifest`); its reproducer,
builder, tests and frozen-source check need the closed delivered inventory,
`SHA256SUMS.json` and `Report185.tex`; `185-eta-README_REPRODUCIBILITY.md`,
`185-eta-optional-README.md` and the provenance JSON files use delivered paths
(`code/…`, `optional/…`, `README.md`); `data/185-eta-diagnostic_provenance.json`
also names the earlier scripts `verify.py`, `explore.py` and
`first_correction.py` from which the optional programs were adapted, which were
never delivered. Report 211's `verify_package.py` needs
`MANIFEST.json`, `Report211.tex` and the delivered layout; `verify_zip.py` needs
the release receipt `Report211-repro-v1.receipt.json`, **which was not
delivered** (only the ZIP arrived; Report 211's README documents it as a
sibling of the ZIP), so the ZIP verification cannot be run as documented. The
articles' sections on reproduction describe the delivered archives; dated notes
there say so.

**Third-party data.** `data/185-eta-fixture21.json` and
`data/211-harmonic-repro-b330498.txt` hold OEIS terms of A330499 and A330498
(the latter is Václav Kotěšovec's b-file, retrieved by Report 211 on 4 October
2026). OEIS content is published by The OEIS Foundation Inc. under CC BY-SA 4.0
(https://oeis.org/LICENSE); these files are third-party data under that
licence, **not** MIT-0 like the rest of the repository.

## Rerunning the checks (on scratch copies)

Never run the programs in place. From this directory (Git Bash):

```sh
# Part I: mandatory exact kernel (standard library only)
T=$(mktemp -d); mkdir -p "$T/r185/code" "$T/r185/data"
cp code/185-eta-verify_exact.py "$T/r185/code/verify_exact.py"
cp code/185-eta-verify_manifest.py "$T/r185/verify_manifest.py"
cp data/185-eta-fixture21.json "$T/r185/data/fixture21.json"
py -I -S -B "$T/r185/code/verify_exact.py" > "$T/r185.json"
tr -d '\r' < "$T/r185.json" | cmp - <(tr -d '\r' < data/185-eta-certificates-exact_checks.json) && echo same

# Part II: exact checker and the two coefficient programs
mkdir -p "$T/r211/repro"
for f in verify_exact verify_coefficients derive_coefficients; do
  cp "code/211-harmonic-repro-$f.py" "$T/r211/repro/$f.py"; done
cp data/211-harmonic-repro-b330498.txt "$T/r211/repro/b330498.txt"
cp data/211-harmonic-repro-coefficients.json "$T/r211/repro/coefficients.json"
py "$T/r211/repro/verify_exact.py" > "$T/r211.json"
tr -d '\r' < "$T/r211.json" | cmp - <(tr -d '\r' < data/211-harmonic-repro-exact.json) && echo same
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python "$T/r211/repro/verify_coefficients.py"
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python "$T/r211/repro/derive_coefficients.py" --order 4 --output "$T/coef.json"
```

At the write (7 October 2026, Windows, Python 3.14.4): Part I's kernel ran in
about 5 s and its output equalled `data/185-eta-certificates-exact_checks.json`
after CR stripping (21 fixture terms, the divisor identity to 100, Stirling
values and strict growth to 600, compositions to 60, the rational tail
certificate); Part II's exact checker ran in about 1 s and equalled
`data/211-harmonic-repro-exact.json` (401 b-file terms, nested logarithms to
degree 24); `verify_coefficients.py` printed `PASS: P0..P3 agree exactly`; and
`derive_coefficients.py --order 4` produced JSON equal to
`data/211-harmonic-repro-coefficients.json`. The intake dossier also reran
Part II's `diagnostics.py` (70 s; equal to the recorded file after CR
stripping) and `build_tables.py --check` (pass). Part I's `reproduce.py` failed
in the intake's sandboxed Windows session only because `unittest.mock` imports
`asyncio`, whose `_overlapped` module raised WinError 10106 there (an
environment failure, not a package defect). Part I's optional diagnostics need
mpmath, NumPy and SciPy and were not rerun; their historical outputs are
shipped. The release builders and `verify_package.py` (PDF byte identity is
specific to the authors' TeX) were not run.

## Build

pdfLaTeX (amsmath, amssymb, amsthm, mathtools, booktabs, array, longtable,
geometry, microtype, hyperref, xurl, mathrsfs, enumitem, lmodern). In a scratch
copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX: 43 pages; no errors or
warnings, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, no overfull or underfull boxes. The delivered
sources, built the same way, give 21 and 16 pages.

## Provenance

- Batch 110 of `docs/incoming`, cluster 110-ETA: bundle Reports 185 and 211
  (arrival `60f54ea06`), placed by `8622ca7e5` with the prefixes `185-eta-`
  and `211-harmonic-`; written 7 October 2026.
- Merge decisions: Report 185 is the base (earlier, the report that Report 211
  continues, positive weight with a combinatorial model); the two theorems are
  parallel results for different kernels, so both are printed in full and
  nothing is printed twice; one table of contents; one bibliography, with the
  two `oeis` keys renamed.
- Sources cited by the Parts: OEIS A330499, A330498 (and its b-file), A003713;
  DLMF 23.18, 18.15(iv), 10.17, 10.40; Ardehali–Rosengren, arXiv:2602.11329v1;
  Flajolet–Sedgewick, *Analytic Combinatorics*; Egger–Steiner,
  arXiv:1001.3556v4; two reports of this collection; the transseries volume
  (added by the write).
