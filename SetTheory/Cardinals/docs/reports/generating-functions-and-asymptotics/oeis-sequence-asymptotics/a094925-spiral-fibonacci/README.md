# Spiral Fibonacci Sequences (OEIS A094926, A094925 and A078510)

**Part I: hexagonal spiral Fibonacci asymptotics, certified amplitudes and
all fixed order corrections. Part II: square Spiro-Fibonacci growth and
inversion. Two independent studies of one construction family.**

A report in two Parts, built from two manuscripts of one external research
session (the session bundle of Reports 1–243, arrival commit `60f54ea06`),
placed by `8622ca7e5` (batch 110, cluster 110-SPIRAL) and written on
7 October 2026. Neither manuscript names an author, a tool or an addressee;
both PDF author fields read "Research report".

**The two Parts share a construction family, not a theorem.** Both study
spiral-Fibonacci ("Spiro-Fibonacci") sequences, where numbers are written
along a planar spiral and each new cell adds values at earlier neighbouring
cells, and both reduce the geometry to an exact recurrence with a delay of
order `√n`. Beyond that they are independent: different lattices and
adjacency rules, different recurrences (`a_n = a_{n−1} + a_{n−2} + Σ_{E_n}
a_j` versus `a_n = a_{n−1} + a_{t(n)}`), different growth classes (`C φ^n`
versus subexponential) and different proofs. No theorem, lemma or constant of
one Part is used in, implied by, or a special case of the other, and neither
re-proves anything of the other. They are bound in one report because they
are the repository's only treatment of spiral-Fibonacci recurrences and
Report 191 calls Report 190 its "prior companion report". The front matter's
Guide sets the two side by side.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Hexagonal Spiral Fibonacci Asymptotics: Certified amplitudes and all fixed order feedback corrections* (title block "Report190", 4 October 2026); the base | 190 | `Hexagonal_Spiral_Fibonacci_Asymptotics_and_Inverses_Source.zip` (789,595 bytes, 22 files; `Report190.tex`, 660 lines, 15 pp.) | `6bf7f30d0` (read-only comparison with the transseries volume, Section 11) | `8622ca7e5` | Part I, Sections 1–11 |
| *Square Spiro Fibonacci Growth and Inversion: Positive amplitude and quantitative asymptotics for A078510* (title block "Report191", 4 October 2026) | 191 | `Square_Spiro_Fibonacci_Growth_and_Inversion_Source.zip` (628,802 bytes, 23 files; `Report191.tex`, 766 lines, 19 pp.) | `9ba11eaf7` (transseries volume and Lambert W Guide, Section 21) | `8622ca7e5` | Part II, Sections 12–22, plus the write's Section 23 |

Both pinned commits exist and contain the files the manuscripts cite.

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status.

## What the report proves

**Part I (Report 190), A094926 and A094925** (seeds `(0, 1)` and `(1, 1)`;
`A094925(m) = a^(1)_{m−1}`, so its amplitude in its own indexing is `C_1/φ`).

- Proposition 2.1: the exact six-side delay formula for Kohmoto's hexagonal
  adjacency rule.
- **Theorem 1.1:** `a_n ~ C φ^n` for both seeds, and
  `a_n/(Cφ^n) = Σ_{k≤J} F_k(n) + O((1+r)^{J+1} Q^{(J+1)r})` for every fixed
  `J` (`Q = φ^(−6)`, `r ≈ √(n/3)`), with exact geometry-defined coefficients
  `F_k = S^k 1`. **This proves the equivalents conjectured by Manfred
  Scheucher (3 June 2015) in A094926 and A094925.**
- **Theorem 4.1:** exact algebraic bounds in `Q(φ)` that certify at least 120
  truncated digits of `C_0 = 0.54172002195814443386…`, `C_1 = 1.27063670814838…`
  and `C_1/φ = 0.78529667298898…`; they agree with all 106 supplied digits of
  A258639 and all 77 printed in A094925.
- Corollary 6.2 (seed independence beyond every fixed order), Theorem 7.1
  (nonzero leading profile of every correction sector).
- **Theorem 1.2:** `1 − a_n/(Cφ^n) = √n e^(−2√3 log(φ) √n) {G({√(12n)}) +
  O(n^(−1/2))}`, `G(θ) = φ^(4+θ)(φ² − θ)/√15`, with the exact envelopes
  `φ^6/√15` and `φ^(4+φ²)/(e√15 log φ)`.
- Theorem 9.1: the threshold lies in `{⌈x⌉, ⌈x⌉ + 1}`, `x = log_φ(y/C)`, and
  both occur infinitely often; Theorem 9.2: two-ceiling envelopes at every
  fixed order.

**Part II (Report 191), A078510** (each square cell adds the two closest
earlier centres).

- Lemma 13.1, Proposition 13.2: occupied rectangles and the exact predecessor
  `t(n) = n − 2k + 3 + 1{n = q_k}`, `n − t(n) = 4√n + O(1)`.
- **Theorem 12.1:** `a_n = C e^{H(n)} (1 + O(w³/√n))`, `w = W_0(4√n)`,
  `H = (√n/2)(w − 1 + 1/w) + w²/32 + w/2 − ½ log(1 + w)`, with `C > 0`, uniformly
  including corners; `log a_n ~ ¼ √n log n`. A078510 records no asymptotic
  formula, so this settles no OEIS conjecture, and Report 191 claims none.
- Propositions 17.1, 17.2: the smooth normalizer has non-summable defects
  (`w³/48 + w²/32 + …`); the homogeneous contraction product.
- **Theorem 12.2:** `N(Y) = r_0² − (4r_0/w_0)(Ψ + log C) + O(w_0²)`;
  `N(Y) ~ 4(log Y)²/(log log Y)²`. **Theorem 19.2:** every fixed
  inverse-logarithmic order, with an exact rational coefficient generator.

**The write** (front matter, "The OEIS entries", with proof): Scheucher's
accompanying heuristic in A094926, "a(n) = (a(n-1)+a(n-2))/(1-c*d^(-sqrt(n)))",
cannot hold with constants `c, d`, even asymptotically: by Part I's exact
forcing weights, the excess ratio `a_n/(a_{n−1} + a_{n−2}) − 1` drops by the
factor `φ^(−2)` from the last interior row of a side to its corner row, while
the heuristic form would make consecutive excesses asymptotically equal. This
bears only on the comment; the conjectured equivalent is proved.

(Section, statement and equation numbers are those of the committed PDF.)

## What the report does not claim

- Part I: no convergence of the correction hierarchy as the order grows (the
  constants `Q^(−k(k−1)/2)` give no uniform control), no closed form for the
  amplitudes, no effective onsets or certified inverse constants (an interval
  algorithm is described, not implemented), no uniform seed theorem, no
  universal exact rounding rule, no new-digit priority (the published digits
  predate the report).
- Part II: no certified digits of `C`, no sharp relative phase correction
  (the normalizer phase `Ξ` is a proof device below the stated error), no
  all-orders relative expansion of `a_n`, no effective threshold recovery.
- Credited, not claimed: the sequences and seed conventions (Kohmoto;
  Fernandez; the A265409 recurrence connection to Karttunen; Ryde's
  implementation), the golden-ratio prediction and amplitude digits
  (Scheucher, Kotěšovec), Binet's formula, variation of constants, positive
  products, Lambert balance, WKB normalization, implicit series and
  inverse-error transport. Kundrát's and Appleby–Buckwar's delay theorems are
  shown by Report 191 not to apply directly.
- Both source comparisons are bounded and make no worldwide priority claim.
  Nothing was submitted to the OEIS.

## Further questions, and the standing rule

Section 23 gathers, under Vladimir's standing rule of 4 October 2026, the
open questions of both Parts, kept in two lists because no question of one
Part is answered by the other: Part I (stated by the write from its limits)
— growing order, the amplitudes, effective onsets, other seeds; Part II
(Report 191's Section 22) — certified amplitude, sharper relative error,
further sequence corrections, effective threshold recovery, general delayed
models. No claim of either manuscript was found to be false; the only
refutation is of the OEIS comment's heuristic form above.

## The inverses and the transseries volume

Classified in the front matter against
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`:
the identity `N(y) = ⌈X(log y)⌉` in the proof of Part I's Theorem 9.2 and
Part II's (127) are instances of item (1) of `p0:thm:staircase` (both use an
admissible piecewise-linear interpolation of `log a_n`), and Part I's bracket
(66) follows from it as item (2) does; Part I's Theorem 9.1 is a direct
argument (an analogue); Part II's `V = 2W_0(√(2L))` (132) is an instance of
`p0:thm:lambert-core` (`a = 1`, `b = 2`, target `log 8L`), and its germ `δ`
(133) is, as a formal series, an instance of `p0:thm:lambert-centered`
(`a = 1`, `b = 2`, `Q(s) = log(1 − s + s²)`); the estimates, the germ's
convergence and the hierarchy are the Parts' own. Report 191's "supplied
manuscript" *Transseries for Mere Mortals* is one of the tutorials merged into
the volume's Part Q0.

## Independent check of the write (7 October 2026)

An independent adversarial check of the write (`d30bfb2a3`) reconstructed its
additions from the commit's diff, rebuilt both delivered manuscripts and diffed
them against the Parts, and read A094926 (#27), A094925 (#20), A258639 (#4)
and A078510 (#21) again.

- **Confirmed, checked hardest:** the write's proof that Scheucher's heuristic
  form `a(n) = (a(n-1)+a(n-2))/(1-c*d^(-sqrt(n)))` cannot hold with constants
  (re-derived from (12), (14), (17)). Numerically, both sequences generated
  from the six-side delay formula to `n = 40000` (equal to the OEIS data) give
  an excess ratio of exactly `0.3819660113 = φ⁻²` from the row before each final
  corner to the corner (stages 20, 60, 115), and `1.0` between non-corner rows.
- **Confirmed:** that Scheucher's two equivalents are proved as stated; the
  same terms reproduce all 106 digits of A258639 and all 77 of A094925 (`C_1/φ`);
  the quoted OEIS texts; the transseries identifications (`p0:thm:staircase`(1)
  for Theorem 9.2 and (127); `p0:thm:lambert-core` with `a = 1`, `b = 2` for
  `V = 2W_0(√(2L))`; `p0:thm:lambert-centered` for the germ, whose six
  printed coefficients the check recomputed); both pins and the Guide path;
  the *Mere Mortals* identification; the numbering table (Part I unchanged,
  Part II shifted by 11 sections and 66 equations; 88 + 103 + 20 labels); the
  37 staged files; both mandatory checkers (outputs equal to the records).
- **Clarified (dated note):** the two pin dates in "Provenance and merge
  decisions" are of different kinds (Report 190's comparison date and
  `9ba11eaf7`'s commit date); both commits were made on 3 October 2026
  (−0700), 39 minutes apart.

The check's record is the last paragraph of the front-matter section "What was
checked, and what was not". Its code and outputs are outside the repository.

## Relation to the repository

No other placed report treats A094926, A094925, A258639, A078510, A265409,
A265370, A265404 or spiral-Fibonacci recurrences. Report 191 cites the
repository's Lambert W Guide
(`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/lambert-w/Lambert_W_Guide/`)
for a constant-delay Lambert balance, as motivation only. No Lean or Rocq
development treats these sequences.

## Labels and numbering

All labels carry the prefix `sfb:`: Part I `sfb:hex:` (Report 190's 88
labels), Part II `sfb:sq:` (Report 191's 103), and the write's 20 (`sfb:sec:`
for the front sections and Section 23, `sfb:q:` for its nine questions,
`sfb:hex:part`, `sfb:sq:part`); 211 in all. The delivered labels were
prefixed before anything cited them.

| Part | Manuscript | Sections | Statements | Equations |
|---|---|---|---|---|
| I | Report 190 | 1–11, unchanged | `k.j`, unchanged | (1)–(66), unchanged |
| II | Report 191 | `k + 11` (12–22) | `(k + 11).j` | `(k + 66)` (67–144) |

Both manuscripts number equations continuously; the merge keeps that. Checked
against the `.aux` files of separate builds of the two delivered sources.

## Notation

No symbol was renamed. Because the Parts treat different sequences, most
letters differ in meaning: `a_n` and `C` (two unrelated amplitudes on
different scales), `r` (a stage versus `√x`), `t` (a side label versus the
predecessor function `t(n)`), `Q`, `ρ`, `α`, `β`, `H`, `F`, `D`, `θ`, `E`, `L`,
`U`, `N`, `X`, `K`, `W`. The front-matter table "Notation across the two
Parts" lists them with the tempting false readings.

## The write's additions

The front matter (Guide with the comparison table, status table, OEIS
entries with the note on Scheucher's heuristic, inverses, notation,
provenance and merge decisions, what was checked, neighbours), the
`\partsource` blocks, Section 23, ten dated `[write]` notes in the Parts
(Sections 1, 10, 11, 18, 19, 20, 21, 22 and in the proof part of Section 9),
the label prefixes, one merged entry for the shared key `fernandez`, a pointer
from Report 191's `report190` entry to Part I, a section prefix in Report
191's bibliography (`\ref{sec:sources}`), and the entry `tsvol`. The preamble
is the union of the two delivered preambles plus `longtable` and `xurl`.
Everything else is delivered text.

## Files

```text
README.md                                  this guide (replaces Report 190's delivered README)
article.tex                                the merged report (delivered Report190.tex, merged with Report191.tex)
article.pdf                                compiled report, 42 pages
190-hex-DATA_SOURCES.md                    Part I: sources and attribution (delivered DATA_SOURCES.md)
190-hex-README_REPRODUCIBILITY.md          Part I: reproduction and packaging (delivered README_REPRODUCIBILITY.md)
190-hex-code-README.md                     Part I: the exact code (delivered code/README.md)
190-hex-data-README.md                     Part I: the fixtures (delivered data/README.md)
191-square-DATA_SOURCES.md                 Part II: the same four guides for Report 191
191-square-README_REPRODUCIBILITY.md
191-square-code-README.md
191-square-data-README.md
code/190-hex-check_exact.py                Part I: mandatory exact checker (delivered code/check_exact.py)
code/190-hex-exact_arithmetic.py           Part I: exact Q(phi) and Q(sqrt 5) arithmetic (delivered code/)
code/190-hex-spiral.py                     Part I: the hexagonal walk and delay table (delivered code/)
code/190-hex-independent_certificate.py    Part I: independent certificate route (delivered code/)
code/190-hex-diagnose_float.py             Part I: optional mpmath diagnostics (delivered code/)
code/190-hex-reproduce.py                  Part I: replay in normal and -O modes (delivered reproduce.py)
code/190-hex-test_build.py                 Part I: package tests (delivered test_build.py)
code/190-hex-build.py                      Part I: offline release builder (delivered build.py)
code/190-hex-verify_manifest.py            Part I: manifest verifier (delivered verify_manifest.py)
code/191-square-check_exact.py             Part II: mandatory exact checker (delivered code/check_exact.py)
code/191-square-check_geometry.py          Part II: global geometry search (delivered code/)
code/191-square-spiral.py                  Part II: the square walk and predecessor (delivered code/)
code/191-square-inverse_series.py          Part II: exact inverse germ coefficients (delivered code/)
code/191-square-independent_series.py      Part II: independent coefficient check (delivered code/)
code/191-square-diagnose_mpmath.py         Part II: optional mpmath diagnostics (delivered code/)
code/191-square-reproduce.py               Part II: replay (delivered reproduce.py)
code/191-square-test_build.py              Part II: package tests (delivered test_build.py)
code/191-square-build.py                   Part II: offline release builder (delivered build.py)
code/191-square-verify_manifest.py         Part II: manifest verifier (delivered verify_manifest.py)
data/190-hex-oeis_fixtures.json            Part I: 41 + 38 OEIS terms, 106 + 77 amplitude digits (third-party, CC BY-SA 4.0)
data/190-hex-generated-exact_checks.json   Part I: recorded output of the exact checker
data/190-hex-generated-verification.json   Part I: recorded replay summary
data/190-hex-generated-BUILD_INFO.json     Part I: recorded build metadata
data/190-hex-generated-build_guards.json   Part I: recorded build guards
data/191-square-oeis_fixtures.json         Part II: 64 OEIS terms of A078510 (third-party, CC BY-SA 4.0)
data/191-square-generated-exact_checks.json Part II: recorded output of the exact checker
data/191-square-generated-verification.json Part II: recorded replay summary
data/191-square-generated-BUILD_INFO.json  Part II: recorded build metadata
data/191-square-generated-build_guards.json Part II: recorded build guards
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. Not shipped (retrievable from `60f54ea06`):
both delivered PDFs, `Report191.tex` and Report 191's `README.md` (Report
190's `README.md` was staged and is replaced by this guide), and the two
checksum manifests `SHA256SUMS.json` (21 and 22 entries), verified at intake
with full coverage.

```sh
git show 60f54ea06:docs/incoming/Hexagonal_Spiral_Fibonacci_Asymptotics_and_Inverses_Source.zip > <scratch>/r190.zip
git show 60f54ea06:docs/incoming/Square_Spiro_Fibonacci_Growth_and_Inversion_Source.zip > <scratch>/r191.zip
```

**Delivered text that names the delivery layout or a file not shipped.** The
programs of both packages import their siblings by delivered names
(`check_exact.py` imports the modules beside it in `code/` and reads
`../data/oeis_fixtures.json`); the replay, test and build scripts check the
closed delivered inventory, including the manuscript and `SHA256SUMS.json`,
so they run only in a re-extracted archive; the eight `190-hex-*.md` and
`191-square-*.md` guides use delivered paths (`code/…`, `data/…`,
`README.md`, `Report190.tex`, `Report191.tex`); and the articles' sections on
verification describe the delivered archives (dated notes there say so).

**Third-party data.** The two `oeis_fixtures.json` files hold OEIS terms and
amplitude digits (A094926, A094925, A258639; A078510). OEIS content is
published by The OEIS Foundation Inc. under CC BY-SA 4.0
(https://oeis.org/LICENSE); these files are third-party data under that
licence, **not** MIT-0 like the rest of the repository. The package data
READMEs give the attribution.

## Rerunning the checks (on scratch copies)

Never run the programs in place. From this directory (Git Bash):

```sh
T=$(mktemp -d)
for P in 190-hex 191-square; do
  mkdir -p "$T/$P/code" "$T/$P/data"
  for f in code/$P-*.py; do b=$(basename "$f"); cp "$f" "$T/$P/code/${b#$P-}"; done
  cp "data/$P-oeis_fixtures.json" "$T/$P/data/oeis_fixtures.json"
  py -I -S -B "$T/$P/code/check_exact.py" > "$T/$P.json"
  py -I -S -B -O "$T/$P/code/check_exact.py" > "$T/$P-O.json"
  cmp "$T/$P.json" "$T/$P-O.json"
  tr -d '\r' < "$T/$P.json" | cmp - <(tr -d '\r' < "data/$P-generated-exact_checks.json") && echo "same $P"
done
```

At the write (7 October 2026, Windows, Python 3.14.4) both checkers ran in
about 6–7 s and their outputs equalled the recorded
`data/190-hex-generated-exact_checks.json` (219,581 bytes: the delay table
through 1162 rows, 79 OEIS terms, stage-weight identities, the stage-100
certificates in two arithmetic bases) and
`data/191-square-generated-exact_checks.json` (64 OEIS terms, the predecessor
through `n = 250000`, the global search through 4096, the inverse germs). The
intake dossier found the normal and `-O` outputs byte-identical. The
packages' `reproduce.py` scripts were not run on Windows: the same package
family's replay fails there because it compares text-mode stdout with CRLF
line ends to its output file (see the batch-110 intake record). The optional
mpmath diagnostics and the builders were not run.

## Build

pdfLaTeX (amsmath, amssymb, amsthm, mathtools, booktabs, array, longtable,
geometry, microtype, hyperref, xurl, enumitem, lmodern). In a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was rebuilt this way with MiKTeX after the independent check
(7 October 2026): 42 pages (the write's build had 41); no errors or
warnings, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, no overfull or underfull boxes. The delivered
sources, built the same way, give 15 and 19 pages.

## Provenance

- Batch 110 of `docs/incoming`, cluster 110-SPIRAL: bundle Reports 190 and 191
  (arrival `60f54ea06`), placed by `8622ca7e5` with the prefixes `190-hex-`
  and `191-square-`; written 7 October 2026.
- Merge decisions: the intake's dossier offered one report in two Parts or two
  single reports; the placement chose one report, and the write keeps it while
  stating that the Parts share no theorem. Report 190 is the base (cited by
  Report 191 as prior; settles two OEIS conjectures). Nothing is printed
  twice. One bibliography: the shared `fernandez` entry merged, `report190`
  pointed to Part I, `tsvol` added.
- Sources cited by the Parts: OEIS A094926, A094925, A258639, A078510,
  A265409, A265370, A265404; Fernandez, *Spiro-Fibonacci Sequences*; Ryde,
  Math::NumSeq::SpiroFibonacci; Kundrát (2005, 2006); Appleby–Buckwar (2010);
  the ProveIt transseries volume and Lambert W Guide; *Transseries for Mere
  Mortals*.
