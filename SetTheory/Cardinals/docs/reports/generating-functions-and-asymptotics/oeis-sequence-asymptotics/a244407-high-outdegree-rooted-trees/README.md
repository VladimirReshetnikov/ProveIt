# High Maximum Outdegree in Rooted Unlabeled Trees (OEIS A244407, A244410, A244372)

**Exact diagonals, the exact two-hub and third high-outdegree sectors, every
fixed algebraic order, a Rayleigh hub depth, and Lambert-W inverses for the
number `T(N, k)` of rooted unlabeled trees on `N` vertices with maximum
outdegree exactly `k`.**

A report in two Parts, built from two manuscripts of one external research
session (the session bundle of Reports 1–243, arrival commit `60f54ea06`),
placed by `f79c9bef1` (batch 112) and merged on 7 October 2026. Both are
dated 5 October 2026; their title blocks read "Report 227" and "Report 229"
and both PDF author fields "Research report": neither names a person, tool or
addressee.

| Part | Source | Archive | Placed | Printed as |
|---|---|---|---|---|
| I | *High maximum outdegree in rooted unlabeled trees: Exact diagonals and two hub corrections for OEIS A244407 and A244410* ("Report 227"), the base | `Report227.zip` (566,903 bytes, 15 files, wrapper `Report227/`; `report227.tex`, 670 lines, 18 pp.) | `f79c9bef1`, unprefixed text, files `227-twohub-` | Part I, Sections 1–8 |
| II | *Exact third high outdegree sectors in rooted unlabeled trees: A continuation of Report 227 with uniform two parameter asymptotics* ("Report 229") | `Report229.zip` (1,063,459 bytes, 21 files, wrapper `Report229/`; `report229.tex`, 858 lines, 21 pp.) | `f79c9bef1`, files `229-third-` (text not staged) | Part II, Sections 9–18 |

Neither package records a ProveIt commit, so no pin is recorded.

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status. **No priority is claimed:** the full
text of Goh–Schmutz, *Unlabeled trees: distribution of the maximum degree*
(Random Structures Algorithms 5, 1994) was not compared by either source or
by the write.

## What the report proves

`r_n` counts rooted unlabeled trees, `R = Σ r_n z^n`, `G = 1/(1−R)`,
`H = Π_{s≥1}(1−z^s)^{−r_{s+1}}` (excess forests), `F = HG = Σ f_m z^m`,
`ρ ≈ 0.3383` the Otter radius.

Part I (Report 227):

- **Theorem 2.2:** `T(k+m+1, k) = f_m` for `0 ≤ m < k` and
  `T(2k+1, k) = f_k − 1`; hence `A244407(n) = f_{n−1}`,
  `A244410(n) = f_n − 1 = A244407(n+1) − 1` (`n ≥ 1`), via the
  orbit-pointing Theorem 2.1.
- **Theorem 3.2:** `0 ≤ 1 − T(N,k)/f_m ≤ A_*(N+1)ρ^k` uniformly, with the
  base `ρ` sharp; Corollary 3.3: `P(Δ_N = k)` for the rare event.
- **Theorem 4.1:** the exact two-hub sector `T(2k+r+1, k) = f_{k+r} − b_r`
  for `0 ≤ r < k`, with an explicit positive series `𝓑 = Σ b_r z^r`;
  Corollary 4.3: `T(3k+1, k) = f_{2k} − b_k + 2`.
- **Theorems 5.1, 5.2:** every fixed algebraic order of `f_m` and of `b_r`
  (`b_r ~ Lρ^{−r}√r`, the `s^{−2}` term of `𝓑` cancels), with a Bernoulli
  engine for the corrections `d_j`.
- **Theorems 6.1, 6.2:** conditioned on `Δ_N = k` with `k/log N → ∞`, the
  hub depth over `√m` is Rayleigh (all integer moments), and the decoration
  is tight with tail `s^{−3/2}`, infinite integer moments, asymptotically
  independent of the depth.
- **Theorems 7.1, 7.2:** `x_0(y) = −W_{−1}(−2λ(K/y)²)/(2λ)` with
  fixed-order corrections, and two-ceiling enclosures of the integer
  thresholds.

Part II (Report 229), which answers Part I's third-sector question:

- **Theorem 9.1:** `T(3k+r+1, k) = f_{2k+r} − b_{k+r} + U_r + kV_r` for
  `0 ≤ r < k` (sizes `3k+1 ≤ N ≤ 4k`), with explicit series `U`, `V`; at
  `N = 4k+1` the extra correction is `−7` (`−6` at `k = 1`).
- Lemmas 10.1–10.2: an exact signed type-deletion identity; **Theorem 11.1:**
  the root tail with an exact nonnegative remainder (the source of the
  affine dependence on `k`); Proposition 12.1: the all-size deficit
  congruence.
- **Theorem 15.2:** both negative even poles of `U` cancel (`u_{−4} = u_{−2} = 0`,
  by an explicit hand-checkable polynomial identity).
- **Theorem 16.1, Corollary 16.2:** separate fixed-order expansions of `U_r`
  and `V_r` and a uniform crossover in `κ = k/r²`, including unbounded `κ`
  (`A_V/A_U ≈ 900.11`); Section 16.1: four separate errors for the full
  three-sector formula.

(Section, statement and equation numbers are those of the committed PDF.)

## What the report does not claim

The Pólya–Otter theory, Genitrini's all-order development, singularity
transfer, moments and Lambert-W inversion are prior; `C = H(ρ)` is classical
(Schwenk, Drmota–Gittenberger); the leading diagonal constants are
Kotěšovec's (OEIS, 2014). No worldwide novelty or priority claim (the
Goh–Schmutz full text was unavailable). Every fixed-order statement is a
fixed finite truncation: no convergent or optimally truncated series, no
uniform transseries, and a truncation of an earlier sector may exceed a whole
later sector. No central-window law, no local limit or depth rate, no full
fourth sector (`−7` is one coefficient), no coefficientwise positivity of
`U`; thresholds are enclosures without effective constants; all decimals are
uncertified; finite tests corroborate, they do not prove.

## The write's findings

- **The OEIS entries** (Remark 1.1): A244372 (#23), A244407 (#14), A244410
  (#11) quoted; Kotěšovec's constants `c = 0.9495793…`, `c = 2.806733…`
  and `d = 2.955765285651994974714817524…` are `ρK`, `K`, `1/ρ`, correctly
  truncated. The entries state neither `A244407(n) = f_{n−1}` nor
  `A244410(n) = A244407(n+1) − 1`; they contain no conjecture, so none is
  settled. No OEIS edit.
- **Every exact identity confirmed against the OEIS data:** the whole
  A244372 b-file (rows `N ≤ 141`, 10,011 terms) satisfies the plateau (4970
  cases), the first boundary (70), the two-hub sector (1657), `T(3k+1,k)`
  (46), the third sector (828) and the `−7`/`−6` boundary (35); the write's
  own bounded-outdegree count agrees with the b-file for `N ≤ 60`; all
  b-file terms of A244407 (100) and A244410 (101) match.
- **Decimals:** every printed constant of both Parts recomputed from the
  write's own 60-digit jets; all are correct roundings (Part I's `K` ends in
  a rounded digit; nothing is printed with "…"). `x_5(f_500) − 500 =
  1.2339325093…×10⁻¹⁰` reproduced. The pole cancellations
  `[s^{−2}]𝓑 = u_{−4} = u_{−2} = 0` confirmed from direct Laurent
  expansions to `10⁻⁵⁸`.
- **Positivity evidence for Part II's question 3:** `U_r > 0` for every
  `0 ≤ r ≤ 520` (exact), while `[z^13]W = −7692`; not a proof.
- **Remark 7.3 (transseries volume):** `M_J` is literally the model
  `p0:def:model`; `x_0` is an exact instance of `p0:thm:lambert-core`
  (negative-coefficient branch, `W_{−1}`); the corrections `q_j` are a
  formal instance of `p0:thm:lambert-centered`, so `x_0 + Σ q_j x_0^{−j}` is
  the asymptotic inverse of `p0:def:three-inverses`(3); Theorem 7.2 is an
  analogue of `p0:thm:staircase`(2) proved directly, not an instance.

## Further questions, and the standing rule

Part I's Section 8.2 and Part II's Section 18.2 (the sources' lists, each
with a dated note under Vladimir's standing rule of 4 October 2026). Part I's
question 2 (a third sector) is answered by Part II; open: the Goh–Schmutz
comparison, the bridge to the central window, interval-certified constants and
effective enclosures, optimal truncation, depth local limits and rates, a
full fourth sector, the general threshold dependence of higher sectors,
coefficientwise positivity of `U` (tested to `r = 520`), growing-order
methods. No claim of either source was found false, and nothing is refuted.

## Independent check of the write (7 October 2026)

An independent adversarial check of the batch-112 write (`155fb997d`), with
its own code, confirmed every claim of the write; nothing needed correction.

- **OEIS.** A244372 (#23), A244407 (#14), A244410 (#11) read again: the
  quotations, revisions, dates and attributions of Remark 1.1 are verbatim,
  the posted constants are truncations of `ρK`, `K`, `1/ρ`, and the entries
  hold no conjecture.
- **Exact.** Own series reproduce the printed `f_m`, `b_r`, `U_r`, `V_r` and
  `[z^13]W = −7692`; the signed and positive forms of `𝓑` agree; the A244372
  b-file gives the six case counts above with no failure. A brute-force
  enumeration of canonical trees (`N ≤ 14`) and a cycle-index count of
  bounded-outdegree trees (`N ≤ 70`, `k ≤ 24`) agree with the b-file; the
  root tails agree with Theorem 11.1 for `q ≤ 6`.
- **Decimals, by a second route.** Besides the closed forms from the critical
  equation, Richardson extrapolation of the exact `f_m`, `r_n`, `b_r`, `U_r`,
  `V_r` (`400 ≤ m ≤ 1200`, no Puiseux jet) gives `K`, `ρK`, `d_1…d_6`,
  `e_1…e_3`, `τ`, `L`, `c^B_{−1}`, `A_U`, `α_1/α_0` (hence `u_{−3}`), `A_V`
  (hence `J_3(ρ)`) to at least 25 agreeing digits; fits admitting
  half-integer powers confirm the missing `s^{−2}` of `𝓑` and `s^{−4}`,
  `s^{−2}` of `U`. Every source decimal is a correct rounding, every "…" of
  the write a correct truncation; `x_5(f_500) − 500` reproduced.
- **Evidence extended:** `U_r > 0` for every `r ≤ 1200` (not a proof).
- **Also confirmed:** Remark 7.3 per statement against the volume; the
  provenance (566,903 and 1,063,459 bytes, 15 and 21 files, 670 and 858
  lines, 18 and 21 pages, manifests 12/12 and 18/18, `public227/`
  byte-identical); the 26 staged delivered files byte-identical; 168
  delivered labels with their numbers (Part II shifted by 8 sections and 57
  equations) on the check's own builds; the README listing (29 files); no
  earlier repository mention; the delivered suites reproduce their records
  on scratch copies.

The check is recorded in a dated note at the end of the Guide. Rebuilt:
44 pages (unchanged), label numbers unchanged.

## Relation to the repository

No other file of the repository names A244407, A244410 or A244372. Nearest
(same directory): `a116379-bounded-identity-trees` (rooted *identity* trees
with outdegree at most a *fixed* cap, A116379/A116380 — a different class
and regime), `a242375-many-color-rooted-trees`,
`a003238-uniform-trees-binary-partitions` and `a055779-labeled-fat-trees`
(batch 112). No shared result, so no reciprocal note. No Lean or Rocq
development treats these sequences.

## Labels and numbering

Part I's labels carry `hod:two:`, Part II's `hod:three:`; the write's Guide
label is `hod:sec:guide`, its Part labels `hod:two:part`, `hod:three:part`,
its remarks `hod:two:rem:oeis` and `hod:two:rem:transseries`. The 168
delivered labels (71 + 97) were prefixed before anything cited them (147
references updated: Part I 50 `\eqref`, 6 `\ref`; Part II 82 `\eqref`,
9 `\ref`); 173 labels in all. Part I keeps every delivered number; Report
229's Section `k` is Section `k+8` and its equation `(k)` is `(k+57)`, its
statements moving with their sections (checked against the `.aux` files of
builds of both delivered texts: 168 labels, 0 differences). The write's
remarks (1.1, 7.3) are the last statements of their sections and its
additions contain no numbered display.

## Notation

No symbol was renamed. The Guide's reading-conventions table lists the
letters with several senses and the false readings: the sector offset `r`
(`N = 2k+r+1` in Part I, `N = 3k+r+1` in Part II), `𝓑`/`B`/`b`,
`D`/`𝒟`/`d` (Part II's `d_2 = D(z²)` is not Part I's `d_2 ≈ 68.44`), `W`
(Lambert function versus Part II's series `W`), `J`, `H`/`h`, `K`, `M`,
`P`/`Q`, `A`/`a`, `c`, `L`/`ℒ`, `X`/`s`, `U`/`V`/`u`/`v`, `S`/`δ`/`τ`,
`λ`/`κ`, `e`/`f`/`α`, `R_{<k}`.

## The write's additions

The title block, merged abstract and status note; the Guide (structure,
numbering, provenance, sources read, checks, relation, collected non-claims,
reading conventions); the Part headers with the delivered abstracts; Remarks
1.1 and 7.3; the dated notes after Corollary 4.3, in Sections 5.2, 5.3 and
8, after Part I's question list, and in Sections 9.1, 14.1, 16.1, 17.3, 17.4,
18.1 and 18.2; the label prefixes; the merged bibliography (with `TSvol`);
the merged preamble with the `\file` macro and the `writenote`,
`partabstract`, `partsource` definitions. Everything else is delivered text.

## Files

```text
README.md                                   this guide (replaces Report 227's delivered README.md)
article.tex                                 the report (Report 227's report227.tex + Report 229's report229.tex, merged)
article.pdf                                 compiled report, 44 pages
227-twohub-SOURCES.md                       Report 227's source-provenance and attribution note
227-twohub-code-README.md                   Report 227's code guide (delivered code/README.md)
227-twohub-data-README.md                   Report 227's data guide (delivered data/README.md)
229-third-SOURCES.md                        Report 229's source-scope note
229-third-code-README.md                    Report 229's code guide (delivered code/README.md)
code/227-twohub-build.py                    Report 227's verifier, PDF and ZIP builder (delivered root build.py)
code/227-twohub-exact.py                    exact series, bounded-tree recurrence, colored canonical trees
code/227-twohub-make_fixtures.py            generator of the exact fixture
code/227-twohub-numerics.py                 mpmath jets, constants and inverse coefficients (finite-order engine)
code/227-twohub-reproduce.py                Report 227's check runner (quick/full/caps profiles)
code/229-third-build.py                     Report 229's checker, PDF and ZIP builder (delivered root build.py)
code/229-third-check_guards.py              input and output-path guard tests (normal and -O)
code/229-third-check_poles.py               optional SymPy certificate (normal form, poles, u_{-5}, u_{-3})
code/229-third-numerics.py                  Decimal constants (table of Section 17.3)
code/229-third-output_json.py               exclusive JSON writer used by the CLIs
code/229-third-reproduce.py                 exact third-sector, deficit, boundary, root-tail and literal-tree checks
code/229-third-third_sector.py              exact series, bounded counts and the check routines (sector, root tails, literal trees)
data/227-twohub-build_checks.json           Report 227's build receipt (delivered root)
data/227-twohub-exact_coefficients.json     exact-generated fixture (delivered data/)
data/227-twohub-oeis_samples.json           OEIS samples with URLs and offsets (third-party; delivered data/)
data/229-third-build_checks.json            Report 229's build receipt (delivered root)
data/229-third-tests-exact_checks.json      output of reproduce.py (delivered tests/)
data/229-third-tests-exact_checks_optimized.json  output of reproduce.py under -O (byte-identical to the previous file, as delivered)
data/229-third-tests-guard_checks.json      output of check_guards.py (delivered tests/)
data/229-third-tests-numeric_checks.json    output of numerics.py (delivered tests/)
data/229-third-tests-pole_checks.json       output of check_poles.py (delivered tests/)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. Not shipped (retrievable from `60f54ea06`):
the delivered `Report227.pdf` (18 pages) and `Report229.pdf` (21 pages);
Report 229's `report229.tex` (Part II of `article.tex`) and its delivered
`README.md`; Report 229's `public227/`, a byte-identical copy of Report 227's
`report227.tex` and `Report227.pdf`; and the two pure checksum manifests
`MANIFEST.sha256` (12 and 18 entries, both verified at the write).

```sh
git show 60f54ea06:docs/incoming/Report227.zip > <scratch>/r227.zip
git show 60f54ea06:docs/incoming/Report229.zip > <scratch>/r229.zip
```

**Delivered text that names the delivery layout.** The two code guides,
`227-twohub-data-README.md` and both `SOURCES.md` files use the delivered
names (`report227.tex`, `code/exact.py`, `tests/…`, `public227/`,
`MANIFEST.sha256`); the programs import each other by their delivered names
and Report 227's runner reads `data/exact_coefficients.json` and
`data/oeis_samples.json`; both builders expect the delivered root layout and
verify the manifest, so they run only in a re-extracted archive. Part I's
Section 8 and Part II's Section 17.4 describe the delivered packages (dated
notes there say what is shipped).

**Third-party data.** `data/227-twohub-oeis_samples.json` holds OEIS terms
(CC BY-SA 4.0, https://oeis.org/LICENSE), not MIT-0 like the rest of the
repository.

## Rerunning the checks (on scratch copies)

Never run the programs in place. From this directory (Git Bash), restore the
delivered names in a scratch directory:

```sh
T=$(mktemp -d); mkdir -p "$T/r227/code" "$T/r227/data" "$T/r229/code"
for f in exact make_fixtures numerics reproduce; do cp code/227-twohub-$f.py "$T/r227/code/$f.py"; done
for f in exact_coefficients oeis_samples; do cp data/227-twohub-$f.json "$T/r227/data/$f.json"; done
for f in check_guards check_poles numerics output_json reproduce third_sector; do cp code/229-third-$f.py "$T/r229/code/$f.py"; done
(cd "$T/r227" && py -B code/reproduce.py --caps --numerics --order 5 > ../r227.json)     # mpmath 1.3.0
(cd "$T/r229" && py -B code/reproduce.py --output ../exact_checks.json \
              && py -B code/check_poles.py --output ../pole_checks.json \
              && py -B code/numerics.py --output ../numeric_checks.json)                 # SymPy for check_poles
for f in exact_checks pole_checks numeric_checks; do
  cmp <(tr -d '\r' < "$T/$f.json") <(tr -d '\r' < data/229-third-tests-$f.json) && echo "same $f"; done
```

At the write (7 October 2026, Windows, Python 3.14.4, mpmath 1.3.0, SymPy
1.14.0): Report 227's runner gave the same JSON under `-O`, equal to the
`mathematical` part of `data/227-twohub-build_checks.json` except the
recorded Python version (the delivered run used 3.12.14); Report 229's three
outputs (and `reproduce.py` under `-O`) equalled the delivered `tests/` files
after removing carriage returns (`reproduce.py` 47 s). The guard suite and
the builders were not run (the intake recorded the guard suite's symlink
sub-test as a Windows-only failure).

## Build

pdfLaTeX (lmodern, amsmath, amssymb, amsthm, mathtools, booktabs, microtype,
geometry, enumitem, longtable, array, hyperref, bookmark). In a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX pdfLaTeX (7 October 2026):
44 pages; no errors or warnings, no undefined references, no multiply
defined labels, no duplicate destinations, no overfull or underfull boxes
(the log's "duplicates ignored" lines are font-map notices from the
delivered `\pdfmapfile` lines, also in the delivered builds). The delivered
texts give 18 and 21 pages with no warnings. Rebuilt at the independent
check (7 October 2026, pdfLaTeX ×3): 44 pages, the same clean log.

## Provenance

- Batch 112 of `docs/incoming`: bundle Reports 227 and 229 (arrival
  `60f54ea06`), placed by `f79c9bef1` (227 as base, unprefixed text; 229's
  files prefixed); merged 7 October 2026.
- Sources cited by the report: Otter (1948); Schwenk (1977);
  Drmota–Gittenberger (1999); Gittenberger (2006); Goh–Schmutz (1994);
  Genitrini (2016); Flajolet–Sedgewick (2009); Corless et al. (1996);
  Bartholdi–Diaconis (2026); Bassan–Donderwinkel–Kolesnik (2026); OEIS
  A244372, A244407, A244410; and the repository's transseries volume (added
  by the write).
