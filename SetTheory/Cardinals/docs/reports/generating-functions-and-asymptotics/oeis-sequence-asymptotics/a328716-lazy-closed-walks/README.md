# Lazy Closed Walks in Growing Dimension: All Fixed Orders, Parity-Conditioned Poisson Laws and Occupied-Axis Fluctuations (OEIS A328716, A328718)

**For the number `a_n` of `n`-step closed walks in `ℤ^n` with steps `0`,
`±e_i` (A328716): `a_n = C_ε (dn)^n {Σ_{ℓ≤M} c_{ε,ℓ} n^{−ℓ} + O(n^{−M−1})}`,
`ε = (−1)^n`, for every `M`, with Bessel definitions of Kotěšovec's constants
`d = F(r)/(er)` and `C_±` and explicit `c_{ε,1}, c_{ε,2}, c_{ε,3}`; an absolute
complex-uniform marked expansion, valid at the zeros of its amplitude; the
zero-step count to every order in a weighted `ℓ¹` norm about a
parity-conditioned Poisson law; occupied axes Gaussian on scale `√n`,
asymptotically independent of the zero steps, with a parity-dependent mean
offset; parity inverse brackets with an eventual global width at most one; a
compact proportional `N/D` extension.**

A research article dated 3 October 2026 ("Report 179" of a session bundle),
built from one manuscript. Its author line and PDF author field read
"Research report 179": it names no person, tool or addressee. The package
carries no "prepared for private review" line, no e-mail address and no
personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 179 (batch 109) | `Lazy_Closed_Walks_Asymptotics_and_Inverses_Source.zip` (26 files, no wrapper directory, 617,713 bytes, SHA-256 `e433f40b68ba…e5473b44f613`), arrival commit `60f54ea06`; main file `Report179.tex` (701 lines, 16 pp.) | `83befe707` (ProveIt, 3 October 2026, "Transfer macro continuation sharing to the complete projective compiler"; exists), the commit of the source's bounded repository comparison | `f7e9e5c2f` (batch 109) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report.

## Trust boundaries

- **What is proved by hand.** Proposition 2.1, Lemma 3.1 and Theorems 4.1,
  6.1, 7.1, 8.1 and 9.1: the Bessel-product count, a two-arc saddle analysis
  with an absolute integrated remainder, Cauchy estimates on a larger disk,
  an analytic moving saddle with Lévy's continuity theorem, and monotone
  parity brackets.
- **What rests on computation.** `c_{ε,2}`, `c_{ε,3}` (22)–(23) and higher
  orders come from the finite algorithm of Section 4, checked by the shipped
  programs (exact `Fraction` arithmetic and two independent routes).
- **What is diagnostic.** Every decimal, including the table of Section
  10.3: high-precision, not interval-certified.
- **What is prior.** The exact formula (Gutkovskiy) and the numerical leading
  equivalent (Kotěšovec), both in the OEIS; the Bessel walk generating
  function (Gessel–Weinstein–Wilf 1998, equation (2)); the large-powers method
  with full expansions, compact-ratio uniformity and vanishing multipliers
  (Flajolet–Sedgewick, Theorem VIII.8).

## What it proves

`F(z) = I_0(2z)`, `𝒟 = z d/dz`; `r` solves `2rI_1(2r)/I_0(2r) = 1`,
`b = 4r² − 1`; `d = F(r)/(er)`, `C_ε = E_ε(r)/√b`, `E_ε(t) = e^t + εe^{−t}`.
Equation and statement numbers are the delivered ones (the article numbers
equations consecutively).

- **Proposition 2.1 (`lcw:prop:exact`)**: `A_{N,D}(u) = N![z^N] e^{uz} F(z)^D`
  (2), the joint law (3), and `a_{n+1} > a_n` for `n ≥ 1` (an injection).
- **Lemma 3.1 (`lcw:lem:saddle`)** and (7)–(9): the saddle, the constants and
  the cumulants as polynomials in `b`.
- **Theorem 4.1 (`lcw:thm:absolute`)**: (14)–(15), uniformly for complex
  `|u| ≤ R`, with an absolute remainder; Remark 4.2 at the zeros of
  `E_ε(ru)`.
- Section 5: `c_{ε,1}`, `c_{ε,2}`, `c_{ε,3}` (21)–(23) and their table.
- **Theorem 6.1 (`lcw:thm:weighted`)**: the weighted `ℓ¹` expansion (26) about
  `J_ε` = Poisson(`r`) conditioned on parity `ε`, with `Q_{ε,1}` (27).
- **Theorem 7.1 (`lcw:thm:occupation`)**: `(K_n − np)/√n ⇒ 𝒩(0, τ²)` (31),
  jointly with `J_n` (32), and `E K_n = np − (q/b)(v_ε + (b−1)/2 − 1/b) +
  O(1/n)` (33).
- **Theorem 8.1 (`lcw:thm:inverse`)**: parity brackets (40) about the roots of
  the carriers (38) and `L_M ≤ ν(X) ≤ U_M`, `U_M − L_M ∈ {0, 1}` (41); the
  closed form `t_{ε,0} = Y_ε/W_0(dY_ε)` (42).
- **Theorem 9.1 (`lcw:thm:ratio`)**: the compact proportional extension
  (43)–(44).
- Section 10: three finite counting descriptions (45)–(51) and the
  diagnostics table.

Added by the write (7 October 2026), marked `[write]`:

- **Remark 1.1 (`lcw:rem:oeis`)**: the OEIS entries quoted and the b-file
  compared (next section).
- **Remark 8.2 (`lcw:rem:transseries`)**: the inversions against the
  transseries volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`),
  statement by statement. (a) **Instance**: `ν(X)` is the staircase `N_*` of
  `p0:def:three-inverses`, and `ν = min_ε ν_ε` is `p0:thm:staircase`(4) with
  `r = 2` (`p0:rem:parity-instances`). (b) The parity brackets of Theorem 8.1
  are, **as stated and proved, an analogue** of `p0:thm:staircase`(2) inside
  each class; the write adds a **second route** through part (4) with class
  interpolations; the width-one statement is the source's own. (c)
  **Instance**: the closed form (42) is `p0:prop:factorial-core` with
  `κ = 1`, `d_vol = log d`; its large-`Y` expansion a **formal**
  `plt:thm:lw-template` instance `(1, 1, 0, log(1 + t log d))` in the chart
  `Z_vol = log t`. (d) **Formal instance after `t = t_{ε,0}(1+E)`**: the
  carriers for `M ≥ 1` are `p0:thm:core-reversion` with `Λ_vol = 1 + 1/L`.
  (e) The full carrier equation for `M ≥ 1` is **not shown to be an
  instance** of `plt:thm:lw-template` ((H3) fails in the chart of (c)); not
  claimed to be outside every chart.
- **Remark 9.2 (`lcw:rem:rows`)**: a proof of the A328718 row conjecture
  (section after next).
- Section 1.1 (`lcw:sec:provenance`: provenance, the sources as the write
  read them, what was checked, relation to the repository, collected
  non-claims, reading conventions); notes after the abstract, at the end of
  Section 3 (three rounded constants), in Section 10 (the diagnostics
  rechecked, the shipped layout), at the end of Section 11 and at the end of
  Section 12.

## The OEIS entries (Remark 1.1)

Read on 7 October 2026 in the internal format; quoted verbatim.

- **A328716** (revision #38, 27 October 2019), offset 0, by Seiichi Manyama:
  "Constant term in the expansion of (1 + x_1 + x_2 + ... + x_n + 1/x_1 +
  1/x_2 + ... + 1/x_n)^n."; Heinz's walk comment; "a(n) = n! * [x^n] exp(x) *
  BesselI(0,2*x)^n. - _Ilya Gutkovskiy_, Oct 26 2019"; "a(n) ~ c * d^n * n^n,
  where d = 0.8047104059195202206625458331930618795... and c =
  2.12946224998808159475495497... if n is even and c =
  1.4189559976544232606562785... if n is odd. - _Vaclav Kotesovec_, Oct 27
  2019"; b-file `n = 0..398` (Manyama; terms 0–199 from Heinz).
- **A328718** (revision #35, 30 October 2019), the array `T(n,k)` (dimension
  `n`, `k` steps): "Conjecture: Row r is asymptotic to (2*r+1)^(n + r/2) /
  (2^r * (Pi*n)^(r/2)). - _Vaclav Kotesovec_, Oct 27 2019", and column
  polynomials.

Kotěšovec's `d` and both `c` agree to every printed digit with the article's
`d`, `C_+`, `C_−` (his decimals are truncations); Theorem 4.1 at `M = 0`
proves his equivalent, for which the entry gives no proof. The write compared
all 399 b-file terms with the exact integer convolution of Section 10, and 44
of them with a direct rational power of `F`: all agree; `a_n` is strictly
increasing from `n = 1`, `a_0 = a_1`. Nothing was submitted to the OEIS.

## The rows of A328718 (Remark 9.2)

For fixed dimension `D`, `A_{N,D}(1) ~ (2D+1)^{N+D/2}/(2^D (πN)^{D/2})` as
`N → ∞`: Kotěšovec's conjecture in A328718 is true. The write proves it as
the local central limit theorem for the lazy walk: Fourier inversion with
`φ(θ) = (1 + 2Σcos θ_i)/(2D+1)`, which equals `1` only at `θ = 0` and never
`−1`, and Laplace's method at `θ = 0`. Exact counts give
`N(ratio − 1) = −0.1875, −0.3747, −0.5614` at `N = 400` for `D = 1, 2, 3`.
Row 1 is A002426 (central trinomial coefficients). The argument is classical,
no novelty is claimed, and it is a fixed-dimension statement: Theorem 9.1's
compact-ratio regime excludes fixed `D`, and the source's "not an unresolved
problem being solved by this proportional-dimensional argument" stays
accurate. (Added after the independent check of 7 October 2026: the proof
re-derived and correct; the `1/N` term is `−3D/16`, from the quartic term of
`log φ` averaged against the Gaussian, and Richardson extrapolation of the
exact counts from `N = 200, 400` gives `−0.1875002, −0.375001, −0.562508`.
Numerical corroboration of the standard Edgeworth term, not a proved
second-order theorem.)

## What is not claimed

From the source, kept in the article (collected in Section 1.1):

- The exact formula and numerical leading equivalent are in the OEIS; the
  Bessel walk generating function and the large-powers machinery are
  classical; no open-problem resolution and no historical priority ("bounded
  evidence, not an absence certificate"); priority for the individual
  probability refinements "remains unestablished".
- Poincaré expansions at fixed order only: no convergence, no growing order,
  no computable constants or onsets, no certified finite-input inverse
  calculator.
- The weighted expansion is signed; the occupation limits are weak limits,
  not total-variation convergence to a Gaussian.
- Nothing treats `ρ → 0`, `ρ → ∞` or fixed `D`; diagnostics are not
  interval-certified; no OEIS record or external repository edited.

The write adds: its checks are floating or finite; Remark 9.2 proves a
classical fixed-dimension statement with no novelty claimed; Remark 8.2
claims no novelty for any inversion.

## Further questions

Section 12 of the article (`lcw:sec:further`) keeps the source's four
questions (effective constants and a certified inverse; sparse and dense
ratios `N/D → 0, ∞`; a lattice local theorem or joint Edgeworth expansion for
the occupancy; comparison with conditional-occupancy and Bessel-distribution
literature). A dated note (Vladimir's standing rule of 4 October 2026)
records that no unproved claim of the source lies outside them and none is
wrong, and that Remark 9.2 settles, for its leading term, the extreme case of
question 2 in which `D` stays fixed; `N/D → ∞` with `D → ∞`, and `N/D → 0`,
stay open. **Nothing in the source was found to be wrong.** Recorded with a
dated note: the printed `r`, `b` and `p` are rounded, not truncated, in their
last digit (truncations `r = 0.804139735863439633472418654…`,
`b = 1.586562859178089847374174938…`, `p = 0.431494883273705551403382959…`).
(Scope clarified after the independent check of 7 October 2026: the note's
"every printed digit except these three is a truncation" concerns the seven
values printed with "…"; the six table entries of Section 5 and the two mean
offsets of Theorem 7.1, printed without it, are correctly rounded, five of
them not truncations.)

## Checks made at intake

- At placement (batch-109 dossier, 6 October 2026; Windows 11): the staged
  files byte-identical to a fresh extraction; `SHA256SUMS.json` 25/25; the
  pin `83befe707` exists. The dossier read the manuscript and found no error;
  with its own exact polynomial power at `n = 120, 121` it reproduced `r`,
  `d`, `C_±` and residuals consistent with `c_{ε,1}`, `c_{ε,2}`; it checked
  the audit's statements about the repository (the A039831, A047909, A108242
  reports and Report 169's packed matrices exist as described); and it reran
  the programs on copies: `code/verify.py` passing (summary equal to
  `generated/verification.json` as JSON), `regenerate.py --compare` and both
  optional `--compare` checks exiting 0, `guard_tests.py` failing on Windows
  (text regenerated with CRLF).
- At the write (7 October 2026; same machine; Python 3.14.4, mpmath 1.3.0):
  every proof line by line (the list is in Section 1.1), with no mathematical
  error found; with its own code, the constants at 60 digits (three rounded
  last digits, above; `d`, `C_±`, `τ²` truncations), `c_{ε,1..3}` against
  the table of Section 5, the diagnostics table of Section 10.3 to every
  printed digit, `E K_n − np = −0.07093, −0.31307, −0.07109, −0.31237` at
  `n = 60, 61, 120, 121` (offsets `−0.071243`, `−0.311664`), the b-file, the
  row conjecture. The programs rerun from the shipped files (Route B below):
  `code/verify.py` passing with the delivered and with the written
  `article.tex` (the verified-prefix block is unchanged), its summary equal to
  `data/generated-verification.json` as JSON; `regenerate.py --compare` and
  both optional `--compare` checks exit 0; `guard_tests.py` fails on Windows
  as at intake.
- Sources read by the write: the OEIS entries and the A328716 b-file; the
  transseries volume. Not read: Gessel–Weinstein–Wilf, Flajolet–Sedgewick.

## Independent check of the write (7 October 2026)

An adversarial check made by the intake after the write (`f3fb85cb6`), with
its own code, after fetching again A328716 (#38), A328718 (#35), A002426 and
the A328716 b-file.

- **Remark 9.2, checked hardest**: the reduction to `P(S_N = 0)`, the
  Fourier inversion, `φ = 1` only at `0`, `φ > −1` (`1 + 2Σcos θ_i ≥ 1 − 2D`),
  the local bound and the Gaussian integral re-derived; the conjecture's row
  index is the dimension. Exact counts at `N = 400` by Miller's power
  recurrence for `F^D` (a route distinct from the source's two) give the three
  printed values; row 1 = A002426 on all its data terms. **Strengthened**:
  the `1/N` coefficient is `−3D/16` (dated note above).
- **Remark 1.1**: quotations, revisions and dates confirmed; all 399 b-file
  terms agree with Miller's recurrence modulo two primes, 45 of them exactly;
  Kotěšovec's `d` and both `c` are truncations.
- **Constants note (Section 3)**: at 70 digits `r`, `b`, `p` end in rounded
  digits with the stated truncations and next digits; `d`, `C_±`, `τ²` are
  truncations. **Scope clarified** (dated note; see above).
- **Section 10 notes**: every diagnostics-table entry reproduced;
  `E K_n − np = n(1 − A_{n,n−1}(1)/a_n) − np = −0.070931, −0.313069,
  −0.071086, −0.312368` at `n = 60, 61, 120, 121`, as stated.
- **Remark 8.2**: (a)–(e) re-derived against the volume (staircase (4) with
  `p0:rem:parity-instances`, `p0:prop:factorial-core` with `κ = 1`,
  `d_vol = log d`, the template chart, the core-reversion form).
- Provenance, the pin `83befe707`, the neighbouring reports named, and the 72
  delivered label numbers and 65 references confirmed. Apart from the scope
  of one sentence, **no defect was found in the write.**

The check is recorded at the end of Section 12.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic that Remark
8.2(a)–(b) applies is formalized generically in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`
(`Fabius.staircase_ceil`, and the residue-class identity of part (4) as
`Fabius.isLeast_residue_class`); nothing about these sequences is.

**The transseries volume.** Remark 8.2: the threshold and its parity
decomposition instances of `p0:thm:staircase`(1) and (4); the parity
brackets analogues of (2) as proved and consequences of (4) with the write's
interpolations; the closed form a `p0:prop:factorial-core` instance, its
expansion a formal `plt:thm:lw-template` instance; the higher carriers formal
`p0:thm:core-reversion` instances; the full carrier equation not shown to be
a template instance.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
the source's audit read the A039831 report (`a039831-two-fourier-peaks`) and
set aside A047909, A108242 and Report 169 as covered
(`a047909-beta-renewal-subsequences`, `a108242-regular-cyclic-word-covers`,
Part IV of `a261781-matrix-compositions`). None shares a result with this
report, so no reciprocal note is proposed.

**Stale claims.** Before batch 109 no file of the repository named A328716
or A328718; the audit's bounded comparison at `83befe707` found no A328716
treatment, which was true.

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: `H(v,t)`, `H(s)`, `H_ℓ(j)`; `h`, `h(w)`;
`R`, `R'`, `R_2(n)`, `R_{k,m}`; `q`, `Q_{D,k}`, `Q_{ε,ℓ}`; `K_n`, `K`; `D`,
`𝒟`; `ρ`, `r`, `r_ρ`, `r(w)`; `𝒯_ℓ`, `T(n,k)`; `d`, `d_TV`; `E_ε`,
`E_{ε,u}`, `𝔼`; `v_ε`, `v`; `s_j`, `s`; `ℓ`, `ℓ_{ε,j}`; `A`, `A_n(u)`,
`A_M`; `F`, `𝓕_{ε,M}`; `X`, `X_r`, `x`, `x(s)`; `I`, `I_0`, `I_1`; `κ_h`,
`Λ`, `L_M`. No symbol was renamed; the volume's colliding letters carry the
subscript "vol" in Remark 8.2.

## Labels

Every label carries the prefix `lcw:` (none existed in the repository). The
manuscript's 72 labels (`eq:` 51, `sec:` 13, `thm:` 5, `prop:` 1, `lem:` 1,
`rem:` 1) were prefixed before anything cited them, and the 65 references to
them (52 `\eqref`, 13 `\ref`) updated. The write added 4: `lcw:rem:oeis`,
`lcw:sec:provenance`, `lcw:rem:transseries`, `lcw:rem:rows`. The report has
76 labels; builds of the delivered text and of this one give all 72
delivered labels the same numbers (aux files compared; the article numbers
equations consecutively, so the write added no numbered display). The added
statements are the last of their sections, the added subsection follows the
last delivered text of Section 1, and nothing was inserted before a
delivered display, table or statement.

## Files

```text
README.md                              this guide (replaces the delivery README)
article.tex                            the report (delivered Report179.tex; labels prefixed, [write] additions)
article.pdf                            compiled report, 22 pages
README_CODE.md                         the programs' documentation (delivered at the root)
SOURCE_AUDIT.md                        the source's attribution and overlap audit (delivered at the root)
optional-README.md                     the optional checks' documentation (delivered optional/README.md)
code/exact.py                          exact counting and coefficient algebra (delivered code/)
code/verify.py                         core verifier; reads the manuscript's prefix block (delivered code/)
code/regenerate.py                     regenerates or compares data/certificates.json (delivered code/)
code/guard_tests.py                    corruption and guard tests; fail on Windows (delivered at the root)
code/test_build.py                     build rejection tests (delivered at the root)
code/verify_manifest.py                release-inventory check (delivered at the root)
code/build.py                          isolated PDF and ZIP builder, TeX (delivered at the root)
code/optional-check_walks.py           SymPy/mpmath walk checks (delivered optional/)
code/optional-independent_check.py     SymPy/mpmath independent checks (delivered optional/)
code/optional-utility.py               shared helper of the optional checks (delivered optional/)
data/certificates.json                 exact certificates (delivered data/)
data/walk_checks.json                  recorded optional output (delivered data/)
data/independent_checks.json           recorded optional output (delivered data/)
data/PROVENANCE.json                   hashes and regenerators of the two records (delivered data/)
data/optional-requirements.txt         sympy==1.14.0, mpmath==1.3.0 (delivered optional/)
data/generated-verification.json       verifier summary (delivered generated/)
data/generated-verification_guards.json  guard-test summary (delivered generated/)
data/generated-build_guards.json       build-test summary (delivered generated/)
data/generated-BUILD_INFO.json         build receipt (delivered generated/)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit (next section):
`Report179.pdf` (the delivered 16-page PDF, 402,088 bytes);
`SHA256SUMS.json` (2,333 bytes, 25 entries, verified at placement;
repository policy ships no checksum manifests); and the delivery `README.md`
(5,031 bytes), staged at placement and replaced by this guide (summarized
below).

**Delivered text that names the delivery layout or files not shipped.**
`code/verify.py` reads `Report179.tex` and `data/` from the package root (its
`--manuscript` and `--data` options override them); `code/build.py`,
`code/test_build.py` and `code/verify_manifest.py` expect `Report179.tex`,
`README.md`, `build.py`, `guard_tests.py`, `optional/`, `generated/` and
`SHA256SUMS.json` at the root; `code/guard_tests.py` and the optional scripts
use the delivered names; `optional-README.md` and `README_CODE.md` give
commands for the delivered layout; `data/PROVENANCE.json` names
`optional/check_walks.py` and `optional/independent_check.py` as
regenerators; Section 10.4 of the article describes the delivered ZIP. So
no program runs under the shipped names; use one of the routes below.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Lazy_Closed_Walks_Asymptotics_and_Inverses_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # e433f40b68bae06759f38828c5acff277112cd034a6dd978654fe5473b44f613, 617,713 bytes
cd "$T" && unzip -q a.zip
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later; the core uses only the standard library, the optional
checks SymPy 1.14.0 and mpmath 1.3.0. Never run anything in the repository.

**Route A, delivered layout**, from `$T`:

```sh
python -S -B code/verify.py
python -S -B -O code/verify.py
python -S -B code/regenerate.py --compare data/certificates.json
python -B optional/check_walks.py --compare
python -B optional/independent_check.py --compare
python -S -B guard_tests.py        # POSIX (compares LF output)
python -S -B test_build.py         # POSIX
python -S -B build.py --output ../rebuild-one   # TeX, POSIX
```

**Route B, from the shipped files** (tested at the write on Windows):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a328716-lazy-closed-walks
B=$(mktemp -d); mkdir -p "$B/code" "$B/data" "$B/generated" "$B/optional"; cd "$B"
cp "$R"/code/exact.py "$R"/code/regenerate.py "$R"/code/verify.py code/
cp "$R"/code/build.py "$R"/code/guard_tests.py "$R"/code/test_build.py "$R"/code/verify_manifest.py .
cp "$R"/data/PROVENANCE.json "$R"/data/certificates.json "$R"/data/independent_checks.json "$R"/data/walk_checks.json data/
for f in "$R"/data/generated-*; do n=$(basename "$f"); cp "$f" "generated/${n#generated-}"; done
for f in check_walks independent_check utility; do cp "$R/code/optional-$f.py" "optional/$f.py"; done
cp "$R/optional-README.md" optional/README.md; cp "$R/data/optional-requirements.txt" optional/requirements.txt
cp "$R/README_CODE.md" "$R/SOURCE_AUDIT.md" .; cp "$R/article.tex" Report179.tex
```

then the commands of Route A. At the write, in this layout, `code/verify.py`
passed (its JSON summary equal to `generated/verification.json`), with the
written `article.tex` as `Report179.tex` too; `regenerate.py --compare` and
both optional checks exited 0 (a few seconds each); `guard_tests.py` failed
on Windows ("regenerated bytes differ": CRLF). The manifest check and the
build need the delivered `README.md` and `SHA256SUMS.json` (Route A). Use
`py` where `python` is not on the path.

## Build the PDF

pdfLaTeX (fontenc, lmodern, microtype, amsmath, amssymb, amsthm, mathtools,
booktabs, array, geometry, xcolor, hyperref, enumitem, fancyhdr); the
bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 7 October 2026, and
rebuilt after the independent check of the same day (label numbers
unchanged, aux files compared): 22 pages; no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes (the delivered text also builds without any, 16 pages). The
delivered byte-identity claims (fixed source date, suppressed PDF metadata)
apply to `Report179.tex` under the delivering toolchain, not to this build.

## From the delivery README

The delivery README (replaced by this guide) said that the package contains
"the PDF, editable LaTeX source, exact standard-library verification,
optional SymPy/mpmath diagnostics, and an offline deterministic builder" and
that "No open problem resolution, worldwide priority, or certified
finite-input inverse calculator is claimed"; listed the mathematical content
(as above); said that "Constants and onsets are non-effective here" and
that no convergence, extreme-ratio uniformity, fixed-dimensional
implication or Gaussian total-variation limit is asserted; gave the quick
verification commands (the manifest check "applies to the complete release
ZIP"), the rebuild procedure and its isolation and determinism; and
summarized the evidence: 52 exact count cases including `n = 0..41` and
selected sizes through `n = 201`, joint zero-step/occupation counts, and
optional programs whose "residual stabilization is supporting evidence, not
a proof of the analytic remainders or an effective starting threshold".

## Rights

Repository contents are MIT-0. The article and this README quote OEIS
entries A328716 and A328718; OEIS content is published by The OEIS
Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and that
content remains under that licence. Short quotations of the cited works are
for attribution. No third-party PDF is shipped. Nothing was submitted to the
OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A328716 (entry and official source
  record) and A328718; Gessel–Weinstein–Wilf, Electron. J. Combin. 5 (1998),
  R2; Flajolet–Sedgewick, *Analytic Combinatorics* (2009), Theorem VIII.8.
- Batch 109 of `docs/incoming`, bundle Report 179; arrival `60f54ea06`,
  placement `f7e9e5c2f`, written 7 October 2026. Single source, so no merge
  choices. The delivered `Report179.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
