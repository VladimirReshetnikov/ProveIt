# Partitions into Odious and Evil Parts (OEIS A067590, A067591, A116492, A116491)

**Kotěšovec's two conjectures of July 2025 proved; every fixed order of
expansion, every fixed multiplicity cap and a Bessel comparison with error
smaller than every power; the odious-to-evil ratio `m + 1` for cap `m`;
Lambert-`W` inverses and rounding-aware thresholds**

A research article ("Research Report 165" of a session bundle), built from
one manuscript dated 3 October 2026. Its author line reads "Research Report
165" and its PDF author field is empty: it names no person, tool or
addressee. The package carries no "prepared for private review" line, no
e-mail address and no personal data; it names Vladimir Reshetnikov only as
the author of the ProveIt Thue–Morse atlas it cites.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 165 (batch 107) | `Odious_and_Evil_Partitions_All_Orders_and_Inverses_Source.zip` (21 files at the archive root, no wrapper directory, 669,797 bytes, SHA-256 `a0a70cc3…14b91ca`), arrival commit `60f54ea06`; main file `Report165.tex` (574 lines, 15 pp.) | ProveIt `5dacd76e2` (3 October 2026: the three archived Thue–Morse atlas files, blobs `c927e43a`, `7fee5be7`, `66c8012a`, unchanged at the write) | `3988bf5c4` (batch 107) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report (see "Relation to the
repository" for what the neighbouring Lean development does formalize).
Every theorem has a conventional proof; no proof uses a computation or a
decimal.

## Trust boundaries

- **What is proved by hand.** Theorems 1.1 and 1.2 (all fixed orders, all
  fixed caps, the flat Bessel comparisons and the ratio `m + 1`), Theorem 6.1
  (inverse expansions) and Proposition 6.2 (eventual increase and the
  two-ceiling threshold enclosure), from the Euler products, by a sectorial
  Mellin argument (Section 2), the Dedekind eta transformation (Section 3),
  uniform Fourier bounds on every arc (Section 4) and a completed Hankel
  contour (Section 5).
- **What is prior work.** The entire continuation of `D(s) = Σ_{k≥1} ε(k)
  k^{−s}` (Allouche–Cohen 1985, re-proved here in the form needed), and
  `d = D′(0) = −log Q`, `Q = e^γ/(√2 φ)` with `φ` the Flajolet–Martin
  constant (Allouche 2019/2021, used only to rewrite constants). The eta
  transformation, Hankel's integral, the Bessel series and expansions, and
  Lambert `W` are classical (DLMF).
- **What is numerical only.** `d ≈ −0.4874506225215474`,
  `Q ≈ 1.6281601297189172`, `K₋ ≈ 0.2218648339570363`,
  `K₊ ≈ 0.1235806870073263` are uncertified. The intake's independent
  recomputation agrees (below).
- **The companion** checks finite coefficient identities through `n = 512`,
  the four OEIS prefixes, the Bessel coefficient algebra and the formal
  inverse through order 6, and exact first thresholds; it proves nothing
  asymptotic.

## What it proves

`ε(k) = (−1)^{s₂(k)}`; `E₋` (odious) and `E₊` (evil) are the positive
integers with `ε(k) = −1`, `+1` (zero is never a part); `p_σ(n)` counts
partitions of `n` with parts in `E_σ`, and `p_{σ,m}(n)` those in which each
part occurs at most `m` times. `A = π²/12`, `β_σ = 1/4 + σ/2`. Statement
numbers are the delivered ones.

- **Theorem 1.1 (`oep:thm:unrestricted`)**: with `N = n − 1/48`,
  `p_σ(n) = K_σ N^{−β_σ/2−3/4} e^{2√(AN)}(Σ_{j<J} B_j N^{−j/2} + O(N^{−J/2}))`
  for every `J`, and `p_σ(n) = C_σ (A/N)^{(β_σ+1)/2} I_{−β_σ−1}(2√(AN))
  (1 + O(n^{−R}))` for every `R`. In particular
  `p₋(n) ~ K₋ n^{−5/8} e^{π√(n/3)}` and `p₊(n) ~ K₊ n^{−9/8} e^{π√(n/3)}`.
- **Theorem 1.2 (`oep:thm:capped`)**: for each fixed cap `m`, with
  `a_m = Am/(m+1)` and `N = n + m/48`, the same two forms with `β = 0` and
  constant `(m+1)^{−β_σ}`; hence `p_{−,m}(n)/p_{+,m}(n) = m + 1 + O(n^{−R})`
  for every `R`. At `m = 1`: `p_{−,1}(n) ~ n^{−3/4} e^{π√(n/6)}/(2·12^{1/4})`
  and `p_{+,1}(n) ~ n^{−3/4} e^{π√(n/6)}/(4·12^{1/4})`.
- **Section 2**: flatness of `S(w) = Π_j (1 − e^{−2^j w})` with all
  derivatives in closed acute sectors (Lemma 2.1), vertical decay
  (Lemma 2.2), `D(0) = −1`, `D(−k) = 0`, and `H(w) = log w + d + O(|w|^L)`.
- **Theorem 6.1 (`oep:thm:inverse`)**: the inverse of the smooth Bessel model
  to every fixed order, `v = √(x + λ) = v₀ + Σ c_j v₀^{−j}` with
  `v₀ = −(2p/b) W₋₁(−(b/2p)(K/y)^{1/(2p)})` and a triangular recursion for
  `c_j`; the constant terms `1/48 + 15/(16π²)`, `1/48 + 135/(16π²)`,
  `−m/48 + 3/(16a_m)`.
- **Proposition 6.2 (`oep:prop:threshold`)**: every sequence is eventually
  strictly increasing, and `⌈X_J − C(log y)^{−q}⌉ ≤ T(y) ≤ ⌈X_J +
  C(log y)^{−q}⌉` for the first threshold `T(y)`.

Added by the write (6 October 2026), with proofs, marked `[write]`:

- **Remark 1.3 (`oep:rem:kotesovec`)**: the two conjectures, quoted (next
  section).
- **Remark 2.3 (`oep:rem:atlas`)**: the relation to the Thue–Morse atlas.
  (a) The real-axis case of Lemma 2.1 is the atlas's
  `p1:thm:boundary-flatness`; the atlas continues only the *shifted* series
  `D(s,a) = Σ_{n≥0} ε_n (n+a)^{−s}`, `a > 0`, with `D(0,a) = 0`, whereas the
  unshifted `D` here has `D(0) = −1`. (b) A bridge, proved: `D(s, 1/2) =
  (1 − 2^s) D(s)` on all of ℂ; hence `∂_s D(s,1/2)|₀ = log 2`,
  `∂²_s D(s,1/2)|₀ = log²2 − 2d log 2`, and `D(2πik/log 2, 1/2) = 0` for every
  integer `k`. (c) A second route to `D(0) = −1` and `D(−k) = 0` from the
  atlas's dyadic equation (`p1:thm:Dirichlet-dyadic`), derivative bridge
  (`p1:cor:G-Dirichlet`), Woods–Robbins product (`p1:thm:Woods-Robbins`) and
  trivial zeros, each formal in Lean, plus (b); it does not reach `d`.
  (d) Exactly what is formal (next-but-one section).
- **Remark 6.3 (`oep:rem:transseries`)**: Section 6 against the transseries
  volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`).
  (a) The core `v₀` is an **instance** of `p0:thm:lambert-core` after the
  change of variable `v = √(x + λ)`, with `(a, b) := (b, −2p)` (negative
  logarithmic coefficient, lower branch by the branch rule). (b) The
  recursion for `c_j` is an **instance** of `p0:thm:lambert-centered`(2)–(4)
  with `(a, b, Q) := (b, −2p, Σ ℓ_j t^j)`, equivalently of
  `p0:thm:core-reversion` with `Λ = b`, `h = 0`. (c) The analytic expansion
  (56) is an **instance** of `p0:thm:lambert-centered`(5) for
  `𝒢(v) = 𝓜(v² − λ)` with model data `(K, b, 1, −2p, 1, Σ ℓ_j t^j)`; the
  derivative hypothesis `(log 𝒢)′(v) = b − 2p/v + O(v^{−2})` is proved there
  from `(log 𝒢)′ = 2√a I_{ν−1}(z)/I_ν(z)`. (d) Proposition 6.2 is **not an
  instance as proved, only an analogue** of `p0:thm:staircase`(1)–(2): its
  comparison function `𝓜` does not interpolate the sequence. No novelty is
  claimed for the inversion.
- **Section 10 (`oep:sec:further`)**: further questions, with a proof that
  the ratio law is not uniform in `1 ≤ m ≤ n`.
- Section 1.1 (provenance, the sources as the write read them, what was
  checked, relation to the repository, collected non-claims, reading
  conventions), notes at the ends of Sections 7 and 8, and a note in the
  atlas bibliography entry.

## Kotěšovec's conjectures

The live OEIS entries (read 6 October 2026) are at the revisions the source
inspected: A067590 #17 and A116492 #18, both of July 6, 2025. A067590,
"Number of partitions of n into odious numbers (A000069).", has the line

    Conjecture: a(n) ~ c * exp(Pi*sqrt(n/3)) / n^(5/8), where c = 0.221864833... - _Vaclav Kotesovec_, Jul 06 2025

and A116492, "Number of partitions of n into distinct odious numbers.", the
line

    Conjecture: a(n) ~ c * exp(Pi*sqrt(n/6)) / n^(3/4), where c = 0.26864248.... - _Vaclav Kotesovec_, Jul 06 2025

(quoted verbatim). Theorems 1.1 and 1.2 prove both equivalents, with
`c = K₋ = (2π)^{−1/4} Q^{1/2} (π²/12)^{1/8}/(2√π)` and
`c = 1/(2·12^{1/4}) = 0.2686424829558855…` respectively. The second decimal
is elementary. The first rests on a floating evaluation of `d`; the intake's
independent mpmath quadrature of `d` gives `K₋ = 0.221864833957`, which
begins with the nine printed digits, but no interval enclosure exists, so
those digits are supported by two concordant computations, not proved. The
evil counterparts A067591 (#6) and A116491 (#14) carry no asymptotic line.
This is recorded only; **nothing was submitted to the OEIS**, and both lines
are still labelled conjectures there.

## What is not claimed

From the source, kept in the article (collected at the end of Section 1.1):

- No uniformity in growing caps; no leading term beyond all algebraic orders
  (`p_{−,m} − (m+1)p_{+,m}` is not claimed polynomially small).
- No interval-certified constant, error constant, onset of monotonicity or
  threshold constant; quadrature gives no enclosure of `d`; a bare ceiling of
  an asymptotic inverse is not a threshold.
- No historical priority; a bounded literature search (Merca read at
  abstract level; the Allouche–Cohen and Flajolet–Martin originals not
  obtained; Golafshan–Rigo treat a different object), whose negative result
  is "not an exhaustive literature exclusion, a repository-wide originality
  certificate, or a historical-first claim".
- Finite checks and byte-identical rebuilds prove nothing asymptotic;
  cross-version TeX byte identity is not promised.

The write adds: the residual values of Question 2 are floating-point
observations and determine no rate.

## Further questions

Section 10 of the article (`oep:sec:further`) states every unproved claim as
an open question with its source, sketch and what is missing (Vladimir's
standing rule of 4 October 2026). **Nothing in the source was found to be
wrong.**

1. **Growing caps** (`oep:q:caps`). *Proved at the write:* the ratio law is
   not uniform in `1 ≤ m ≤ n`, since `p_{σ,n}(n) = p_σ(n)` and
   `p₋(n)/((n+1)p₊(n)) ~ (K₋/K₊) n^{−1/2} → 0`, `K₋/K₊ = √12 Q/π ≈ 1.795`.
   Heuristically the transition is at `m ≍ √n`. Open: the range of `m(n)`
   with ratio `~ m + 1`, and the transition law.
2. **Residuals beyond all orders** (`oep:q:residual`). Intake observations:
   `p_σ(n)/𝓜(n) − 1 = 3.33·10⁻⁸, 8.49·10⁻¹⁰` (odious) and `−4.40·10⁻⁸,
   −7.77·10⁻¹⁰` (evil) at `n = 1000, 3000`; the cap ratio minus `m + 1` at
   `n = 500, 1000, 1500` is `−5.6·10⁻⁵, −1.6·10⁻⁶, −2.8·10⁻⁷` (`m = 1`) and
   `+5.6·10⁻⁵, +9.8·10⁻⁷, −2.4·10⁻⁶` (`m = 2`, not of one sign). Sketch:
   `S(w + πi) = (1 + e^{−w}) S(2w)` is again flat, so the arc at `q = −1`
   looks amenable to the same Mellin method.
3. **Effective constants and onsets** (`oep:q:effective`), which would also
   certify the digits of Kotěšovec's first decimal.
4. **The literature boundary** (`oep:q:literature`): Merca, Allouche–Cohen.

## Checks made at intake

- At placement (batch-107 dossier, 5–6 October 2026; Windows, Python
  3.14.4): the 16 staged files other than `README.md` and `article.tex` are
  byte-identical to the archive, and so were the staged `Report165.tex` and
  README; `SHA256SUMS` 20/20 and `companion/reference_run/SHA256SUMS` 2/2. An
  in-process replay of the companion (normal and `-O`) reproduced
  `exact_results.json` and `numerical_illustrations.json` byte for byte. The
  dossier read the manuscript in full and found no error; it checked by hand
  the pair bound `16/(3√3)`, the first corrections, the inverse constants and
  the ratio `r`; with its own code it found `d = −0.487450622521547` by the
  quadrature (25), `K₋ = 0.221864833957`, `K₊ = 0.123580687007`, the
  relative Bessel residuals and cap ratios quoted above, and the four
  thresholds `T(100000) = 76, 110, 170, 186`.
- At the write (6 October 2026; same machine): the live data of the four
  entries (54, 63, 69, 74 terms) agree with counts recomputed from the
  definitions; the bridge value `∫₀^∞ e^{−t/2} S(t) dt/t = log 2` to 20
  digits and the second-derivative relation to 16 digits (mpmath,
  uncertified); route B below: the 9 mathematical tests pass (25 s), the 7
  output-safety tests fail (they need POSIX directory descriptors and file
  ownership), and the in-process replay is byte-identical. The archived atlas
  blobs were compared at `5dacd76e2` and at the write's HEAD (identical), and
  their cited line ranges spot-checked.
- Sources read by the write: the four OEIS entries; the current atlas
  (statements listed in Section 1.1) and the Lean modules named below
  (statements only; nothing was built); the transseries volume
  (`p0:def:core`, `p0:def:model`, `p0:thm:lambert-core`,
  `p0:thm:lambert-centered`, `p0:thm:core-reversion`,
  `p0:thm:backward-error`, `p0:def:three-inverses`, `p0:thm:staircase`).
  Not read by the write: Allouche 2019 and 2015, Tóth, Golafshan–Rigo,
  Merca, Allouche–Cohen, Flajolet–Martin, DLMF (what the source read is
  fingerprinted in `data/SOURCE_PROVENANCE.json`).

## Relation to the repository

**Formal status.** No statement of this report is formalized. The
neighbouring Lean development
(`Analysis/FabiusFunction/Lean/FabiusFunction/`) formalizes, for the atlas:
the effective real-axis flatness bounds of `𝓔(t) = S(t)`
(`Fabius.lacunaryExpProduct_le`, `Fabius.le_lacunaryExpProduct`,
`ThueMorseBoundaryFlatness.lean`); the entire continuation of the *shifted*
series `D(s,a)`, `a > 0` (`Fabius.dirichletMellinContinuation`,
`Fabius.dirichletMellinContinuation_differentiable`,
`Fabius.dirichletMellinContinuation_eq` for real `s > 1`); its zeros at
`s = −r` in the form `Fabius.tendsto_dirichletMellinContinuation_neg_natCast`
(the evaluations `Fabius.dirichletMellinContinuation_neg_natCast` and
`_zero` hold by Mathlib's conventions `Γ(−r) = 0`, `0⁻¹ = 0` alone, as their
docstrings warn); the dyadic equation at every complex `s`
(`Fabius.dirichletMellinContinuation_dyadic`); the derivative bridge
(`Fabius.mpLimit_eq_deriv_sub`, `ThueMorseGDirichlet.lean`); the
Woods–Robbins value (`Fabius.woods_robbins`, `Fabius.mpLimit_one_half_one`);
and the evil and odious enumerators (`Fabius.evilEnum`, `Fabius.odiousEnum`).
**Not formal:** the sector and derivative forms of flatness, the unshifted
`D(s)`, its values and `d`, the evaluation `d = −log Q`, the bridge of
Remark 2.3, the combination in Remark 2.3(c) (which nobody has written in
Lean), and everything in Sections 3–6. Placement in the collection, or
beside the Fabius development, confers no formal status.

**The Thue–Morse atlas.** The source checked three archived atlas files at
`5dacd76e2`
(`Analysis/FabiusFunction/docs/archive/research-frontiers/Thue_Morse_Formula_Atlas-{1,2,3}/`);
their blobs are unchanged at the write. The current consolidated volume is
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/thue-morse/Thue_Morse_Atlas_and_Frontiers/`,
whose overlapping statements are `p1:thm:boundary-flatness`,
`p1:thm:Mellin-integral`, `p1:cor:Dirichlet-trivial-zeros`,
`p1:thm:Dirichlet-dyadic`, `p1:cor:G-Dirichlet`, `p1:thm:Woods-Robbins` and
`p1:thm:evil-odious`. The overlap is one of method and inputs: the atlas
poses no question about partition counts with Thue–Morse-restricted parts,
so this report does not continue it ("Thue–Morse partition" elsewhere in
the Fabius tree means the Prouhet set partition, a different notion).

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a174065-radix-layer-partitions` (parts with digit structure, a
log-periodic factor); `a022629-distinct-partition-norms` and
`a097356-sqrt-restricted-partitions` (Meinardus/Bessel-type transfers for
restricted partitions); `a301981-unitary-divisor-partitions` (an arithmetic
weight in an Euler product). None treats these sequences, and none needs a
reciprocal note.

**Stale claims.** Before batch 107 no file of the repository named the four
sequences or partitions into odious or evil parts, as the source's bounded
search found. Its atlas citations are accurate; the write adds the current
volume's labels (note at the end of Section 7 and the bibliography entry).

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings, especially against the atlas: `σ` (a sign,
not `Re s`); `E_σ` (parts, zero excluded) against the atlas's enumerators
`𝓔_n, 𝓞_n` and its product `𝓔(t)`; `S(w)` (= the atlas's `𝓔(t)` on the
real axis); the unshifted `D(s)`, `d` against the shifted `D(s,a)`; `G(s)`
against the master product `G(a,b)`; `J`; `Q`, `φ`; `θ`, `t`; `N`; `A, a,
a_m`; `B, B_j, b` (and the `b` of `p0:thm:lambert-core`, which is `−2p`
here); `p`; the constants; `r, m`; `L, R, q`; `δ, ℓ`; `𝓜`, `T(y)` (the
staircase `N_*` only on the monotone tail). No symbol was renamed.

## Labels

Every label carries the prefix `oep:` (none existed in the repository). The
manuscript's 78 labels (`eq:` 66, `sec:` 6, `thm:` 3, `lem:` 2, `prop:` 1)
were prefixed before anything cited them, and the 38 references to them
updated. The write added 9: `oep:sec:provenance`, `oep:rem:kotesovec`,
`oep:rem:atlas`, `oep:rem:transseries`, `oep:sec:further`, and the questions
`oep:q:caps`, `oep:q:residual`, `oep:q:effective`, `oep:q:literature`. The
report has 87 labels; builds of the delivered text and of this one give all
78 delivered labels the same numbers (aux files compared). The added remarks
are the last statements of their sections, the added section follows the
last delivered one, and the added displays are unnumbered.

## Files

```text
README.md                                         this guide (replaces the delivery README)
article.tex                                       the report (delivered Report165.tex; labels prefixed, [write] additions)
article.pdf                                       compiled report, 23 pages
companion-README.md                               the companion's README (delivered companion/README.md)
code/companion-companion.py                       exact companion and bounded CLI (delivered companion/companion.py)
code/companion-test_companion.py                  16 unit tests (delivered companion/test_companion.py)
code/build_pdf.py                                 deterministic PDF build (delivered at the root)
code/make_zip.py                                  allowlist-verified source ZIP (delivered at the root)
code/release_tools.py                             descriptor-pinned output helpers (delivered at the root)
code/test_release.py                              tests of the release tools (delivered at the root)
data/RELEASE_RECEIPT.json                         local verification and page-review receipt (delivered at the root)
data/SOURCE_PROVENANCE.json                       sources, inspection scope, SHA-256 and blob ids (delivered at the root)
data/companion-oeis_prefixes.json                 four frozen OEIS prefixes (delivered companion/oeis_prefixes.json)
data/companion-reference_run-COMPLETE.json        completion marker (delivered companion/reference_run/COMPLETE.json)
data/companion-reference_run-exact_results.json   exact results (delivered companion/reference_run/exact_results.json)
data/companion-reference_run-numerical_illustrations.json  uncertified illustrations (delivered companion/reference_run/)
data/companion-test-results-normal.txt            recorded test output (delivered companion/)
data/companion-test-results-optimized.txt         recorded test output under -O (delivered companion/)
data/companion-verification.json                  check summary and reference hashes (delivered companion/)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit (next section):
`Report165.pdf` (the delivered 15-page PDF, 383,119 bytes); `SHA256SUMS`
(1,828 bytes, 20 entries) and `companion/reference_run/SHA256SUMS` (180
bytes, 2 entries), both verified at placement (repository policy ships no
checksum manifests); and the delivery `README.md` (5,207 bytes), staged at
placement and replaced by this guide (summarized below).

**Delivered text that names the delivery layout or files not shipped.**
`companion-README.md` describes `companion/`, `reference_run/` and the
reference `SHA256SUMS`; `companion.py` reads `oeis_prefixes.json` beside
itself, and the tests import it as `companion`, so neither runs under the
shipped names. `build_pdf.py` compiles `Report165.tex`; `make_zip.py` checks
a closed allowlist of delivered names (`Report165.pdf`, `SHA256SUMS`,
`companion/…`); `data/RELEASE_RECEIPT.json`, `data/companion-verification.json`
and `data/SOURCE_PROVENANCE.json` record hashes of delivered names, and
Section 8 of the article speaks of "the source archive". The release tools
also require POSIX (`O_NOFOLLOW`, directory descriptors, `/proc/self/fd`).

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Odious_and_Evil_Partitions_All_Orders_and_Inverses_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # a0a70cc31bafd900d7e5bd395d6a26cbb7a985df6524f6d37d996521414b91ca, 669,797 bytes
mkdir "$T/pkg" && cd "$T/pkg" && unzip -q ../a.zip     # the 21 files are at the archive root
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later, standard library only. Never run anything in the
repository.

**Route A, delivered layout, on a POSIX host** (as the delivery README
gives it; not run by the intake, whose host is Windows):

```sh
cd "$T/pkg/companion"
python3 -B -m unittest -v test_companion          # 16 tests
python3 -B -O -m unittest -v test_companion
python3 -B companion.py --output-parent "$(pwd -P)" --output-name new_run
cmp new_run/exact_results.json reference_run/exact_results.json
```

The parent must be owned by the user and not group- or world-writable; the
output name must be new. The PDF and ZIP rebuilds (`build_pdf.py`,
`make_zip.py`, `test_release.py`, from `$T/pkg`) need pdfTeX and POSIX and
were not run by the intake.

**Route B, from the shipped files, any OS** (tested at the write on Windows):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a067590-odious-evil-partitions
B=$(mktemp -d); mkdir "$B/reference_run"; cd "$B"
cp "$R/code/companion-companion.py" companion.py
cp "$R/code/companion-test_companion.py" test_companion.py
cp "$R/data/companion-oeis_prefixes.json" oeis_prefixes.json
for f in COMPLETE exact_results numerical_illustrations; do
  cp "$R/data/companion-reference_run-$f.json" "reference_run/$f.json"; done
python3 -B -m unittest -v test_companion     # Windows: 9 pass, the 7 OutputSafetyTests fail (POSIX only)
python3 -B -c "import companion as c; from pathlib import Path as P; e=c.exact_results(); \
print(c.json_bytes(e)==P('reference_run/exact_results.json').read_bytes(), \
c.json_bytes(c.numerical_illustrations(e))==P('reference_run/numerical_illustrations.json').read_bytes())"
```

The last command prints `True True` (it rebuilds both payloads in memory,
which the CLI cannot do on Windows because its writer needs POSIX
`O_NOFOLLOW`). Use `py` where `python3` is not on the path.

## Build the PDF

pdfLaTeX (fontenc, lmodern, amsmath, amssymb, amsthm, mathtools, booktabs,
array, geometry, microtype, hyperref, fancyhdr); the bibliography is
embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 6 October 2026: 23
pages; no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes. The delivered source builds the same way to 15 pages, also
without warnings. The article keeps the delivered preamble lines that
suppress PDF dates and trailer identifiers; the delivered byte-identity
claims apply to `Report165.tex` under the delivering toolchain, not to this
build.

## From the delivery README

The delivery README (replaced by this guide) called the package "a local,
self-contained article and exact-check package". It summarized the results
as above; listed the contents; said that "No decimal constant is
interval-certified", that the numerical illustrations "have ordinary binary64
roundoff", that no claim concerns growing caps or the leading
beyond-all-orders correction, and that "Finite inverse formulas must not be
rounded blindly"; gave the companion commands (Route A) and the POSIX
release builds (`build_pdf.py --output-dir`, `make_zip.py --output`, each
refusing existing destinations, "Reproduction was checked twice in the
provided TeX installation"); called the manifest "an integrity/replay aid,
not a cryptographic signature"; and ended "Local preparation involved no
upload, publication, external contact, OEIS edit, repository modification,
or change to earlier reports."

## Rights

Repository contents are MIT-0. The article, the companion's frozen prefixes
and the recorded outputs quote OEIS terms and formula lines of A067590,
A067591, A116492 and A116491; OEIS content is published by The OEIS
Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and those
terms remain under that licence. No third-party PDF is shipped. Nothing was
submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A067590, A067591, A116492, A116491;
  Allouche, Adv. Appl. Math. 126 (2021) (arXiv:1906.10532); Allouche,
  J. Théor. Nombres Bordeaux 27 (2015); Allouche and Cohen, Bull. London
  Math. Soc. 17 (1985); Flajolet and Martin, J. Comput. Syst. Sci. 31 (1985);
  Tóth, Integers 22 (2022); Golafshan and Rigo, DLT 2026; Merca (publisher
  record); DLMF 4.13, 5.9.2, 10.17.1, 10.25.2, 10.40.1, 23.18; this
  repository's archived Thue–Morse atlases, pinned at `5dacd76e2`.
- Batch 107 of `docs/incoming`, bundle Report 165; arrival `60f54ea06`,
  placement `3988bf5c4`, written 6 October 2026. Single source, so no merge
  choices. The delivered `Report165.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
