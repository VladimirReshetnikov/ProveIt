# Modified Entringer Connection Constants and Spectral Limits (OEIS A386381, A386363)

**`d_n = 2 C(1) ρ^{1−n} Γ(n−1)² (1 + Σ_{j<M} (−1)^{j+1} j! L_j(1)/(n−2)^{\underline{j+1}} + O(n^{−M−1}))`
for every fixed `M`, with `ρ = π/2`; the OEIS amplitude `c = 25.5745…` identified
exactly as `π C(1) = π A(π/2)`, `(zA′)′ = (sec z + tan z)A`, `A(0) = A′(0) = 1`, with a
certified enclosure; a marked endpoint `C(λ)` that is the Fredholm determinant of a
positive trace-class Green operator, a limiting infinite-Bernoulli law with
weighted corrections, a large-mark law and a far tail; simple negative limiting
zeros; and two-ceiling inverse brackets**

A research article dated 3 October 2026 ("Report 180" of a session bundle),
built from one manuscript. Its author line and PDF author field read "Research
report 180": it names no person, tool or addressee. The package carries no
"prepared for private review" line, no e-mail address and no personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 180 (batch 110) | `Modified_Entringer_Asymptotics_and_Spectral_Limits_Source.zip` (34 files, no wrapper directory, 789,613 bytes, SHA-256 `23d6b43bbad1…e089a7f571f95f`), arrival commit `60f54ea06`; main file `Report180.tex` (1,018 lines, 22 pp.) | none: the package names no ProveIt commit; `SOURCE_AUDIT.md` names three neighbouring reports, one of them (A125054) by its GitHub path and two by title (corrected after the independent check of 7 October 2026) | `8622ca7e5` (batch 110) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report.

## Trust boundaries

- **What is proved by hand.** Proposition 2.1 (the boustrophedon reduction to
  the ODE, credited to Millar–Sloane–Young and also derived directly),
  Theorem 3.1 (the entire endpoint), Lemma 4.1 (Frobenius pair), Theorem 5.1
  and Corollary 5.2 (all fixed orders, by Δ-domain transfer), Proposition 6.1
  (the Wronskian formula), Theorem 7.1 (the inverse bracket), Theorem 8.1
  (Fredholm determinant), Theorems 9.1, 9.2 (limiting law, weighted
  corrections), Theorem 10.1 with Lemma 10.2 (large mark), Theorem 10.3 and
  Corollary 10.4 (far tail and its inverse), Theorem 11.1 (simple zeros, escape
  of nonreal zeros). No proof uses a computation.
- **What rests on computation.** The certified enclosure (36) of `c` combines
  proved Taylor tails (`δ_420 < 10^{−44}`, checked in exact rationals) with
  90-digit interval arithmetic in mpmath, whose implementation is trusted; the
  displayed correction polynomials, `P_10` and its exact Sturm count are exact
  finite computations of the shipped programs (and were recomputed by the write).
- **What is diagnostic.** Every other decimal (`C(1)` to 55 places, the optical
  length `𝒜 ≈ 4.2586174557`, the residual table of Section 12); remainder
  constants and thresholds are existential.
- **What is prior.** The triangle and its diagonal (OEIS A386363, A386381;
  Kurkov, July 2025), the leading scale and the numerical amplitude
  (Kotěšovec, 2 September 2025), the boustrophedon transform theorem,
  singularity analysis, Fredholm theory and the spectral Bernoulli principle
  (HKPV). The source makes "not a historical priority claim".

## What it proves

`T(n,k)` is the triangle A386363, `d_n = T(n,n)` (A386381), `N = n − 2`,
`E(z) = sec z + tan z`, `ρ = π/2`. Statement and equation numbers are the
delivered ones.

- **Proposition 2.1 (`men:prop:ode`)**: `B = EA`, `(zA′)′ = EA`, `A(0) = A′(0) = 1`,
  `d_{N+2} = (N!)² [z^N] B`; exact Taylor recurrences (7).
- **Theorem 3.1 (`men:thm:endpoint`)**: with the marked array (8) and
  `P_{N+2}(λ)`, `C(λ) = A_λ(ρ)` is entire, `|C(λ)| ≤ e^{|λ| K_0}`,
  `1 < C(1) ≤ e^{π²/3} < 200`; the amplitude is `c = π C(1)` (14).
- **Lemma 4.1 (`men:lem:frobenius`)**, **Theorem 5.1 (`men:thm:transfer`)**:
  every fixed order of `R_N(λ) = ρ^{N+1} P_{N+2}(λ)/(2(N!)²)`, absolute and
  uniform on compact complex mark sets, valid at zeros of `C`; `s_1, …, s_4`
  (27); **Corollary 5.2 (`men:cor:scalar`)**: the scalar expansion and its
  first six inverse-power corrections (29), which prove the OEIS equivalent.
- **Proposition 6.1 (`men:prop:wronskian`)** and the certificate:
  `25.5745196289574675215372323127353368945234275278994 < c <
  25.5745196289574675215372323127353368945234275279353` (36).
- **Section 7**: the logarithmic expansion (38), the Lambert start (39);
  **Theorem 7.1 (`men:thm:inverse`)**: `⌈ξ − K_M ξ^{−M−1}/log ξ⌉ ≤ min{n ≥ 3 : d_n ≥ X} ≤
  ⌈ξ + K_M ξ^{−M−1}/log ξ⌉`, `ξ` the root of the carrier (41).
- **Theorem 8.1 (`men:thm:fredholm`)**: `C(λ) = det(I + λK) = Π(1 + λκ_j)`,
  `K` positive, injective, trace class, trace `K_0`.
- **Theorem 9.1 (`men:thm:law`)**: the limiting law is an infinite sum of
  independent Bernoulli(`κ_j/(1+κ_j)`) variables; **Theorem 9.2
  (`men:thm:weighted`)**: all fixed-order exponentially weighted `ℓ¹`
  corrections, with `Q_1, Q_2, Q_3`, mean and variance to `N^{−3}`.
- **Theorem 10.1 (`men:thm:largemark`)**: `C(λ) = exp(𝒜√λ)/(2√2 π √λ)(1 + O(λ^{−1/2}))`
  as real `λ → +∞`; **Theorem 10.3 (`men:thm:tail`)**:
  `P(J = m) = 𝒜^{2m+1}/(√2 π C(1)(2m+1)!)(1 + O(m^{−1/2}))`,
  `P(J ≥ m)/P(J = m) = 1 + 𝒜²/(4m²) + o(m^{−2})`; **Corollary 10.4
  (`men:cor:tailinverse`)**: a two-ceiling bracket for the tail threshold.
- **Theorem 11.1 (`men:thm:zeros`)**: the eigenvalues are simple, so the zeros
  of `C` are simple and negative; in each bounded disk the zeros of
  `P_{N+2}` are eventually real and simple; `P_10` has six real and two
  nonreal roots (exact Sturm chain), so finite real-rootedness fails.

Added by the write (7 October 2026), marked `[write]`:

- **Remark 1.1 (`men:rem:oeis`)**: the OEIS entries quoted (next section).
- **Remark 7.2 (`men:rem:transseries`)**: the inverses against the transseries
  volume, statement by statement (see "Relation to the repository").
- Section 1.1 (`men:sec:provenance`: provenance, the sources as the write read
  them, what was checked, relation to the repository, collected non-claims,
  reading conventions); a status note after the abstract; dated notes at the
  end of Section 6 (`C(1)` recomputed), after the proof of Theorem 10.1 (a
  large-mark diagnostic) and in Section 13 (the b-file; the standing rule).

## The OEIS entries (Remark 1.1)

Read on 7 October 2026 in the internal format; quoted verbatim in the article.

- **A386363** (revision #24, 27 February 2026, Mikhail Kurkov, Jul 19 2025):
  "Variation of triangle of Entringer numbers (A008281) read by rows: T(n, k) =
  T(n, k-1) + (n-2)*T(n-1, n-k) for 1 < k <= n, T(n, 1) = T(n-1, n-1) for n > 0,
  T(n, 0) = 0^n." — the recurrence (1).
- **A386381** (revision #27, 27 February 2026, Mikhail Kurkov, Jul 20 2025):
  "Main diagonal of A386363."; "a(n) ~ c * 2^(n+1) * n^(2*n-3) / (exp(2*n) *
  Pi^(n-1)), where c = 25.574519628957467521537232312735336894... -
  _Vaclav Kotesovec_, Sep 02 2025". Corollary 5.2 proves this equivalent with
  `c = π C(1)`; the printed decimal is the truncation of the certified value.
  Its divisibility conjectures (Kurkov's Conjectures 1 and 2; Luschny's
  `A060818(n) | 2a(n)`) are outside this report.

The b-file (Kotěšovec, `n = 0..264`), which the source could not retrieve,
was fetched on 7 October 2026: all 265 terms agree with the write's exact
recomputation from the triangle. Nothing was submitted to the OEIS.

## What is not claimed

From the source, collected in Section 1.1 of the article:

- No historical priority; the recurrence, the leading scale and the posted
  decimal are prior; the overlap review is bounded and settles no posed open
  problem.
- Fixed order only; no convergence of the inverse-power series, no growing-order
  error, no complete exponentially small sectors, no explicit onset; remainder
  constants non-effective.
- The mark is the recursive coefficient statistic; no combinatorial family or
  bijection is claimed.
- The amplitude enclosure trusts mpmath's interval arithmetic and is not a
  proof-assistant verification; longer decimal strings are diagnostics; no
  effective finite-`N` constants.
- The inverse bracket is not an effective algorithm; `⌈x_1⌉` and `⌈ξ_M⌉` are
  not asserted to work.
- Theorem 10.1: no complex-sector uniformity, no joint limit with `N`, no first
  correction coefficient; the tail results concern the limiting law only.
- Theorem 11.1: a bounded-region statement; no eventual real-rootedness, no
  escape rate.

The write adds: its checks are exact finite or floating computations, and it
claims no novelty for any inversion.

## Further questions

Section 13 of the article (`men:sec:limits`) keeps the source's six questions:
effective remainders and threshold algorithms; certified spectral
computation (`μ_J`, `v_J`, the limiting zeros); nonreal root geometry;
large-mark corrections, complex sectors and finite-size rare tails; farther
singularities (towards `−3ρ`); a combinatorial model for the mark. A dated
note there records, under Vladimir's standing rule of 4 October 2026, that
the write found no further unproved claim and no wrong claim in the source,
and that its large-mark diagnostic (below) suggests, without proving, a first
correction `c_1 λ^{−1/2}` with `c_1 ≈ 0.0278`. **Nothing was refuted.**

## Checks made at intake

- At placement (batch-110 dossier, 6 October 2026; Windows 11): the staged
  files byte-identical to a fresh extraction; `SHA256SUMS.json` 33/33. On
  copies, `code/verify.py` normal and `-O`: identical output, JSON-equal to the
  recorded `generated/verification.json`; `code/regenerate.py --compare
  data/certificates.json`: PASS. `guard_tests.py`, `test_build.py` and
  `build.py` were not run (POSIX and TeX Live).
- At the write (7 October 2026; Python 3.14.4, SymPy 1.14.0, mpmath 1.3.0;
  scripts in the intake record): every proof read line by line; by its own
  exact re-expansion `L_0(1), …, L_4(1)`, `[t⁴]H_1`, the six corrections (29),
  `s_1, …, s_4`, `Q_1, Q_2, Q_3`, (52), the mean and variance corrections (53),
  (54) and the coefficients of (38); `P_10` from the marked array, its six real
  roots and gcd 1; `C(1)` at 70 digits by its own midpoint evaluation (inside
  the certified interval; the printed `C(1)` and the OEIS `c` are truncations);
  `𝒜 = 4.2586174557058935695…`; the 265 b-file terms. A diagnostic of Theorem
  10.1: `C(λ)` divided by its leading term is 1.005513, 1.002776, 1.001390,
  1.000695 at `λ = 25, 100, 400, 1600` (`√λ` times the excess: 0.02756,
  0.02776, 0.02780, 0.02781). Route B below was run: verifier and regeneration
  pass, output byte-identical to the dossier's.

## Independent check of the write (7 October 2026)

An adversarial check made by the intake after the write (`e378a2d67`), with
its own code, after fetching again A386363 (#24), A386381 (#27) and its
b-file.

- **Remark 1.1.** Every quotation, revision, date and author line confirmed,
  and row 8 of the triangle. The two divisibility conjectures are unsigned
  lines of A386381, so by OEIS convention its author's (Kurkov's). All 265
  b-file terms and the 21 displayed terms recomputed; `d_{N+2} = (N!)² [z^N] EA`
  checked for `N < 40` from the Taylor recurrences (7), a second route.
- **Recomputations.** By its own symbolic expansion, with (18) checked against
  the operator (16) itself: `[t⁴]H_1`, `L_0(1), …, L_4(1)`, `s_1, …, s_4`, the
  six corrections (29), `Q_1, Q_2, Q_3`, (52), (53), (54) and the coefficients
  of (38); `P_10` from (8), its Sturm chain (the displayed signs, 7 − 1 = 6 real
  roots) and gcd 1; `δ_420 = 5.6973·10⁻⁴⁸`. `C(1)` by the midpoint formula
  (the same 70 digits at `z/ρ = 0.4, 0.5, 0.6`) and, by a route independent of
  the Wronskian, from the exact `d_802` and the twelve-term carrier (28), to 28
  digits: all agree, and every truncation claim of the Section 6 note holds.
  `𝒜 = 4.2586174557058935695…` is a truncation.
- **Large-mark diagnostic.** The four ratios and four products reproduced.
  Continued to `λ = 6400, 25600`: `√λ` times the excess is 0.0278067,
  0.0278052; a first-order Liouville–Green computation (heuristic, not a
  proof) gives `c_1 = ½∫_0^𝒜 (Q + 1/(4x²) − 3/(4(𝒜−x)²)) dx − 1/(4𝒜) =
  0.027803…`. So `c_1 ≈ 0.0278` stands.
- **Remark 7.2.** (a)–(d) re-derived against the volume's statements: the
  instance claims hold (`κ_vol = 2` with `d_vol = −(2 + log ρ)` and
  `2 log(2/(e𝒜))` reproduce both `x_0` exactly), and the interpolation argument
  of (b) has no gap. `Fabius.staircase_ceil` is as described.
- **Provenance.** Archive facts, the staged files (byte-identical), the 102
  delivered label numbers and 73 references, the neighbouring reports and the
  Route B rerun (verifier normal and `-O`, regeneration comparison) confirmed,
  **except** that the write said `SOURCE_AUDIT.md` names three neighbouring
  reports by their GitHub paths: it links only A125054 and names A205497 and
  A122399 by title (corrected by a dated note in Section 1.1 and in the table
  above).
- The check read the source's proofs as well and found no error.

The check is recorded at the end of Section 13.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. The staircase arithmetic that Remark
7.2(a), (b), (d) applies is formalized generically as `Fabius.staircase_ceil`
in `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`
(a lemma about an arbitrary strictly monotone function); nothing about `d_n` is.

**The transseries volume**
(`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`),
Remark 7.2: (a) `min{n ≥ 3 : d_n ≥ X}` is an **instance** of the staircase of
`p0:def:three-inverses`(1) (`n_1 = 3`), so `p0:thm:staircase`(1) applies;
(b) Theorem 7.1 as stated and proved is an **analogue** of
`p0:thm:staircase`(2) (a direct bracket about the root of a carrier that does
not interpolate the sequence); the write routes it through
`p0:thm:staircase`(1) with the interpolation `F_M e^{Ẽ}` (the same comparison
rearranged, not an independent proof); (c) the Lambert start (39) is an
**instance** of `p0:prop:factorial-core` with `κ_vol = 2`,
`d_vol = −(2 + log ρ)`; (d) the tail threshold of Corollary 10.4 is a staircase
**instance** (`A_m = −log P(J ≥ m)`, `n_1 = 0`), its bracket an **analogue** of
`p0:thm:staircase`(2), and its start (71) an **instance** of
`p0:prop:factorial-core` with `d_vol = 2 log(2/(e𝒜))`.

**Neighbouring reports** (under `SetTheory/Cardinals/docs/reports/`):
`…/oeis-sequence-asymptotics/a125054-central-poupard-numbers` (tangent numbers
by the Seidel boustrophedon), `congruences-and-valuations/secant-number-periodicity`
(secant numbers through the Entringer triangle),
`…/a205497-zigzag-eulerian-spectra` and `…/a122399-surjection-diagonal` (named by
the source audit). They share classical ingredients but no object or result,
so no reciprocal note is proposed.

**Stale claims.** Before batch 110 no file of the repository named A386381 or
A386363. The source's sentence that the b-file could not be retrieved carries a
dated note (Section 13).

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: `c`, `C(λ)`, `C_*`; `A`, `A_λ`, `𝒜`; `d`
(`1/(e√ρ)`) against `d_n`; `E`, `𝔼`, `e_n`; `K` (the Green operator, but a
compact mark set in Theorems 5.1 and 9.2), `K_0`, `K_M`, `K_tail`, `k`; `L`,
`L_j`, `L_λ`, `ℒ_λ`; `H_λ` against the tail carrier `H(x)`; `G_λ`, `G`, `G_N`,
`𝒢`; `W(r,j)`, `W_0`, `W_x`; `p_n`, `p_j`, `p(m)`, `q_n`, `q_m`; `Q_λ`, `Q_j`, `Q`;
`N`, `n`, `M`, `m`; `V`, `V(r)`, `v_J`; `S`, `μ`, `μ_J`; the two pairs
`x_0, x_1`; `B`, `B_{2j}`, `B_ν`; `ρ`, `κ_j`, `Φ`; `T(n,k)`, `T`, `t`; `δ_m`, `δ`.
No symbol was renamed; the volume's colliding letters carry the subscript
"vol" in Remark 7.2.

## Labels

Every label carries the prefix `men:` (none existed in the repository). The
manuscript's 102 labels (`eq:` 74, `sec:` 13, `thm:` 9, `prop:` 2, `lem:` 2,
`cor:` 2) were prefixed before anything cited them, and the 73 references to
them (64 `\eqref`, 9 `\ref`) updated. The write added 4: `men:sec:scope`,
`men:sec:provenance`, `men:rem:oeis`, `men:rem:transseries`. The report has 106
labels; builds of the delivered text and of this one give all 102 delivered
labels the same numbers (aux files compared). The added remarks are the last
statements of their sections, the added subsection follows the last delivered
text of Section 1, and the added displays are unnumbered. The verified OEIS
prefix block of Section 1 (between `% BEGIN VERIFIED OEIS PREFIX` and
`% END …`), which `code/verify.py` parses, is unchanged.

## Files

```text
README.md                                         this guide (replaces the delivery README)
article.tex                                       the report (delivered Report180.tex; labels prefixed, [write] additions)
article.pdf                                       compiled report, 27 pages
README_CODE.md                                    delivered reproducibility guide (delivered names)
SOURCE_AUDIT.md                                   delivered source and attribution audit
optional-README.md                                delivered guide to the optional programs (delivered optional/README.md)
code/verify.py                                    exact standard-library verifier (delivered code/)
code/exact.py                                     exact algebra used by the verifier (delivered code/)
code/regenerate.py                                regenerates data/certificates.json to a new file (delivered code/)
code/verify_manifest.py                           release-manifest checker and file helpers; imported by verify.py (delivered at the root)
code/guard_tests.py                               corruption and -O guard tests (delivered at the root)
code/test_build.py                                builder tests; POSIX (delivered at the root)
code/build.py                                     offline PDF and archive builder; TeX Live, POSIX (delivered at the root)
code/optional-producer-verify_entringer.py        SymPy/mpmath producer diagnostics (delivered optional/producer/)
code/optional-producer-certify_entringer.py       interval certificate of c (delivered optional/producer/)
code/optional-producer-check_marked_coefficients.py  symbolic marked corrections (delivered optional/producer/)
code/optional-audit-check_exact.py                independent exact audit (delivered optional/audit/check_exact.py)
code/optional-root-check.py                       scalar expansion and amplitude estimates (delivered optional/root/check.py)
code/optional-check_length.py                     optical-length quadrature (delivered optional/check_length.py)
data/certificates.json                            exact certificate (delivered data/)
data/PROVENANCE.json                              frozen-reference provenance and hashes (delivered data/)
data/references-checks.json                       frozen reference (delivered data/references/)
data/references-entringer_connection_certificate.json  frozen interval certificate (same)
data/references-entringer_diagnostics.json        frozen producer diagnostics (same)
data/references-exact_checks.json                 frozen audit output (same)
data/references-finite_nonreal_counterexample.json  frozen P_10 record (same)
data/references-length_diagnostics.json           frozen optical-length diagnostics (same)
data/references-marked_coefficients.json          frozen marked coefficients (same)
data/generated-verification.json                  recorded verifier output (delivered generated/)
data/generated-verification_guards.json           recorded guard output (same)
data/generated-build_guards.json                  recorded build-guard output (same)
data/generated-BUILD_INFO.json                    recorded build information (same)
data/optional-requirements.txt                    sympy==1.14.0, mpmath==1.3.0 (delivered optional/requirements.txt)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. `code/verify_manifest.py`,
`data/optional-requirements.txt` and `data/generated-build_guards.json` are
generic files with byte-identical copies in other reports of this collection;
they are shipped here so that the package reruns on its own.

**Not shipped**, recoverable from the arrival commit (next section):
`Report180.pdf` (the delivered 22-page PDF, 393,054 bytes); the checksum
manifest `SHA256SUMS.json` (3,285 bytes, 33 entries), verified at placement
(repository policy ships no checksum manifests); and the delivery `README.md`
(6,495 bytes), staged at placement and replaced by this guide (summarized
below).

**Delivered text that names the delivery layout or files not shipped.**
`README_CODE.md` and `optional-README.md` (paths `code/`, `data/references/`,
`optional/…`, `generated/`, `Report180.tex`, `Report180.zip`,
`SHA256SUMS.json`, root `build.py`, `guard_tests.py`); `SOURCE_AUDIT.md`;
`code/verify.py` (imports `verify_manifest` from the package root, reads
`Report180.tex` and pins 14 reference and program hashes by delivered path);
`code/regenerate.py`, `code/guard_tests.py`, `code/test_build.py`,
`code/build.py` (delivered paths); `data/PROVENANCE.json` (delivered paths);
the optional programs (write JSON beside themselves); and Section 12 of the
article ("The accompanying source archive", "The package README"). So no
program runs under the shipped names; use Route B below.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Modified_Entringer_Asymptotics_and_Spectral_Limits_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # 23d6b43bbad18e36643b9c7b9be6a30bf1209bba6334f20287e089a7f571f95f, 789,613 bytes
cd "$T" && unzip -q a.zip
```

`SHA256SUMS.json` maps the 33 other files to their SHA-256 values.

## Rerun the checks (on a scratch copy)

Python 3.10 or later; the core needs only the standard library. Never run
anything in the repository.

**Route A, delivered layout** (as `README_CODE.md` gives it), in the extraction
`$T`: `python -I -S -B code/verify.py`, the same with `-O`,
`python -I -S -B code/regenerate.py --output /tmp/new.json --compare
data/certificates.json`; `guard_tests.py`, `test_build.py` and `build.py` need
POSIX and TeX Live. The optional programs (SymPy 1.14.0, mpmath 1.3.0) write
beside themselves: copy them to a fresh directory first, as `optional/README.md`
says.

**Route B, from the shipped files** (tested at the write on Windows): rebuild
the delivered layout under the delivered names, then run the core.

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a386381-modified-entringer
B=$(mktemp -d); cd "$B"; mkdir -p code data/references generated optional/producer optional/audit optional/root
cp "$R/article.tex" Report180.tex; cp "$R/README_CODE.md" "$R/SOURCE_AUDIT.md" .; cp "$R/optional-README.md" optional/README.md
for f in build guard_tests test_build verify_manifest; do cp "$R/code/$f.py" .; done
for f in exact regenerate verify; do cp "$R/code/$f.py" code/; done
cp "$R/code/optional-check_length.py" optional/check_length.py; cp "$R/code/optional-audit-check_exact.py" optional/audit/check_exact.py
cp "$R/code/optional-root-check.py" optional/root/check.py; cp "$R/data/optional-requirements.txt" optional/requirements.txt
for f in "$R"/code/optional-producer-*.py; do n=$(basename "$f"); cp "$f" "optional/producer/${n#optional-producer-}"; done
cp "$R/data/certificates.json" "$R/data/PROVENANCE.json" data/
for f in "$R"/data/references-*; do n=$(basename "$f"); cp "$f" "data/references/${n#references-}"; done
for f in "$R"/data/generated-*; do n=$(basename "$f"); cp "$f" "generated/${n#generated-}"; done
python -I -S -B code/verify.py; python -I -S -B -O code/verify.py
python -I -S -B code/regenerate.py --output "$(mktemp -d)/new.json" --compare data/certificates.json
```

At the write both verifier runs printed the same PASS line (21 OEIS terms,
`largest_exact_n` 101, corrections through order 6, 14 reference hashes) and
the regeneration comparison passed, in about a second. The layout differs from
the delivery only by the missing `README.md`, `Report180.pdf` and
`SHA256SUMS.json`; `article.tex` serves as `Report180.tex` because the verifier
reads only its unchanged OEIS prefix block. Use `py` where `python` is not on
the path.

## Build the PDF

pdfLaTeX (fontenc, lmodern, microtype, amsmath, amssymb, amsthm, mathtools,
booktabs, array, geometry, xcolor, hyperref, enumitem, fancyhdr, longtable);
the bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 7 October 2026, and
rebuilt after the independent check of the same day (label numbers
unchanged, aux files compared): 27 pages;
no errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull boxes
(the delivered text also builds without any, 22 pages). The article keeps the
delivered preamble lines that suppress PDF dates and trailer identifiers; the
delivered byte-identity claims apply to `Report180.tex` under the delivering
toolchain, not to this build.

## From the delivery README

The delivery README (replaced by this guide) described the package (article,
"a standard-library exact verifier, frozen computational references, optional
SymPy/mpmath reproductions, and an offline deterministic builder"); listed the
mathematical content; stated "These are conventional mathematical arguments,
not proof-assistant results" and that no convergence of the full series,
complete exponentially small expansion, "universal novelty, or
finite-polynomial Bernoulli representation is claimed"; gave the quick
verification and POSIX build commands (new output directories only); said that
the interval certificate "trusts the interval library implementation"; and
summarized the large-mark theorem ("No joint growing-lambda/N regime,
complex-sector uniformity, Weyl expansion, or numerically certified large-mark
error constant is claimed") and the far tail of the limiting law ("an
asymptotic factorial comparison, not an exact factorial law"; no simultaneous
finite-`N`/`m` tail limit). "No third-party article/book PDFs or raw
research-review dossiers are included."

## Rights

Repository contents are MIT-0. The article and this README quote OEIS
entries A386363 and A386381; OEIS content is published by The OEIS Foundation
Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and that content remains
under that licence (the shipped code embeds the 21 displayed terms). No
third-party PDF is shipped. Nothing was submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A386363, A386381; Millar–Sloane–Young,
  JCTA 76 (1996); Flajolet–Odlyzko, SIAM J. Discrete Math. 3 (1990);
  Flajolet–Sedgewick, *Analytic Combinatorics* (2009); Hough–Krishnapur–Peres–
  Virág, Probab. Surveys 3 (2006); DLMF Chapter 10.
- Batch 110 of `docs/incoming`, bundle Report 180; arrival `60f54ea06`,
  placement `8622ca7e5`, written 7 October 2026. Single source, so no merge
  choices. The delivered `Report180.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
