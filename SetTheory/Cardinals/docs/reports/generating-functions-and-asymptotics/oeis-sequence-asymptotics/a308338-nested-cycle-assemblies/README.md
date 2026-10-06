# Assemblies of Nested Cycles (OEIS A308338, A392471, A007838)

**`a_n ~ C n! n^{c/2−3/4} e^{2√(cn)}` with `c = e^{−γ}` and an explicit `C`;
a complex-uniform expansion to every fixed order in `n^{−1/2}` with
polynomials in `log n`; the mean and variance of the number of components
with their logarithmic and constant corrections; a two-ceiling inverse; and,
from the write, Riedel's conjecture `E[X] ~ N√n` proved with
`N = e^{−γ/2}`, and a corrected covariance display of Erlihson and
Granovsky**

A research article ("Report 167" of a session bundle), built from one
manuscript dated 3 October 2026. Its author line reads "Report 167" and its
PDF author field is empty: it names no person, tool or addressee. The package
carries no "prepared for private review" line, no e-mail address and no
personal data (the word "private" occurs only in the delivered README's
"private fresh format", a TeX format file).

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 167 (batch 108) | `Nested_Cycle_Assemblies_Asymptotics_and_Inverses_Source.zip` (21 files at the archive root and in `companion/` and `data/`, 938,156 bytes, SHA-256 `ef59faff…eaebc0b63`), arrival commit `60f54ea06`; main file `Report167.tex` (908 lines, 15 pp.) | none: the package names no ProveIt commit and cites nothing in the repository | `602e5bd0f` (batch 108) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and nothing in the
repository formalizes these assemblies. No proof uses a computation.

## Trust boundaries

- **What rests on an external theorem.** Every analytic statement rests on
  the component estimate `p_m = B_m/m! = c + c/m + O(log m/m²)` (`(1.4)`,
  `ncy:eq:prior`), which Flajolet, Fusy, Gourdon, Panario and Pouyanne
  (Electron. J. Combin. 13 (2006) R103, Section 3, eq. (22)) attribute to
  Greene and Knuth. It is cited, not reproved; the source read the hybrid
  paper's Section 3 and Proposition 1, not the book. The A007838 entry states
  the same formula and cites the book.
- **What is proved by hand, given it.** The fixed-order expansion, the
  all-arc suppression, the Gaussian Taylor lemma, the explicit `R_1`, `R_2`,
  the moment expansions, the CLT (a known regime, re-proved with this
  normalization) and the two-ceiling inverse. No implied constant or onset is
  made effective; every decimal is an uncertified floating evaluation.
- **The companion** computes `B_n`, `a_n` and the triangle `T(n,k)` exactly
  for `n ≤ 100` by four independent routes (integer cycle product and Bell
  recurrence, rational EGF recurrences, rational powers through `n = 30`,
  literal enumeration through `n = 7`), checks the 100 published terms, and
  (optionally, with SymPy) the finite symbolic identities behind `R_1`, `R_2`,
  `B`, `B_3`, `m_0`, `v_0`, `M_1`, `V_1`. It proves nothing asymptotic.

## What it proves

`P(z) = Π_{m≥1}(1 + z^m/m)` is the EGF of permutations with distinct cycle
lengths (A007838, `B_m`); a nested cycle is such a set of cycles in its
unique decreasing nesting order; `F(z,u) = exp(u(P(z)−1))` counts sets of
them, `a_n = n![z^n]F(z,1)` is A308338 and `T(n,k)` (the coefficient of
`u^k`) is A392471. Statement numbers are the delivered ones.

- **Theorem 2.1 (`ncy:thm:main`)**: for every fixed `J`,
  `f_n(u) = C(u) n^{cu/2−3/4} e^{2√(cun)} {1 + Σ_{j≤J} n^{−j/2} R_j(log n; u) + E_{n,J}(u)}`,
  `deg R_j ≤ 2j`, `E_{n,J} = O(n^{−(J+1)/2}(1+log n)^{2J+2})`, uniformly on a
  small disc about `u = 1`, with every fixed derivative.
- **(2.3) (`ncy:eq:equivalent`)**:
  `a_n ~ C n! n^{c/2−3/4} e^{2√(cn)}`,
  `C = e^{c(1/2−log 2)−1} c^{1/4−c/2}/(2√π) ≈ 0.0947779253874791584`.
- **Sections 3–5**: the local expansion of `log P(e^{−t})` in a right
  half-plane with the constants `B`, `B_3` (`ncy:eq:logP`), the all-arc
  bound (`ncy:eq:globalP`) controlling every secondary arc without crossing
  the natural boundary, and Lemma 5.1 (`ncy:lem:gaussian`).
- **Section 6**: `R_1`, `R_2` explicitly (`ncy:eq:R1`, `ncy:eq:R2`) and a
  formal Bessel-type coefficient calculator (`ncy:eq:calculator`).
- **Theorem 7.1 (`ncy:thm:moments`)**: for the number `K_n` of components,
  `E K_n = √(cn) + (c/2) log n + m_0 + O(n^{−1/2}(1+log n)²)` and
  `Var K_n = √(cn)/2 + (c/2) log n + v_0 + O(…)`, with explicit `m_0`, `v_0`
  and next terms `M_1`, `V_1` (`ncy:eq:explicitM1`, `ncy:eq:explicitV1`); in
  particular `E K_n/√n → e^{−γ/2} = 0.749306…` (`ncy:eq:meanlimit`).
- **Corollary 7.2 (`ncy:cor:clt`)**: `(K_n − E K_n)/σ_n ⇒ N(0,1)`,
  `σ_n² = √(cn)/2` (credited regime: Erlihson–Granovsky 2008, Corollary 4.5,
  attributing it to their 2004 paper).
- **Theorem 8.1 (`ncy:thm:inverse`)**: for `N(y) = min{n : a_n ≥ y}`,
  `⌈x_J − ε_J⌉ ≤ N(y) ≤ ⌈x_J + ε_J⌉` with `x_J` the root of the order-`J`
  model; starting value `x_0* = L/W(L/e)`, `L = log y`, and one Newton step.

Added by the write (6 October 2026), with proofs, marked `[write]`:

- **Remark 7.3 (`ncy:rem:riedel`)**: Riedel's conjecture, proved, and what
  his fitted constants missed (next section).
- **Remark 8.2 (`ncy:rem:transseries`)**: Section 8 against the transseries
  volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`).
  The starting value `x_0*` is an **instance**, verbatim, of
  `p0:prop:factorial-core` with `(κ_vol, d_vol, L_vol) := (1, −1, log y)`;
  `N(y)` is the staircase `N_*` of `p0:def:three-inverses` with `n_1 = 1`
  for `y > 1`; Theorem 8.1 is **not an instance, only an analogue** of
  `p0:thm:staircase`(2): it compares the model `G_J` with `log a_n` at the
  integers and uses monotonicity directly, with no admissible interpolation.
- **Remark 10.1 (`ncy:rem:eg`)**: the Erlihson–Granovsky covariance display,
  refuted and corrected (next-but-one section).
- **Section 1.1 (`ncy:sec:provenance`)**: provenance, the sources as the
  write read them (including the OEIS changes since the source), what was
  checked, relation to the repository, collected non-claims, reading
  conventions; a note on the package at the end of Section 9; a note and
  Question 6 in Section 11.

## Riedel's conjecture, proved

Marko Riedel's note *Nested Cycle Partitions: a conjecture* (January 2026;
revised author-hosted version, page footers dated 24.01.26, and the original
linked from A392471, footers 13.01.26) has on p. 3 a paragraph "The
conjecture", identical in both versions. With `X` the number of components
of a uniformly random nested cycle partition on `n` nodes, the boxed
conjecture is `E[X] ~ N√n` with the constant `N` to be determined. He adds
that the asymptotics might instead involve `n^M` with `M` "close to but not
equal to 1/2", and that the numerical data suggest `M ≥ 0.4704567259` and
`N ≈ 0.7719351399`; the note states neither the range of `n` nor the fitting
method. Neither OEIS entry carries the conjecture. (The batch-108 placement
message paraphrased this as a conjecture `E[X] ~ N n^M` with fitted
`M ~ 0.4705`; the box says `N√n`, and the inequality sign is `≥`.)

- **Proved** (the source's Theorem 7.1; the source quotes Riedel's `N` as a
  "finite-data estimate" but does not say the conjecture is settled): his `X`
  is `K_n`, so `E[X] ~ e^{−γ/2} √n`, `N = e^{−γ/2} = 0.7493060…`. The
  alternative is false: `E K_n ~ N n^M` with `N > 0` holds only for
  `M = 1/2`. The printed inequality `M ≥ 0.4704567259` is satisfied by
  `M = 1/2`; the value `N ≈ 0.7719351399` is not the constant (it exceeds
  `e^{−γ/2}` by 0.0226).
- **What the fits missed** (`[write]`, proved from Theorem 7.1):
  `E K_n/√n = e^{−γ/2} + ((c/2) log n + m_0)/√n + O(n^{−1} log² n)` with
  `m_0 = −0.977132…`, so the ratio exceeds `e^{−γ/2}` for all large `n`; and
  for every fixed integer `ϱ ≥ 2`,
  `M_ϱ(n) = log(E K_{ϱn}/E K_n)/log ϱ = 1/2 − (1−ϱ^{−1/2})(c/2) log n/(√(cn) log ϱ) + O(n^{−1/2})`,
  below `1/2` for all large `n`. The additive `(c/2) log n` is read by a fit
  as a smaller exponent and a larger constant. Computed values
  (double precision, checked against exact and 256-bit values):
  `E K_n/√n = 0.821954, 0.786471, 0.771935, 0.766422, 0.762634` and
  `M_2(n) = 0.47781, 0.48628, 0.49089, 0.49285, 0.49428` at
  `n = 100, 1000, 4500, 10⁴, 2·10⁴`.
- **Where his numbers may come from**: `E K_4500/√4500 = 0.77193514015`
  agrees with his `N` to `2.5·10^{−10}`, and the ratio first drops below it at
  `n = 4501`. This suggests, but the note does not say, that his `N` is the
  ratio at `n = 4500`. The computation behind `M ≥ 0.4704567259` was not
  identified (slopes, two-point exponents and least-squares windows tried).

Recorded only: nothing was submitted to the OEIS and Riedel was not
contacted.

## Correction: the Erlihson–Granovsky covariance display

Erlihson and Granovsky, *Limit shapes of Gibbs distributions on the set of
integer partitions: the expansive case*, Ann. Inst. H. Poincaré Probab.
Statist. 44(5) (2008) 915–945, Theorem 4.3(i), for weights `a_k ~ C k^{p−1}`
(every `p, C > 0`), with `b_r(u) = C Γ(r+1, u)`:

    e_mk = b_{p−1}(u_s) − b_p(u_m) b_p(u_k) / Γ(p+2),   s = max(k, m)

(preprint arXiv:math/0507343v3 eq. (4.54); published eq. (4.18), p. 927;
both read at the write and identical). Corollary 4.5 applies it for all
`u ≥ 0`, `u = 0` being the total number of components.

- **Counterexample** (the source found it; Remark 10.1(a)): `p = 1`,
  `C = 3`, `u = 1`: `e_11 = 3/e − 18/e² = −1.3324 < 0`. At `u = 0` the
  display is `C Γ(p)(1 − Cp/(p+1))`, negative whenever `C > (p+1)/p`.
- **Correction** (`[write]`): the denominator must be `C Γ(p+2) = b_{p+1}(0)`,
  the limit of `r_N^{−p−2} Var Z` for the total mass `Z`; this is what
  conditioning the independent Poisson counts of the Boltzmann model on `Z`
  gives. The corrected value is positive by Cauchy–Schwarz (`0.29163` in the
  example) and equals the printed one only at `C = 1`.
- **Where the `C` is lost**: the published (5.62) (preprint (5.121)) gives
  `Var Z_N ~ Γ(p+2) δ^{−(p+2)}` where `a_k ~ C k^{p−1}` gives
  `C Γ(p+2) δ^{−(p+2)}`; `T_q` in (5.69) has the same factor, while the proof
  of (5.72) uses `Σ_j f_j(p+1) = C Γ(p+2)`. Theorem 4.1(ii)'s covariance
  (4.13) (preprint (4.49)) fails the same way (`−1.4956` at `q = 1`, `p = 1`,
  `C = 3`, `u_1 = 10`). Which step first drops `C` was not traced.
- **Against this report**: here `p = 1`, `C = c`, `r_N = (n/c)^{1/2}`. Read
  at `u = 0`, the printed display predicts the normalized component count to
  have limiting variance `c(1 − c/2) = 0.40384`, the corrected one `c/2 =
  0.28072`; Corollary 7.2 and (7.3), proved without the display, give `c/2`,
  and two normalizations differing by a deterministic shift cannot have
  Gaussian limits of different variances. So the printed display contradicts
  this report, and the corrected one agrees.

The source derived its variance independently and used the display for
nothing; no other report uses it. Not audited: the rest of Section 5 of the
paper (Question 6). Nothing was sent to the authors.

## The OEIS entries at the write (6 October 2026)

- **A308338** (live revision #21; the source froze #17 of 15 January 2026):
  revisions #18–#21 by Alois P. Heinz on 5 October 2026 add a Maple program
  and a b-file for `0 ≤ n ≤ 445`; the 22 data terms are unchanged.
- **A392471** (live #42; the source froze #37 of 25 January 2026): on
  5 October 2026 Heinz inserted the column `k = 0` (offset now 0, rows from
  `n = 0`), a Maple program and a b-file of rows `0..150`. The delivered
  sentence of Section 1 that the triangle "starts at n=1" describes #37; the
  entry now uses this report's extension `T(0,0) = 1`, `T(n,0) = 0`. Its
  link to Riedel's original note is titled "definitions and basic
  recurrences"; the PDF is titled "a conjecture".
- **A007838** (#74, unchanged) states (1.4) and cites Greene–Knuth.
- The three b-files agree with `data/exact_data_100.json` for `n ≤ 100`.

## What is not claimed

From the source, kept in the article (collected in Section 1.1):

- Every fixed order only: no convergence, optimal truncation, Stokes
  phenomenon or complete beyond-all-orders description; constants not
  uniform when the order grows; the calculator is formal.
- No effective constant or onset, no certified `M_J`, no interval enclosure
  of `C`; all decimals uncertified.
- The square-root law, the limit `e^{−γ/2}` and the normal fluctuations are
  the established expansive-assembly regime; the CLT is "not a new
  universality assertion"; no local limit theorem or distance bound.
- Finite and symbolic checks prove nothing asymptotic (the `B`, `B_3` checks
  verify the arithmetic pieces, not the tail summations).
- Bounded source coverage, no worldwide priority, "No claim is made that no
  other work contains overlapping results"; the Greene–Knuth book and the
  2004 Erlihson–Granovsky paper were not inspected; no OEIS amendment.
- Byte identity of rebuilds is toolchain-specific.

The write adds: the table and the `n = 4500` identification in Remark 7.3
are floating evaluations and an inference, not a statement of Riedel's; the
correction in Remark 10.1 rests on the conditioning computation, not on a
re-audit of the whole paper.

## Further questions

Section 11 of the article (`ncy:sec:questions`) states every unproved claim
as an open question (Vladimir's standing rule of 4 October 2026). **Nothing
in the source was found to be wrong**; the two corrections above concern
outside literature.

1. **Effective constants** (`ncy:q:effective`): certified constants and
   onsets for the equivalent and the inverse (it would also give the onset of
   `E K_n/√n > e^{−γ/2}`, computed for `n ≤ 40000`).
2. **Beyond the small disc** (`ncy:q:local`): local limit theorem, moderate
   deviations, a normal-approximation rate.
3. **Periodic terms** (`ncy:q:periodic`): how the root-of-unity component
   corrections appear in exponentially small outer terms.
4. **Higher corrections** (`ncy:q:calculator`): complexity bounds and
   certified simplification.
5. **Faster exact counts** (`ncy:q:bell`).
6. **Erlihson–Granovsky** (`ncy:q:eg`, the write's): does their proof, with
   (5.62) and (5.69) corrected, give the corrected displays, and does
   anything else depend on the missing factor?

## Checks made at intake

- At placement (batch-108 dossier, 6 October 2026; Windows, Python 3.14.4):
  the 19 staged files are byte-identical to a fresh extraction, and
  `SHA256SUMS` verified 20/20. The dossier read the manuscript in full and
  found no false claim; checked `p_100` against `c + c/100`, the counts,
  exact mean and variance at `n = 100` against the theorems, and `a_n` over
  the leading term at `n = 25, 50, 100`; read Riedel's conjecture paragraph
  and verified the literal substitution in the Erlihson–Granovsky preprint.
  On copies, `verify.py` (normal and `-O`), `verify.py --include-data`,
  `test_exact_nested.py` and `symbolic_checks.py` reproduced the four frozen
  outputs; the release tests errored on Windows (POSIX descriptor helpers).
- At the write (6 October 2026; same machine): the archive retrieved from the
  arrival commit again (`SHA256SUMS` 20/20); the companion rerun from a fresh
  extraction (route A) and from the shipped files (route B), reproducing the
  frozen outputs after converting line endings (SymPy 1.14.0); the three
  live OEIS entries, their histories and b-files; both versions of Riedel's
  note as page images; the Erlihson–Granovsky preprint and published text;
  a double-precision evaluation of `a_n/n!`, `E K_n`, `Var K_n` for
  `n ≤ 40000` (residuals consistent with Theorem 2.1 at `J = 1` and with
  `M_1`, `V_1`: at `n = 40000`, `9.682/9.344`, `12.92/12.69`, `16.97/16.53`
  for `√n` times the residual against the next coefficient), and a 256-bit
  fixed-point evaluation of `E K_n` near `n = 4500`.

## Relation to the repository

**Formal status.** No statement of this report is formalized, and no Lean or
Rocq development in the repository concerns these assemblies. Placement in
the collection confers no formal status.

**The transseries volume.** `x_0*` is an instance of
`p0:prop:factorial-core`; the two-ceiling inverse is an analogue of
`p0:thm:staircase` only (Remark 8.2). No novelty is claimed for the
inversion.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a064856-stirling-catalan-transforms` (Part II: cycle-weighted permutation
mixtures, a different model); `a301746-divisor-weighted-asymptotics`,
`a022629-distinct-partition-norms`, `a271619-strict-twice-partitions`
(Gibbs-partition background after Granovsky, Stark and Erlihson). None treats
these sequences, none uses the corrected display, and none needs a
reciprocal note.

**Stale claims.** Before batch 108 no file of the repository named these
sequences or Riedel's note; the source made no claim about the repository.

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with the tempting false readings: `B_m`, `p_m` against the constants `B`,
`B_3`, the calculator `𝓑_β` and Erlihson–Granovsky's `b_r`, `p`; `C(u)`, `C`
against `C_0`, `C_{j,k,m}` and their `C`; `u` against their scaled size `u`;
`L` (`log n` or `log y`) against `L_n(u)` and the volume's `L`; `Q`, `Q_j`,
`X_n` against Riedel's `Q(z,u) = F(z,u)` and `X = K_n`; `K_n`, `K`, `K_0`;
`H_{j,k}`, `H_j`; `ℓ`, `ℓ_c`, `ℓ_r`; `β`; `κ`, `κ'`, `h`, `d`, `δ` against
the volume's and their `δ`; `p`, `q` of Section 8; `N(y)`, `M_J`, `M_1`
against Riedel's `N`, `M` and the write's `M_ϱ(n)`. No symbol was renamed.

## Labels

Every label carries the prefix `ncy:` (none existed in the repository). The
manuscript's 62 labels (`eq:` 46, `sec:` 11, `thm:` 3, `lem:` 1, `cor:` 1)
were prefixed before anything cited them, and the 60 references to them
updated. The write added 10: `ncy:sec:provenance`, `ncy:rem:riedel`,
`ncy:rem:transseries`, `ncy:rem:eg`, and the questions `ncy:q:effective`,
`ncy:q:local`, `ncy:q:periodic`, `ncy:q:calculator`, `ncy:q:bell`,
`ncy:q:eg`. The report has 72 labels; builds of the delivered text and of
this one give all 62 delivered labels the same numbers (aux files compared).

## Files

```text
README.md                             this guide (replaces the delivery README)
article.tex                           the report (delivered Report167.tex; labels prefixed, [write] additions)
article.pdf                           compiled report, 22 pages
companion-README.md                   the companion's README (delivered companion/README.md)
companion-PROVENANCE.md               fixture and source provenance (delivered companion/PROVENANCE.md)
code/companion-exact_nested.py        exact integer/rational computations (delivered companion/exact_nested.py)
code/companion-verify.py              bounded verifier CLI (delivered companion/verify.py)
code/companion-test_exact_nested.py   eight regression groups (delivered companion/test_exact_nested.py)
code/companion-symbolic_checks.py     optional SymPy identities (delivered companion/symbolic_checks.py)
code/build_pdf.py                     deterministic PDF build (delivered at the root)
code/make_zip.py                      allowlist-verified source ZIP (delivered at the root)
code/release_tools.py                 descriptor-pinned output helpers (delivered at the root)
code/test_release.py                  11 tests of the release tools (delivered at the root)
data/SOURCE_PROVENANCE.json           sources, coverage and roles (delivered at the root)
data/verification_receipt.json        author-side receipt (delivered at the root)
data/published_fixtures.json          23 A007838, 22 A308338, 55 A392471 terms (delivered data/)
data/full_verification.json           verify.py output (delivered data/)
data/exact_data_100.json              verify.py --include-data output, all counts to n = 100 (delivered data/)
data/tests.normal.json                regression output (delivered data/)
data/symbolic.normal.json             symbolic-check output (delivered data/)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit (next section):
`Report167.pdf` (the delivered 15-page PDF, 406,435 bytes); `SHA256SUMS`
(1,746 bytes, 20 entries, verified at placement and at the write; repository
policy ships no checksum manifests); and the delivery `README.md` (5,076
bytes), staged at placement and replaced by this guide (summarized below).

**Delivered text that names the delivery layout or files not shipped.**
`companion-README.md` runs `verify.py` etc. "from this directory" and reads
`../data/published_fixtures.json`; `test_exact_nested.py` imports
`exact_nested` and `verify` by those names; so the programs do not run under
the shipped names. `companion-PROVENANCE.md` and `companion-README.md` cite
`../data/…` paths. `build_pdf.py` compiles `Report167.tex`; `make_zip.py`
checks an allowlist of the delivered names (`Report167.pdf`, `companion/…`)
against `SHA256SUMS`; `verification_receipt.json` records hashes of the
delivered source and PDF and of the `data/…` files under delivered names. Section 9
of the article refers to "the package README" for commands. The release
tools require POSIX.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Nested_Cycle_Assemblies_Asymptotics_and_Inverses_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # ef59faff7aba2b7dc9070b282abdf011f7c088dbe7e18f45a02b7d4eaebc0b63, 938,156 bytes
mkdir "$T/pkg" && cd "$T/pkg" && unzip -q ../a.zip     # files at the archive root, plus companion/ and data/
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later; the core needs only the standard library, the symbolic
checks SymPy (1.14.0 used). Never run anything in the repository.

**Route A, delivered layout** (as the delivery README gives it; at the write
on Windows every line below was run except the `-O` variants and the release
tests, which the dossier ran at placement):

```sh
cd "$T/pkg"
python3 -B companion/verify.py > v.out                       # = data/full_verification.json
python3 -B companion/verify.py --include-data > vd.out        # = data/exact_data_100.json
python3 -B companion/test_exact_nested.py > t.out             # = data/tests.normal.json
python3 -B companion/symbolic_checks.py > s.out               # = data/symbolic.normal.json (needs SymPy)
python3 -B -O companion/verify.py
sha256sum -c SHA256SUMS
```

On Windows the outputs carry CRLF line endings and equal the frozen files
after conversion. The release tests (`python3 -m unittest test_release`) and
the PDF and ZIP rebuilds need POSIX and pdfTeX and were not run by the
intake on Windows.

**Route B, from the shipped files, any OS** (tested at the write):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a308338-nested-cycle-assemblies
B=$(mktemp -d); mkdir "$B/companion" "$B/data"; cd "$B"
for f in exact_nested verify test_exact_nested symbolic_checks; do cp "$R/code/companion-$f.py" "companion/$f.py"; done
cp "$R/data/published_fixtures.json" data/
python3 -B companion/verify.py > v.out           # compare with $R/data/full_verification.json
python3 -B companion/test_exact_nested.py > t.out  # compare with $R/data/tests.normal.json
```

Use `py` where `python3` is not on the path. Route A took about 25 s on the
intake's loaded laptop.

## Build the PDF

pdfLaTeX (fontenc, lmodern, amsmath, amssymb, amsthm, mathtools, geometry,
booktabs, array, microtype, hyperref); the bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 6 October 2026: 22
pages; no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes. The delivered source builds the same way to 15 pages, also
without warnings. The article keeps the delivered preamble lines that
suppress PDF dates and trailer identifiers; the delivered byte-identity
claims apply to `Report167.tex` under the delivering toolchain (pdfTeX
1.40.26, TeX Live 2025/dev/Debian), not to this build.

## From the delivery README

The delivery README (replaced by this guide) described the 15-page report
and the package (LaTeX, PDF, bounded exact code, frozen fixtures, outputs);
summarized the results as above, with "No worldwide priority claim or
complete beyond-all-orders transseries"; gave the quick checks of Route A
(normal and `-O`, release tests); said that exact finite checks "do not
certify an asymptotic remainder, error constant, onset threshold, decimal
transcendental constant, or distributional error"; gave POSIX build and
archive commands refusing existing destinations, with two clean builds
reproducing the PDF byte for byte under the same TeX installation; and ended
on sources and limits (the 2004 paper not inspected; "No external
publication, author contact, repository change, or OEIS edit accompanies
this package").

## Rights

Repository contents are MIT-0. The article and the frozen data quote OEIS
terms of A007838, A308338 and A392471; OEIS content is published by The OEIS
Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and those
terms remain under that licence. No third-party PDF is shipped. Nothing was
submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A007838, A308338 (Gutkovskiy,
  20 May 2019), A392471 (Riedel, January 2026); Riedel's note (both
  versions); Flajolet–Fusy–Gourdon–Panario–Pouyanne, Electron. J. Combin. 13
  (2006) R103 (Section 3 and Proposition 1); Erlihson–Granovsky, AIHP 44
  (2008) 915–945 (preprint and published numbering); Erlihson–Granovsky,
  Random Structures Algorithms 25 (2004) 227–245 (not inspected); Greene and
  Knuth (indirect). Read by the write: the three OEIS entries with
  histories and b-files, Riedel's note, the Erlihson–Granovsky preprint and
  published text, the transseries volume (`p0:def:core`,
  `p0:prop:factorial-core`, `p0:def:three-inverses`, `p0:thm:staircase`).
- Batch 108 of `docs/incoming`, bundle Report 167; arrival `60f54ea06`,
  placement `602e5bd0f`, written 6 October 2026. Single source, so no merge
  choices. The delivered `Report167.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
