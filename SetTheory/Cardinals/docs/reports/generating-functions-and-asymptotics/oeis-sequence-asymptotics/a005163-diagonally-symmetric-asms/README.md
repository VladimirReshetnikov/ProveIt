# Diagonally Symmetric Alternating Sign Matrices

**The full leading equivalent and its amplitude, the bounded logarithmic remainder, the fugacity pressure and limit laws, and elementary growth envelopes for OEIS A005163**

This is a research report built on 5 October 2026 (write batch 104) from four
manuscripts of one external research session, Reports 128, 124, 121 and 120 of
the session bundle of Reports 1–243, all dated 2 October 2026. They are four
stages of one programme on one object: the number `a_n` of diagonally
symmetric alternating sign matrices (DSASMs) of order `n` (OEIS
[A005163](https://oeis.org/A005163), `1, 2, 5, 16, 67, 368, 2630, …` for
`n = 1, 2, …`), and the polynomial `Z_n(s)` that weights each DSASM by `s` to
the number of its nonzero diagonal entries, so `a_n = Z_n(1)`. Throughout
`α = ½ log(3√3/4)`, `β = ¼ log 3`, `κ = 5/72`.

- **Part I** (Report 128, the base): the full leading equivalent
  `a_n ~ C_* e^{αn² + βn} n^{−5/72}` along all `n`, and more generally
  `Z_n(s) ~ C(s) e^{αn² + nB(s)} n^{−κ}` locally uniformly on `Re s > 0`; the
  positive amplitude is characterized by convergent Fredholm determinants and a
  convergent Fourier series, not evaluated. This is the **leading term of
  Behrend–Fischer–Koutschan's Conjecture 11.1** (arXiv:2309.08446v3, eq. (11.8));
  their finer corrections are **not** proved. Also: a common calibration
  amplitude on both parities, an exact boundary formula and boundary-ratio limit,
  a Szegő-type constant for Jacobi ensembles with endpoint-vanishing Hölder
  symbols, an amplitude-aware inverse threshold, and the constant terms of all
  fixed diagonal cumulants.
- **Part II** (Report 124; Part I depends on it): stability of the diagonal
  fugacity polynomials (strictly negative roots), weak cross-size interlacing,
  the exact calibration `Z_n(√3) Z_{n+1}(√3) = √3·2ⁿ A_{n+1}`, the bounded
  remainder `log a_n = αn² + βn − κ log n + O(1)` for all `n ≥ 1`, the calibration
  trace limit, an inverse with the `log log` term, a holomorphic pressure with
  bounded error, bounded cumulant errors and an explicitly centred CLT.
- **Part III** (Report 121): the pressure with `o(n)` error by a second route
  (finite Jacobi matrices, a pole-cleared determinant), the linear coefficient,
  and results found only here: the limiting root measure (half of the mass
  escapes to infinity), Newton inequalities, Hoeffding concentration, the
  actual-mean CLT, a parity-lattice local CLT and a speed-`n` large-deviation
  principle with explicit rate.
- **Part IV** (Report 120): elementary envelopes
  `αn² + pn − κ log n − C ≤ log a_n ≤ αn² + qn − κ log n + C` by Jensen and chord
  inequalities on the roots and a projected two-step contraction, with
  `p = 0.26324…< β < q = 0.29604…` certified by exact interval arithmetic, and a
  two-ceiling inverse.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *The full leading equivalent for diagonally symmetric alternating sign matrices: Individual fugacity amplitudes and finite-section boundary limits* (base) | 128 | `A005163_Full_Leading_Equivalent_and_Individual_Amplitude_Source.zip` (1,054,732 bytes, 28 files; `report128.tex` + 8 files in `sections/`, 27 pp.) | none (ships Report 124's TeX and PDF byte for byte as `earlier_input/`) | `612787fb4` | Part I, Sections 1–8, plus the write's Section 9 |
| *Logarithmic asymptotics of diagonally symmetric alternating sign matrices: Bounded determinant remainders and inverse thresholds* | 124 | `A005163_Exact_Logarithmic_Scale_and_Inverse_Thresholds_Source.zip` (536,606 bytes, 17 files; `report124.tex`, 2,289 lines, 34 pp.) | none | `612787fb4` | Part II, Sections 10–24 (in full) |
| *DSASM fugacity pressure and diagonal statistics: Finite Jacobi matrices and cross size interlacing* | 121 | `A005163_Linear_Growth_Fugacity_Pressure_and_Limit_Laws_Source.zip` (496,105 bytes, 18 files; `report121.tex`, 1,837 lines, 27 pp.) | none | `612787fb4` | Part III, Sections 25–40 (26, 28, 29 pointers; 33 partly) |
| *Diagonal fugacity roots and DSASM growth bounds: A partial asymptotic result for A005163* | 120 | `A005163_Diagonal_Roots_Growth_Bounds_and_Inverse_Brackets_Source.zip` (410,599 bytes, 18 files; `report120.tex`, 961 lines, 15 pp.) | none | `612787fb4` | Part IV, Sections 41–49 (42–45 pointers) |

All four archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `612787fb4` (batch 104) removed them from `docs/incoming/`. The write is
batch 104's "Write batch 104 (a005163-diagonally-symmetric-asms): new report,
diagonally symmetric alternating sign matrices".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. None of the manuscripts names an author or a tool, says it is
AI-assisted, or carries "prepared for private review" wording; each is headed
"REPORT N", and `pdfauthor` is empty. Every result, proof, example, remark,
question and limitation of the four manuscripts is printed; the sections that
Reports 120, 121 and 124 share almost word for word are printed once (see
"Labels and numbering"). **Trust boundary:** Part I's operator-theoretic
Sections 2 and 4–6 (and the analytic estimates of Part II's Sections 16–20 and
23, on which Part I rests) were read for structure and for every displayed
algebraic identity that could be checked, but were **not re-derived line by
line** at intake; the limit theorems are the manuscripts' proofs, corroborated
numerically, not independently verified.

## Files

The directory holds 52 files: 7 at the root, 31 in `code/`, 14 in `data/`.

**Report files**, written in the write: this guide, the merged article and its
PDF. The base was delivered as `report128.tex` with eight modules in
`sections/`; the write inlined the modules into `article.tex` (the
`sections/` directory staged at placement is removed), so the whole report is
one file.

```
README.md
article.pdf
article.tex
```

**Report 128, prefix `128-amplitude-`** (14 files): the guide to its exact
check suite; the exact checker and its adversarial campaign, the clean-build,
closed-inventory, repack and replay scripts and the inventory tests; the
recorded exact and audit results, case data and expected values, the
verification receipt and the reference build environment. Its `integrity.py`
also stands for Report 124's (byte-identical).

```
128-amplitude-checks-README.md
code/128-amplitude-build.py
code/128-amplitude-checks-check_exact.py
code/128-amplitude-checks-test_exact.py
code/128-amplitude-integrity.py
code/128-amplitude-repack.py
code/128-amplitude-replay.py
code/128-amplitude-test_integrity.py
data/128-amplitude-build-environment.txt
data/128-amplitude-checks-audit_results.json
data/128-amplitude-checks-exact_results.json
data/128-amplitude-data-cases.json
data/128-amplitude-data-expected.json
data/128-amplitude-verification_results.json
```

**Report 124, prefix `124-logscale-`** (11 files): check guide; build, repack,
replay and inventory-test scripts; the algebra checks, the verifier and its
negative tests; fixtures, reference build environment (also Report 121's,
byte-identical) and receipt.

```
124-logscale-checks-README.md
code/124-logscale-build.py
code/124-logscale-checks-algebra.py
code/124-logscale-checks-negative_tests.py
code/124-logscale-checks-verify.py
code/124-logscale-repack.py
code/124-logscale-replay.py
code/124-logscale-test_integrity.py
data/124-logscale-build-environment.txt
data/124-logscale-checks-fixtures.json
data/124-logscale-verification_results.json
```

**Report 121, prefix `121-pressure-`** (12 files): check guide; build, inventory
(also Report 120's, byte-identical), pack, reproduce and inventory-test
scripts; the exact checks, the pressure checks, the verifier and its mutation
tests; fixtures and receipt.

```
121-pressure-checks-README.md
code/121-pressure-build.py
code/121-pressure-checks-exact.py
code/121-pressure-checks-mutation_tests.py
code/121-pressure-checks-pressure.py
code/121-pressure-checks-verify.py
code/121-pressure-integrity.py
code/121-pressure-pack.py
code/121-pressure-reproduce.py
code/121-pressure-test_integrity.py
data/121-pressure-checks-fixtures.json
data/121-pressure-verification_results.json
```

**Report 120, prefix `120-envelopes-`** (12 files): check guide; build, pack
and inventory-test scripts; the exact-mathematics and interval-arithmetic
checkers, the runner, its support module and its mutation campaign; fixtures
(including the 20 OEIS terms `n = 1..20`), reference build environment and
receipt.

```
120-envelopes-checks-README.md
code/120-envelopes-build.py
code/120-envelopes-checks-exact_math.py
code/120-envelopes-checks-interval_math.py
code/120-envelopes-checks-mutation_tests.py
code/120-envelopes-checks-run_checks.py
code/120-envelopes-checks-support.py
code/120-envelopes-pack.py
code/120-envelopes-test_integrity.py
data/120-envelopes-build-environment.txt
data/120-envelopes-checks-fixtures.json
data/120-envelopes-verification_results.json
```

**Not shipped** (all retrievable from `60f54ea06`): the four PDFs; the four
`CHECKSUMS.sha256` files (verified at placement: 27, 16, 17 and 17 entries)
and the inner inventories `checks/MANIFEST.json` (Report 120) and
`checks/inventory.json` (Reports 121, 124) — repository policy drops checksum
manifests; Report 128's `earlier_input/report124.{tex,pdf}` (byte copies of
Report 124's delivery; Report 124 is Part II); the member manuscripts
`report124.tex`, `report121.tex`, `report120.tex` (printed as Parts II–IV); the
delivery READMEs (Report 128's was staged and is replaced by this guide;
Reports 124's `README.md`, 121's and 120's `README.txt` were not staged);
Report 124's `integrity.py` (= Report 128's), Report 120's `integrity.py`
(= Report 121's) and Report 121's `build-environment.txt` (= Report 124's).

## Labels and numbering

Label prefix **`dsasm:`**: Part I uses `dsasm:` (Report 128's 100 labels),
Part II `dsasm:log:` (Report 124's 145), Part III `dsasm:pr:` (85 of Report
121's 115) and Part IV `dsasm:env:` (37 of Report 120's 62). The other labels
of Reports 121 and 120 sit in their repeated sections and resolve to the
printed ones (Report 121's `eq:parity` is `dsasm:log:parity`; Report 120's
`newton` is `dsasm:pr:newton`). The write added 19 labels: the front matter
`dsasm:sec:guide`, `…:status`, `…:bfk`, `…:notation`, `…:provenance`,
`…:trust`, `…:neighbours`; the Parts `dsasm:part`, `dsasm:log:part`,
`dsasm:pr:part`, `dsasm:env:part`; `dsasm:sec:further`; and section labels the
deliveries lacked, `dsasm:log:sec:main`, `dsasm:pr:sec:main`,
`dsasm:pr:sec:consequences`, `dsasm:pr:sec:questions`, `dsasm:env:sec:main`,
`dsasm:env:sec:consequences`, `dsasm:env:sec:questions`. 386 labels in all, all
distinct.

Sections are numbered continuously and statements within sections, so a
statement number moves with its section only. The four manuscripts number
equations consecutively through the text; each Part keeps those numbers:

| Part | Manuscript | Section here | Statement `k.j` | Equation `(k)` |
|---|---|---|---|---|
| I | Report 128 | `k` (1–8); Section 9 added | `k.j` | `(k)` |
| II | Report 124 | `k + 9` (10–24) | `(k+9).j` | `(II.k)` |
| III | Report 121 | `k + 24` (25–40) | `(k+24).j` | `(III.k)` |
| IV | Report 120 | `k + 40` (41–49) | `(k+40).j` | `(IV.k)` |

So Report 124's Theorem 1.1 is Theorem 10.1 and its equation (110) is (II.110);
Report 121's Theorem 10.1 is Theorem 34.1. **Repeated sections**: Reports 121's
and 120's Sections 2, 4, 5 are printed once, as Part II's Sections 11, 13, 14
(Report 124's 2, 4, 5); Report 120's Section 3 is printed once, as Part III's
Section 27; Report 121's Section 9 is Part II's Section 12 plus two identities.
Their places in Parts III and IV (Sections 26, 28, 29, 33; 42–45) keep the
title, the equation numbers (advanced so that the following equations keep
theirs), every differing sentence (the "structural part of Theorem [main]"
ending, Report 120's longer closing non-claim, Report 120's `d` for
`d_ASM`, Report 121's root formula written without the definition of `M_n`,
its identities (III.63)–(III.64) and last sentence) and a
pointer. A reference in Parts III and IV to an equation of a repeated section
shows its printed number, e.g. (II.17) for Report 121's (15). A comparison of
the build's `.aux` with separate builds of the four delivered `.tex` files
confirmed every printed label's number under these rules (367 of 367).

## Notation

No symbol was renamed. The front matter's "Notation across the four Parts"
fixes the convention and lists every letter whose meaning changes, with the
tempting false readings; each Part opens with a reading-conventions table. The
most dangerous is **`P_n`**: with a polynomial argument (`P_n(t)`, `P_n(s²)`)
it is the parity-reduced polynomial, `Z_n(s) = s^{n mod 2} P_n(s²)`, of Parts
II–IV; as an operator factor (`P_n 𝓑 P_n`, `Ran P_n`) it is a rank-`n`
projection, onto polynomials of degree `< n` (Part I Section 3, Part II
Section 15) or onto the first `n` coordinates (Part I Sections 2 and 6; Part
II writes `P_n^0`); `P(s) = (s+1)²/(2(s+2))` is the pressure of Part I. Part I
uses only the projections, Report 124 both. Others: `D_n` (companion
polynomial, but a number `log(P_n(4)/P_n(1))` in Part IV), `E_n` (Part I's
function, Part II's number `E_n(1)`, Part IV's `log(P_n(3)/P_n(1))`), `f`
(pressure, `√w ψ_j`, `log tan(θ/2)`), `m`, `v` (slopes, but also a weight
`m(y)`, a Fourier variance `v(F)`, a gamma phase), `M_n` (mean, or a
modulation operator in Part I), `B` vs `β(s)`, `C`, `c`, `a`, `h`, `d`, `r`,
`ν`, `S`, `T`, `Q_n`, `F`, `θ`, and the inverse centres `z_C(T)`, `z(T)`,
`n_0 − β/(2α)`, `c(T)`.

## What the report claims

**Part I (Report 128).**
- Theorem 1.1: a holomorphic `E` on `ℂ \ (−∞, 0]` with
  `E_n(t) = Log(D_n(t)/D_n(3)) − n f(t) → E(t)` locally uniformly, where
  `D_n(t) = Z_n(√t) Z_{n+1}(√t)/√t`; `Z_n(s) = C(s) e^{αn² + nB(s)} n^{−κ}(1 + o(1))`
  locally uniformly on `Re s > 0`, `C(s) = C_cal e^{E(s²)/2} (s/√3)^{1/2} P(s)^{−1/4}`,
  `C_cal = 3^{11/72} π^{1/6} e^{ζ'(−1)/6} / (2^{1/24} Γ(1/3)^{1/3})`; in particular
  `a_n ~ C_cal 2^{−1/4} e^{E(1)/2} e^{αn² + βn} n^{−5/72}`. The explicit formula
  (26) for `E(t)`.
- Section 3: the common calibration `Z_n(√3) ~ C_cal e^{αn² + bn} n^{−κ}` on both
  parities (from the published ASM/OSASM product asymptotics); Proposition 3.1,
  the exact boundary formula for `sZ_n(s)/Z_{n+1}(s)`; the boundary-ratio limit
  (8) `F_n(s) → (s/√3)/√P(s)` (Sections 3–6, Theorems 4.1, 5.1, 6.1).
- Proposition 2.1: a Szegő-type constant `(n+1)μ(F) + ½v(F) + o(1)` for Jacobi
  ensembles with real endpoint-vanishing Hölder symbols (exponent `> ½`), via
  the Breuer–Duits polynomial CLT and exponential integrability.
- Corollary 7.1: `⌈z_C(T) − ε(T)/r⌉ ≤ N(T) ≤ ⌈z_C(T) + ε(T)/r⌉` with `ε(T) → 0`
  and the amplitude in the centre; Corollary 7.2:
  `cum_k(S_n) = n 𝒟^{k−1} m(s) + 𝒟^k L(s) + o(1)`, with explicit mean and
  variance constants.

**Part II (Report 124).** Theorem 10.1: two-sided bounds
`c_− ≤ a_n e^{−αn² − βn} n^κ ≤ c_+` for all `n ≥ 1`;
`log(D_n(1)/D_n(3)) = n log(2/3) + O(1)`;
`D_n'(3)/D_n(3) = (n+1)(1 − √3/2) + o(1)`. Corollary 10.2: the inverse bracket
with the `κ log log T` term. Sections 11–14: stability of `Q_n` on
`Re s_i > 0`, negative roots, interlacing, `|M_n − M_{n−1}| ≤ 1`, the calibration
and its logarithmic form (shared with Reports 120, 121). Sections 15–21: the
exact polynomial operator, the regularized Fredholm comparison, the Jacobi
projection and phase, endpoint Jacobi means, the scalar bound, the Hardy
overlap, the transfer. Theorem 23.1: holomorphic pressure with `O_K(1)` error on
`ℂ \ (−∞, 0]`, all derivatives, all positive fugacities; cumulants
`n(s∂_s)^{k−1}m(s) + O(1)`; the explicitly centred CLT.

**Part III (Report 121).** Theorem 25.1 (stability, interlacing, the adjacent
mean bound, trace limits); Theorem 34.1, the pressure
`(1/n) log(D_n(t)/D_n(3)) → f(t)` on `Re t > 0` with all derivatives (second
route); `log a_n = αn² + βn + o(n)`; the root measure (III.86); cumulant limits;
Hoeffding (III.90); CLT (III.91); local CLT (III.93); LDP (III.97) with rate
(III.95); the inverse (III.98).

**Part IV (Report 120).** Theorem 41.1 (stability; envelopes with certified
`p`, `q`); Sections 46–47 (Jensen/chord, projected contraction, the interval
certificates (IV.48)–(IV.50)); Theorem 48.1 (two-ceiling inverse, limiting
width `(q − p)/(2α) ≈ 0.1254 < 1`).

**Added by the write** (all marked `[write]`, dated 5 October 2026): the front
matter (guide, status table, the section on Conjecture 11.1, notation,
provenance, trust boundary, neighbours); each Part's reading conventions;
Section 9, "Further questions and research"; the pointer sections; and dated
notes, which contain only short deductions, each with its justification:
(a) Part III's local CLT may be centred at `nm(s)` (Part II gives
`M_n(s) − nm(s) = O(1)`, `σ_n ≍ √n`, `φ` Lipschitz); (b) Part II's bounds hold
with any `c_− < C_* < c_+` for large `n` (Part I); (c) Part II's question 2 is
answered since `x_n → log C_*`; (d) Part III's question 2 is answered by
Part II's `O(1)` cumulants; (e) Part IV's questions 1, 3, 4 are answered by Parts
III, II, I. Nothing else is new.

**Behrend–Fischer–Koutschan.** The write checked arXiv:2309.08446v3 (HTML, 5
October 2026): version 3 is dated 1 October 2026; Conjecture 11.1 is eq.
(11.8), `|DSASM(n)| = C (3√3/4)^{n²/2} 3^{n/4} n^{−5/72} (1 − 385/(31104n²) +
(−1)^{n/2} a n^{−5/2} + O(n^{−3}))` for even `n` (odd: `(−1)^{(n+1)/2} b`),
with `C ≈ 0.72352852136732…`, `a ≈ 0.0783`, `b ≈ 0.1892` estimated from
`n ≤ 1000` and `b = (1+√2)a` conjectured; no closed form for `C`. Part I proves
the leading term (existence and characterization of `C`); the `n^{−2}` and
`n^{−5/2}` terms, the relation `b = (1+√2)a`, any rate and the digits of `C` are
not proved. The manuscripts' citations (eqs. (4.1), (4.11), (5.10)/Prop. 5.1,
(11.3)–(11.6), Theorem 11.2) match that version.

**Independent check of the write (5 October 2026).** An adversarial check
made by the intake after the write (`ed4d0a12f`) reread the deductions (a)–(e)
and the identification of Theorem 1.1 with the leading term of (11.8) (and
`p < B(1) = β < q`), the merge (the eight `\cite{r124}` conversions, (I1)–(I4)
against Report 124, the shared sections printed once), the statements about
Conjecture 11.1, and every number in the notes and in Section 9. It found every
mathematical claim valid, with no counterexample and no gap, and the merge
faithful. Changes, each dated, with a note keeping the first wording where
wording was replaced:

- Section 9, item 1: the centre of the uncertified estimate is
  `C_* ≈ 0.7235287` (`exp(−0.323615) = 0.72352875…`), not 0.7235288; a note
  adds that a `1/n`-drift extrapolation has no basis in the form of (11.8), and
  that least-squares fits of `r_n` to that form over four windows in
  `80 ≤ n ≤ 200` give `log C_*` between −0.3236153120 and −0.3236153117, within
  `7·10⁻¹⁰` of BFK's −0.3236153123 (uncertified).
- Section 9, item 6: the boundary-ratio errors are not "decreasing"; each
  varies with period 4 in `n` without changing sign, and only its maximum over
  `4k ≤ n ≤ 4k + 3` decreases (about `4·10⁻⁷`, `10⁻⁶`, `1.6·10⁻⁵` for
  `192 ≤ n ≤ 195`).
- Notes in Sections 42 and 49: Part II proves **weak** cross-size interlacing
  (with multiplicities, (II.21)); strict interlacing remains open with root
  simplicity. *[Dated note, 7 October 2026: the merged abstract still said
  "cross-size interlacing" for Part II; it now says "weak cross-size
  interlacing", with a dated note in the abstract. The same words in the
  delivered texts (Reports 128 and 124, and Report 121's title) stay as
  printed; the two notes above cover them.]*
- Note in Section 40: the comparison values 0.352, 0.455, 0.485, 0.499 are
  `ν([0, x])`, whose finite part has mass ½, not values of its normalized
  finite part; the note adds that Part II's proof of (II.121) is locally
  uniform in `s`, and that every exact `P_n`, `n ≤ 64`, is squarefree with
  `gcd(P_n, P_{n+1}) = 1`, so roots are simple and interlacing strict there.
- Provenance, item 2: the third difference of Report 121's interlacing section
  (the root formula without the definition of `M_n`), already recorded in
  Section 33's note, is added to the list.

The tests, none of which used the delivered or the write's programs: exact
`a_n` for `n ≤ 200` from BFK's Pfaffian (Corollary 4.2) by skew elimination
modulo 280 primes near `2³¹` with CRT (stable when 15 primes are dropped), equal
to the OEIS b-file (`n ≤ 131`) and to the write's terms (`n ≤ 177`); brute-force
enumeration of all ASMs for `n ≤ 7` (counts, `Z_4`, `Z_5`); from these, `r_n`,
the period-4 increments, the residual against (11.8) with BFK's constants
(at most `1.895·10⁻¹⁰` for `170 ≤ n ≤ 177`, `1.56·10⁻¹⁰` for `178 ≤ n ≤ 200`) and
the fits; exact `P_n` for `n ≤ 64` and exact `P_n`, `P_n'` at `t = 1, 3, ¼, 9`
for `n ≤ 200`, confirming `P_n(1) = a_n`, `Z_n(2) = a_{n+1}` (`n ≤ 63`),
`Z_n(c)Z_{n+1}(c) = c2ⁿA_{n+1}` (`n ≤ 199`), the Newton inequalities, the `P_60`
root data, `M_n(1) − n/3 → 0.4060` on both parities and the boundary ratios; a
normalized diff of Part I against Report 128's delivered sections (exactly the
13 lines the conversions explain) and diffs of the shared sections; and (11.8)
and its constants read in the HTML text of arXiv:2309.08446v3. The record is an
unlabelled dated paragraph at the end of Section 9. This was a careful reading
with numerical tests, not a formal verification.

## What the report does not claim

Every limitation is printed in place. In short: **no numerical digits** for
`C_* = C(1)` or for `E(t)` (Section 9 gives an uncertified estimate), no closed
form; **no rate** in the full equivalent, no `n^{−2}` or parity-dependent
correction, no all-orders expansion or transseries; no uniformity as `s → 0` or
`s → ∞` or in growing derivative order; `ε(T)` in the inverse has no explicit
decay and cannot be dropped inside the ceilings; no effective constants or onsets
anywhere, so no certified finite inverse; no root simplicity or strict
interlacing (both hold for `n ≤ 64`, a finite check at the independent check
of the write); stability is not claimed for arbitrary further six-vertex weights or
for a general `r`-refinement of `X_n(r,s,1)`; the Bernoulli representation is
of the total diagonal count, not independence of diagonal indicators; the
root-measure atom at infinity is essential (the finite density has mass ½); the
LDP endpoint values are not point asymptotics, and no `n²`-speed tails are
identified; no priority, peer-review or formal-verification claim. **All four
packages**: finite exact checks corroborate identities, normalizations and
implementations; they prove no asymptotic statement. Part IV's interval
certificates certify only `p` and `q`.

## Further questions, and the standing rule

Each Part closes with a questions section (Sections 9, 24, 40, 49). Under
Vladimir's standing rule of 4 October 2026 the write moved every claim stated
without proof there, with source, sketch and what is missing, and re-scoped the
questions a stronger Part answers:

- Part I, Section 9 (added): (1) the value of `C_*` — **uncertified**:
  `C_* ≈ 0.7235287 ± 10⁻⁶` (so `E(1) ≈ −0.248070 ± 2·10⁻⁶`) from exact terms to
  `n = 177` (residuals `r_n = log a_n − αn² − βn + κ log n`, four-term averages
  and Richardson extrapolation), agreeing with BFK's `log C = −0.32361531…`
  (the centre was first printed 0.7235288; corrected, and sharpened by
  least-squares fits, after the independent check above);
  (2) rate and the finer corrections — **uncertified**: `r_n − r_{n−1}` shows a
  decaying period-4 oscillation (about `±3·10⁻⁷`, `±7·10⁻⁷` near `n = 175`,
  signs `+,+,−,−`), the period of the conjectured `n^{−5/2}` terms, and `r_n`
  for `170 ≤ n ≤ 177` matches BFK's (11.8) with their constants to `2·10⁻¹⁰`;
  (3) an all-orders expansion; (4) effective constants and a certified inverse;
  (5) uniformity in `s`; (6) evaluating `E(t)` (uncertified `E'(1) ≈ 0.0727`).
- Part II, Section 24: questions 1 (limiting amplitude) and 2 (parity at
  constant order) **answered by Part I**; 3 and 4 open (Section 9).
- Part III, Section 40: questions 1 (log term, amplitude) and 2
  (`M_n(s) − nm(s) = o(√n)`) **answered by Parts II and I**; 3 (scales of root
  escape; uncertified: `P_60` has largest root ≈ `7.3·10³²` and root fractions
  consistent with half the mass escaping), 4 (prefactors away from the central
  window), 5 (effective constants) open; root simplicity open (it holds, with
  strict interlacing, for `n ≤ 64`).
- Part IV, Section 49: questions 1, 3, 4 **answered** (Parts III, II, I), 2
  overtaken (Part III's root measure), 5 open; weak interlacing (Part II) and a
  common calibration amplitude (Part I) now proved, root simplicity and strict
  interlacing open.

Superseded statements stay as printed with dated notes pointing forward: Part
II's bounds, inverse and "no limiting amplitude" scope; Part III's `o(n)` growth,
actual-mean centring, inverse and "remain unresolved"; Part IV's envelopes,
inverse and "no common calibration amplitude". **Nothing in any of the four
manuscripts was found to be wrong**; every numerically testable headline claim
held at intake.

## Relation to neighbouring reports and formal projects

No other report in the collection treats alternating sign matrices, DSASMs,
A005163 or arXiv:2309.08446 (searched 5 October 2026: only a bibliography item
in a q-Pochhammer monograph of the Fabius tree and a library-search log line in
`a271619-strict-twice-partitions/181-nested-SOURCE_AUDIT.md`). No reciprocal
notes are needed. Placement in the collection confers no formal status: no Lean
or Rocq file in the repository treats alternating sign matrices, and nothing
here is formalized.

## Delivery names, renames and discrepancies

- Every staged delivered file keeps its bytes; only names changed (tables at the
  end). The base's `report128.tex` and `sections/*.tex` are now the merged
  `article.tex`. The delivered code uses delivery paths (`checks/…`, `data/…`,
  `report12N.tex`, `earlier_input/…`, `CHECKSUMS.sha256`,
  `checks/MANIFEST.json`, `checks/inventory.json`), which are shipped under
  other names or not at all, and the closed-inventory checkers reject any
  layout but the delivered one, so **none of the scripts runs in this
  directory**. Run them on a fresh extraction (below).
- **Unshipped files named in delivered text**: the four checks READMEs and
  scripts name the checksum inventories, `MANIFEST.json`/`inventory.json`,
  `report12N.{tex,pdf}` and (Report 128) `earlier_input/`; Report 128's
  `build.py` rebuilds and compares Report 124's PDF from `earlier_input/`.
- **Paths**: `120-envelopes-checks-README.md` writes its campaign output to
  `/tmp/report120-check-results.json`, and Report 120's delivered README names
  `/tmp/report120-reproducibility.zip`; use a scratch directory outside the
  repository. Reports 121's and 124's delivered READMEs name sibling archives
  `../report12N_*.zip|json`. The reference toolchain in `data/*-build-environment.txt`
  is Linux, Python 3.12, TeX Live 2025/dev (Debian).
- **In-place writers**: `integrity.py --write` rewrites the inventory, and the
  build/pack/repack scripts write PDFs and archives; run only on a copy.
- **Windows**: Report 120's `checks/mutation_tests.py` has a mutation case
  (`file.fifo`) that calls `os.mkfifo`, which Windows lacks: there the campaign
  aborts with `AttributeError` and then `INTEGRITY_UNLISTED`. Run it on POSIX,
  or on Windows with a `sitecustomize.py` on `PYTHONPATH` (outside the package)
  that emulates `os.mkfifo` by an empty placeholder which `pathlib` reports as
  neither file nor directory, and forces LF newlines; with that shim the
  campaign's output was byte-identical to the receipt at intake. Other suites
  only need LF output on Windows.

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. Recreate the
delivered layout from the arrival commit:

```
git show 60f54ea06:docs/incoming/A005163_Full_Leading_Equivalent_and_Individual_Amplitude_Source.zip > s128.zip
git show 60f54ea06:docs/incoming/A005163_Exact_Logarithmic_Scale_and_Inverse_Thresholds_Source.zip > s124.zip
git show 60f54ea06:docs/incoming/A005163_Linear_Growth_Fugacity_Pressure_and_Limit_Laws_Source.zip > s121.zip
git show 60f54ea06:docs/incoming/A005163_Diagonal_Roots_Growth_Bounds_and_Inverse_Brackets_Source.zip > s120.zip
for r in 128 124 121 120; do mkdir r$r && unzip -q s$r.zip -d r$r; done
cd r128/report128 && python3 -B integrity.py && python3 -B checks/check_exact.py > ../../c128.json   # compare with checks/exact_results.json
python3 -B checks/test_exact.py; python3 -B test_integrity.py
cd ../../r124/report124 && python3 -B integrity.py && python3 -B checks/verify.py && python3 -B checks/negative_tests.py
cd ../../r121/report121 && python3 -B integrity.py && python3 -B checks/verify.py && python3 -B checks/mutation_tests.py
cd ../../r120/report120 && python3 -B checks/run_checks.py && python3 -B checks/mutation_tests.py --output ../../c120.json
```

Each verifier also runs under `python3 -B -O`. Python 3.10 or later with the
standard library suffices; on Windows use `py -B` and see the shim above.
Results at placement (5 October 2026, copies, Windows with the LF/`mkfifo`
shim): Report 120 `run_checks.py` normal = `-O` = receipt, `mutation_tests.py`
(198 named cases, 396 negative runs) byte-identical to its receipt,
`test_integrity.py` 14 mutations × 2 modes; Report 121 `verify.py` normal and
`-O` byte-identical to the receipt, 82 negative cases; Report 124 `verify.py`
normal = `-O` = receipt, `negative_tests.py` 86 expected failures; Report 128
`check_exact.py` normal and `-O` and `test_exact.py` byte-identical to their
recorded results; every `integrity.py` passed (17, 17, 16, 27 files), and every
`CHECKSUMS.sha256` verified. At the write (5 October 2026, Python 3.14.4,
Windows, fresh extraction of Report 128's archive) `integrity.py` passed
(27 files) and `checks/check_exact.py` reproduced `checks/exact_results.json`
byte for byte in about 42 s. Not run: the PDF builds and replays (byte identity
needs the recorded TeX Live toolchain) and the pack/repack scripts.

## Rights

Repository contents are MIT-0. The sequence terms printed in the article and
contained in the code and data are recomputed by the shipped programs; Report
120's fixtures (`data/120-envelopes-checks-fixtures.json`) and receipt contain
the 20 OEIS terms of A005163 for `n = 1..20`, transcribed from the OEIS entry
(not the b-file). OEIS data are available under CC BY-SA 4.0
([OEIS license](https://oeis.org/LICENSE)). Credits: the OEIS entry for the
sequence; Behrend–Fischer–Koutschan for the six-vertex correspondence, the
Pfaffian and adjacent determinant, `Z_n(2) = a_{n+1}`, Theorem 11.2 and
Conjecture 11.1 with its numerical constant; Borcea–Brändén for the MOD
operator and stable pencils; Krattenthaler for the shifted determinant;
Rosengren, Frenzen–Wong, Simon, Breuer–Duits, Casper–Zurrián,
Alseidi–Margaliot–Garloff, Cao–Li–Lin and the DLMF as cited. Nothing was
submitted to the OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy; commit only `article.pdf`. The write's
build (5 October 2026): 104 pages, no errors, no warnings, no undefined or
multiply defined references or citations, no duplicate destinations, no
overfull or underfull boxes; the four delivered `.tex` files build alone
without warnings (27, 34, 27 and 15 pages).

Rebuilt on 5 October 2026 after the independent check, in a scratch copy with
four pdfLaTeX passes: 106 pages (104 before; the record and the longer notes
of Section 9 add two pages), no errors, no warnings, no undefined or multiply
defined references or citations, no duplicate destinations, no overfull or
underfull boxes; all 386 labels keep their numbers (`.aux` compared with a
build of the committed text; page numbers from the end of the front matter on move by at most two).

Rebuilt on 7 October 2026 (cleanup pass, "weak" in the abstract with its
dated note) with three pdfLaTeX passes: 106 pages, equally clean; all 386
labels keep their numbers and pages (`.aux` compared with a build of the
committed text); page 1 rendered and inspected.

## Delivered path → shipped path

Report 128 (`128-amplitude-`; `README.md` replaced by this guide):

| Delivered | Shipped |
|---|---|
| `report128.tex`, `sections/01_main.tex` … `07_consequences.tex` | `article.tex` (Part I) |
| `sections/08_references.tex` | merged into the bibliography of `article.tex` |
| `checks/README.md` | `128-amplitude-checks-README.md` |
| `build.py`, `integrity.py`, `repack.py`, `replay.py`, `test_integrity.py` | `code/128-amplitude-<name>` |
| `checks/check_exact.py`, `checks/test_exact.py` | `code/128-amplitude-checks-<name>` |
| `checks/exact_results.json`, `checks/audit_results.json` | `data/128-amplitude-checks-<name>` |
| `data/cases.json`, `data/expected.json` | `data/128-amplitude-data-<name>` |
| `build-environment.txt`, `verification_results.json` | `data/128-amplitude-<name>` |
| `report128.pdf`, `CHECKSUMS.sha256`, `earlier_input/report124.{tex,pdf}` | not shipped |

Report 124 (`124-logscale-`):

| Delivered | Shipped |
|---|---|
| `report124.tex` | not shipped; printed as Part II of `article.tex` |
| `checks/README.md` | `124-logscale-checks-README.md` |
| `build.py`, `repack.py`, `replay.py`, `test_integrity.py` | `code/124-logscale-<name>` |
| `checks/algebra.py`, `checks/negative_tests.py`, `checks/verify.py` | `code/124-logscale-checks-<name>` |
| `checks/fixtures.json` | `data/124-logscale-checks-fixtures.json` |
| `build-environment.txt`, `verification_results.json` | `data/124-logscale-<name>` |
| `integrity.py` | = `code/128-amplitude-integrity.py` (byte-identical) |
| `report124.pdf`, `README.md`, `CHECKSUMS.sha256`, `checks/inventory.json` | not shipped |

Report 121 (`121-pressure-`):

| Delivered | Shipped |
|---|---|
| `report121.tex` | not shipped; printed as Part III of `article.tex` |
| `checks/README.md` | `121-pressure-checks-README.md` |
| `build.py`, `integrity.py`, `pack.py`, `reproduce.py`, `test_integrity.py` | `code/121-pressure-<name>` |
| `checks/exact.py`, `checks/mutation_tests.py`, `checks/pressure.py`, `checks/verify.py` | `code/121-pressure-checks-<name>` |
| `checks/fixtures.json` | `data/121-pressure-checks-fixtures.json` |
| `verification_results.json` | `data/121-pressure-verification_results.json` |
| `build-environment.txt` | = `data/124-logscale-build-environment.txt` (byte-identical) |
| `report121.pdf`, `README.txt`, `CHECKSUMS.sha256`, `checks/inventory.json` | not shipped |

Report 120 (`120-envelopes-`):

| Delivered | Shipped |
|---|---|
| `report120.tex` | not shipped; printed as Part IV of `article.tex` |
| `checks/README.md` | `120-envelopes-checks-README.md` |
| `build.py`, `pack.py`, `test_integrity.py` | `code/120-envelopes-<name>` |
| `checks/exact_math.py`, `checks/interval_math.py`, `checks/mutation_tests.py`, `checks/run_checks.py`, `checks/support.py` | `code/120-envelopes-checks-<name>` |
| `checks/fixtures.json` | `data/120-envelopes-checks-fixtures.json` |
| `build-environment.txt`, `verification_results.json` | `data/120-envelopes-<name>` |
| `integrity.py` | = `code/121-pressure-integrity.py` (byte-identical) |
| `report120.pdf`, `README.txt`, `CHECKSUMS.sha256`, `checks/MANIFEST.json` | not shipped |

## Provenance

Four manuscripts (bundle Reports 128, 124, 121, 120) → one report; base 128.
Arrival `60f54ea06`, placement `612787fb4`, write batch 104 (5 October 2026). No
manuscript pins a ProveIt commit. Merge choices (strength order with Report 128
as base and Report 124 printed in full because Part I depends on it; shared
sections printed once with pointer sections keeping every differing sentence;
Report 128's eight citations of Report 124 made internal; the merged
bibliography keeping every annotation; the modules inlined) are listed in the
article's front matter, "Provenance and merge decisions".
