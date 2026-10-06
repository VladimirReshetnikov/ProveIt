# Self-Complementary Tournament Score Sequences

**Leading equivalents, the strong fraction e^{−λ}, the Θ(2ⁿn^{−3/4}) growth theorem, monotonicity and threshold inverses for OEIS A345470 and A351869, with a corrected Denisov–Wachtel limit density**

This is a research report built on 5 October 2026 (write batch 103) from two
manuscripts of one external research session, Reports 116 and 114 of the
session bundle of Reports 1–243, both dated 2 October 2026. A tournament score
sequence `s_1 ≤ … ≤ s_n` is self-complementary when `s_i + s_{n+1−i} = n − 1`.
`C_n` counts these sequences (OEIS [A345470](https://oeis.org/A345470),
`1, 1, 1, 2, 2, 5, 6, 15, 19, 48, …`) and `D_n` the strong ones
([A351869](https://oeis.org/A351869), `1, 1, 0, 1, 1, 3, 3, 9, 11, 30, …`).
The report counts sorted sequences, not tournaments or isomorphism classes.

- **Part I** (Report 116, the base): `C_n ~ A 2ⁿ n^{−3/4}` and
  `D_n ~ e^{−λ} A 2ⁿ n^{−3/4}` with one amplitude `A > 0` for both parities,
  where `λ = Σ N_k/(k4^k) = 0.33023754…` is the ordinary-score constant
  (`S(1/4) = e^λ`, Kolesnik), so the strong fraction is
  `r = e^{−λ} = 0.71875297…` with a certified enclosure. Part I also has
  `A = 2^{1/4} κ V_DW(1/√2,1/√2) f_Y(0)`, a harmonic identity, a Lambert
  `W_{−1}` smooth inverse with vanishing-width integer brackets, and an
  eventual zero-or-one gap `N_C ≤ N_D ≤ N_C + 1`.
- **Part II** (Report 114, written first): the first proof of
  `C_n, D_n = Θ(2ⁿ n^{−3/4})` (Stockmeyer's Section 6 conjectures), by a
  bounded-bridge argument, with the inverse
  `N_E(x) = log₂x + (3/4)log₂log₂x + O(1)`. It also proves that `C_n` is
  nondecreasing for all `n` and `D_n` for `n ≥ 2`, which Part I does not have.
- **Correction (write).** Both manuscripts copy the limit density printed in
  Denisov–Wachtel's Theorem 1 (2015, p. 170). That display integrates to
  `0.1154552960…`, not 1. The density that the same paper's Remark 2 cites
  from Groeneboom–Jongbloed–Wellner (1999, (2.24)) has `s^{−5/2}` where the
  display has `s^{−1/2}`, and the constant `2^{9/4}/Γ(1/4)`. The write proves
  that the corrected density has mass exactly 1 and velocity marginal
  `f⋆(0) = √(2/3) Γ(3/4)²/π = 0.39027621886917…` at 0. Part I's printed
  `f_Y(0) = 0.0377237…` is about ten times too small. Hence
  `A = √6 Γ(3/4) π^{−3/2} V_DW(1/√2,1/√2)`, and the one lemma whose proof used
  the printed shape is repaired. An independent check of the write
  (5 October 2026) confirmed the corrected density numerically, by a dynamic
  programme of the conditioned walk to `n = 600` (below).

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Leading equivalents for self complementary tournament score sequences* (base); author line "Report 116", PDF author "Research report" | 116 | `Self_Complementary_Tournament_Scores_Leading_Constants_and_Inverses_Source.zip` (541,891 bytes, 17 files; `report116.tex`, 900 lines, 14 pp.) | none (its `checks/fixtures.json` pins Report 114's `checks/results.json` by SHA-256, which matches) | `9c995cefe` | Part I, Sections 1–12 |
| *The growth of self complementary tournament score sequences*; author line "Report 114", PDF author "Research report" | 114 | `Self_Complementary_Tournament_Scores_Growth_and_Inverse_Source.zip` (483,412 bytes, 17 files; `report114.tex`, 717 lines, 11 pp.) | none | `9c995cefe` | Part II, Sections 13–20, plus the write's Section 21 |

Both archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`). The placement
commit `9c995cefe` (batch 103) removed them from `docs/incoming/`. The write
is batch 103's "Write batch 103 (a345470-self-complementary-scores): new
report, self-complementary tournament score sequences".

**Status.** Unrefereed and not formalized; no statement has been checked by a
proof assistant. Neither manuscript names an author or a tool, says it is
AI-assisted, or carries "prepared for private review" wording, and neither
names a ProveIt commit or repository path. Every result, proof, remark,
question and limitation of both manuscripts is printed. Report 114's results
that Part I proves again or more strongly are kept as second routes.

## Files

The directory holds 28 files: 5 at the root, 14 in `code/` and 9 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 116, prefix `116-leading-`**: 14 files besides the article (1 at the
root, 7 in `code/`, 6 in `data/`); its `report116.tex` is the base of
`article.tex`. Root: the guide to its exact checks. `code/`: the exact
checker, the mutation campaign, the replay driver, the integrity checker and
its attack tests, the deterministic PDF builder and archive maker. `data/`:
fixtures, recorded results, mutation results, integrity-test results and the
recorded TeX toolchain.

```
116-leading-checks-reader_validation.md
code/116-leading-build_pdf.py
code/116-leading-checks-mutation_campaign.py
code/116-leading-checks-validate.py
code/116-leading-integrity.py
code/116-leading-integrity_tests.py
code/116-leading-make_archive.py
code/116-leading-replay.py
data/116-leading-build-environment.txt
data/116-leading-checks-fixtures.json
data/116-leading-checks-mutation_results.json
data/116-leading-checks-results.json
data/116-leading-integrity_results.json
```

**Report 114, prefix `114-growth-`**: 12 files (1 at the root, 7 in `code/`,
4 in `data/`), the same kinds of files as Report 116's.

```
114-growth-checks-reader_validation.md
code/114-growth-build_pdf.py
code/114-growth-checks-mutation_campaign.py
code/114-growth-checks-validate.py
code/114-growth-integrity.py
code/114-growth-integrity_tests.py
code/114-growth-make_archive.py
code/114-growth-replay.py
data/114-growth-build-environment.txt
data/114-growth-checks-fixtures.json
data/114-growth-checks-mutation_results.json
data/114-growth-checks-results.json
```

**Not shipped** (all retrievable from `60f54ea06`): the two PDFs; both
`manifest.json` files (SHA-256 manifests of 16 files each, verified at
placement; repository policy drops checksum manifests); Report 114's
`report114.tex` (printed as Part II) and delivery `README.md`; Report 116's
delivery `README.md` (staged at placement and replaced by this guide); and
Report 114's `integrity_results.json`, a byte copy of the shipped
`data/116-leading-integrity_results.json`.

## Labels and numbering

Label prefix **`sct:`**. Part I uses `sct:` for Report 116's 75 labels and
Part II `sct:gr:` for Report 114's 38 labels; 13 label names occur in both
manuscripts, and the sub-prefix separates them. The write added 15 labels:
the front-matter sections `sct:sec:guide`, `sct:sec:status`,
`sct:sec:notation`, `sct:sec:provenance` and `sct:sec:neighbours`; the parts
`sct:part` and `sct:gr:part`; `sct:gr:sec:problem` (Report 114's unlabelled
Section 1); the subsections `sct:sub:density` and `sct:sub:further`; the
section `sct:gr:sec:further`; and the statements `sct:rem:misprint`,
`sct:prop:corrected`, `sct:rem:lemmafix` and `sct:rem:scope`. That makes 128
labels, all distinct.

Sections and equations are numbered continuously through the report, and
statements within sections, as in both deliveries:

| Part | Manuscript | Section here | Statement `k.j` | Equation `(k)` |
|---|---|---|---|---|
| I | Report 116 | `k` (unchanged, 1–12) | unchanged | unchanged, (1)–(56) |
| II | Report 114 | `k + 12` (13–20); Section 21 added | `(k+12).j` | `(k + 56)`, (57)–(81) |

The write's additions in Part I are Section 4.2 (Remark 4.2, Proposition 4.3,
Remarks 4.4–4.5, the last statements of Section 4) and Section 12.1. They have
no numbered equations, so no delivered number moved. For example, Report
114's Theorem 1.1 is Theorem 13.1, its Proposition 6.1 is Proposition 18.1,
and its density display (20) is (76). The build's `.aux` was compared with
separate builds of the two delivered `.tex` files: all 113 delivered labels
have their delivered numbers under these offsets. The delivered audits and
code use the manuscripts' own numbers.

## Notation

No symbol was renamed. The front matter's "Notation across the two Parts"
lists every letter whose meaning changes between the Parts, inside one Part,
or against the neighbouring report `a000571-tournament-score-sequences`, with
the tempting false readings. The most dangerous ones:

- **`f_Y`**: Part I defines it from the misprinted display, value
  `0.0377…` at 0. Theorem 1.1 needs the marginal of the true limit law, which
  the write calls `f⋆`, value `0.3903…` at 0.
- **`T_k`**: in Part I, Sections 5–6, `T_j` is a partial sum of the walk. In
  Section 8, `T_k` counts strong *ordinary* score sequences, a000571's `I_k`.
- **`I_j`**: the area of the walk in both Parts, not a000571's `I_n`.
- **`A`**: the amplitude, and also the Landau excess `A_j`/`A_r`; a000571's
  `A(z)` is a third object, with `A(1/4) = λ`.

Others: `r` (ratio and terminal velocity `r_n`; an index in Part II), `h`,
`q`, `K`, `N`, `a`, `b`, `B`, `c`, `t`, `u` and `L`. Against a000571: `μ`,
`τ` and `σ` mean different things there, while `λ`, `S_n` and `N_k` agree.
Part II's `N_E(x)` uses `log₂` and Part I's `N_E(X)` natural logarithms; they
are the same thresholds.

## What the report claims

**Part I (Report 116).**
- Theorem 1.1: `C_n ~ A2ⁿn^{−3/4}`, `D_n ~ rA2ⁿn^{−3/4}`, `r = e^{−λ}`, one
  `A > 0` for both parities. `λ` is given by the EGZ divisor formula, and
  `0.7187529762 < r < 0.7187529792` follows from Kolesnik's published interval
  (the checker certifies `0.7187529767248666 ≤ r ≤ 0.7187529791004629` from
  1669 exact terms and Kolesnik's tail bound).
- The proof: an exact geometric-gap encoding with an untested final slack
  (Section 2). Denisov–Wachtel's survival theorem and weak limit (imported),
  the regularity of the velocity marginal (Lemma 4.1) and an
  endpoint-weighted maximal estimate (Lemma 5.1) give the fixed-velocity
  endpoint equivalent `P_z(τ>n, V_n=b) ~ c_z f_Y(0) σ^{−1} n^{−3/4}`
  (Theorem 6.1). A summable slack mixture (Section 7) follows. Stockmeyer's
  convolution `D = C(1 − T(z²))` and the ordinary tail bound give the strong
  count (Section 8).
- Section 9: the direct strong amplitude and the harmonic identity
  `Σ_{g≥1} 2^{−g−1} V_DW(g/√2,g/√2) = e^{−λ} V_DW(1/√2,1/√2)`.
- Section 10: the Lambert `W_{−1}` smooth inverse `q_E(X)` with constant
  term, ceiling brackets of vanishing width, the counterexample to a global
  `o(1)` threshold error, `q_D − q_C → λ/log 2 = 0.47643…`, and the eventual
  gap `N_C ≤ N_D ≤ N_C + 1` with both values infinitely often.

**Part II (Report 114).**
- Theorem 13.1: `Θ(2ⁿn^{−3/4})` for both counts and the `O(1)` inverse. This
  is the first proof; Part I implies it and credits it.
- Proposition 14.1 (the encoding), Lemmas 15.1–15.2 (negative-binomial atoms,
  bounded bridge) and Lemma 16.1 (`Θ(k^{−3/4})` endpoint estimate from `(1,1)`)
  are second routes to Part I's Section 2, Lemma 5.1 and Theorem 6.1.
- Proposition 18.1: `C_n` nondecreasing for all `n ≥ 0` and `D_n` for
  `n ≥ 2` (`D_1 = 1 > D_2 = 0`), by explicit injections. This is new; Part I
  has only eventual strict increase.

**Added by the write** (all marked `[write]`, dated 5 October 2026):
- Remark 4.2: the refutation, with its counterexample (below).
- Proposition 4.3: the corrected density
  `h⋆(x,y) = (2^{9/4}/Γ(1/4)) ∫₀¹∫₀^∞ w^{3/2}s^{−5/2}e^{−2w²/s} q_{1−s}(x,−y;0,−w) dw ds`
  `= κ^{−1} h̄_GJW(1,x,−y)`. It proves (a) total mass exactly 1 (Euler's
  integral, Euler's transformation and the quadratic case
  `F(α,1−α;3/2;sin²θ)`); (b) `f⋆(0) = √(2/3) Γ(3/4)²/π` (a `₃F₂` with
  parameters 1 and 2 reduced to `F(−3/4,3/4;1/2;3/4) = cos(π/2) = 0`, giving
  32/27); (c) positivity for `y ≤ 3x`.
- Remark 4.4: Lemma 4.1 for the true density. The delivered majorant
  `s^{3/4}` becomes the non-integrable `s^{−5/4}`; it is replaced by one that
  uses the cancellation in `q`. Theorem 6.1 and Theorem 1.1 then hold with
  `f_Y = f⋆`, and the rectangle positivity of Lemma 9.1 and of Part II's
  Section 16.2 holds unchanged.
- Remark 4.5: what the misprint affects, why `h⋆` is the density of `μ`, the
  numerical evidence and the literature search. Since the independent check
  it also proves the mean area
  `∫∫ x h⋆ = (12/(5√2)) Γ(3/4)/Γ(1/4) = 0.5735865569…`, from
  `∫∫_{x>0} x q_u(x,−y;0,−w) dx dy = wu` (time reversal of the Gaussian
  kernel); the identity is the check's, the integrability argument (Fisher
  information of the mean shift) the write's.
- The amplitude `A = √6 Γ(3/4) π^{−3/2} V_DW(1/√2,1/√2) = 0.539057… × V_DW`.
- The front-matter explanation of why the strong fraction is `e^{−λ}` here and
  `e^{−2λ}` in a000571.

**Independent numerical checks made in the write** (uncertified floating
point; scripts in the session scratchpad, not shipped): a scipy quadrature of
`h⋆` gives mass 1.000000000000 and `f⋆(0) = 0.390276218869`, both to 12 digits.
The same quadrature of the printed display gives mass 0.115455296005 and
`f_Y(0) = 0.037723723892`, agreeing with the placement's 40-digit values.
mpmath confirms the hypergeometric steps to 40 digits. The velocity marginal
of `h⋆` has `f⋆(1)/f⋆(0) = 1.128`, `f⋆(2)/f⋆(0) = 0.338` and
`f⋆(−1)/f⋆(0) = 0.0713`; the printed display renormalized gives 1.803,
0.180 and 0.0135. (The write compared these with the placement's Monte Carlo
of the conditioned Gaussian walk at `n = 2000`, 1.107, 0.347 and 0.0775; that
evidence is superseded by the independent check's walk computation below.)

**Independent check of the write (5 October 2026).** An adversarial check
made by the intake after the write (`1b792e07a`) reread Section 4.2
(Remark 4.2, Proposition 4.3 with its proof, Remarks 4.4 and 4.5) and the
front matter's "Relation to the ordinary score sequences". It found every
mathematical claim valid, with no counterexample and no gap in any proof
chain, and four defects in the supporting text. Each is corrected in the
article with a dated note keeping the first wording:

1. With the printed density the prediction is `A ≈ 0.0374`, not `0.038`
   (Remark 4.2): `2^{1/4} · 0.83360 · 0.0377237 = 0.03740`.
2. The Monte Carlo evidence (Remarks 4.2 and 4.5, Section 12.1 item 1, this
   guide) is replaced by the walk computation below. Two of its values were
   wrong: the conditional velocity density at 0 was "0.448 at `n = 500`"
   (the walk computation gives 0.396060, and 0.404539 at `n = 100`,
   decreasing), and `c_{(1,1)} = 0.8426` at `n = 2000` lies about 0.009 above
   the monotone sequence (0.835866 at `n = 600`, limit 0.83360).
   `0.8355` at `n = 500` was right (0.836094).
3. The paraphrase of Denisov–Wachtel's Lemma 16 omitted a factor: the limit
   is `κ h̄(u,v)`, not `h̄(u,v)`.
4. The literature paragraph now says that the misprint is in the journal
   version only (below).

Section 12.1, item 6 is re-scoped. The check also noted that the integral
defining `h⋆` converges absolutely for every `x > 0`, not only almost
everywhere; the statement is kept (true and weaker).

The decisive check was a dynamic programme of the conditioned
geometric-minus-one walk from `(1,1)` to `n = 600` (floating point on a
truncated state space, discarded mass below `10⁻⁹`, extrapolated in powers of
`n^{−1/2}`; evidence, not certification):

| Quantity | Walk, `n = 600` | Walk, extrapolated | `h⋆` | Printed display, renormalized |
|---|---|---|---|---|
| `σ√n P(V_n = 0 ∣ τ > n)` | 0.395520 | 0.390277 | 0.390276 | 0.3267 |
| `f(1)/f(0)`, `f(2)/f(0)`, `f(−1)/f(0)` | 1.0876, 0.3423, 0.0644 | 1.1280, 0.3386, 0.0717 | 1.1282, 0.3379, 0.0713 | 1.8039, 0.1797, 0.0135 |
| mean area `E[I_n/(σn^{3/2}) ∣ τ > n]` | 0.58810 | 0.57365 | 0.573587 (proved closed form) | 0.217262 |
| `n^{1/4} P(τ > n)` | 0.835866 | 0.833604 | – | – |

So `2^{1/4} c_{(1,1)} f⋆(0) ≈ 0.38689`, against `A = 0.3868892(2)` from
per-parity least-squares fits to the exact counts (`150 ≤ n ≤ 500`, two to
five correction terms in `n^{−1/2}`; even and odd agree to `10⁻⁷`).

The check did not use the write's scripts. It also downloaded the published
Denisov–Wachtel from numdam and read pp. 169–170 and 186 as rendered pages
(the Theorem 1 display is the report's (18); Remark 2; Lemma 16 with `κ`);
read GJW (2.24) in the authors' preprint of 30 August 1999 and confirmed that
it gives `h⋆`, with `κ^{−1} · 12/(π√(2π)) = K⋆` to 30 digits; recomputed the
printed mass `0.11545529600527263` (17 digits) and the printed `f(0)` (equal
to the delivered `₃F₂` value to 30 digits); re-derived Proposition 4.3(a)–(c)
by hand, its own quadrature giving mass 1 and `f⋆(0)` to 28 digits;
recomputed Remark 4.4's bounds and majorant; validated the OEIS b-files of
A345470 (`n ≤ 500`) and A351869 (`n ≤ 501`) by brute force with the full
Landau criterion (`n ≤ 12`) and its own exact big-integer half-sequence
dynamic programme (every `n ≤ 40`, every seventh `n` to 160), with no
mismatch; and confirmed the front matter's explanation of `e^{−λ}` here
against `e^{−2λ}` in a000571 (`D_500/C_500 = 0.7172086`, gap of order
`1/n`). This was a careful reading with independent computation, not a
formal verification. The write checked the mean-area identity by direct
two-dimensional quadrature at five pairs `(u,w)` (12 digits).

## What the report does not claim

Every limitation of both manuscripts is printed in place. In short:

- **No numerical value of `A`** is established: `V_DW(1/√2,1/√2)` is not
  evaluated or enclosed. The counts suggest `A ≈ 0.387`, and hence
  `V_DW ≈ 0.718`, but these are uncertified extrapolations.
- No convergence rate, higher-order counting correction, transseries or
  effective cutoff. The smooth inverse is not an integer threshold, and the
  ceiling brackets are qualitative.
- The `λ` enclosure is conditional on Kolesnik's published tail theorem.
- Sequences are counted, not tournaments or isomorphism classes. Complement
  symmetry of a sequence does not make every realization isomorphic to its
  reverse (Stockmeyer, Section 3). The convention `D_0 = 1` does not assert
  that an empty tournament is strong.
- Part I does not use Denisov–Wachtel's conditional local limit theorem (12).
- Part II draws no inference about D-finiteness or analytic continuation from
  the growth estimates.
- Finite checks prove no asymptotic statement, and there is no claim of
  publication, peer review, priority or the absence of other proofs.
- The write's identification of the density of `μ` rests on Denisov–Wachtel's
  Remark 2 and Lemma 16 with Groeneboom–Jongbloed–Wellner's (2.24), restated
  by Bär–Duraj–Wachtel. The write proves only that `h⋆` has mass 1, computes
  `f⋆(0)`, and repairs Lemma 4.1. It does not re-derive (2.24).

## Further questions, and the standing rule

Part I's Section 12.1 and Part II's Section 21, both added in the write,
collect every claim stated without proof, under Vladimir's standing rule of
4 October 2026:

- **Part I (12.1)**:
  1. Certify `A`. Re-scoped: only `V_DW(1/√2,1/√2)` is now missing.
     Evidence: `c_{(1,1)} ≈ 0.83360` from the walk computation and
     `A = 0.3868892(2)` from the counts (the Monte Carlo values were
     replaced after the independent check, dated note).
  2. Rates and corrections, including the parity correction of relative order
     about `n^{−1/2}` visible in the counts (an observation, claimed by
     neither source).
  3. A direct proof of the harmonic identity.
  4. Effective inverse brackets.
  5. Correction expansions and transseries.
  6. The density of `μ`: settled to the standard of the literature; what a
     self-contained check would need is stated. Re-scoped after the
     independent check (dated note): the comparison of `h⋆` with the
     conditioned walk is now made numerically (`f⋆(0)` to six digits, the
     mean area to `10⁻⁴`, the velocity ratios to `7·10⁻⁴`); the
     self-contained derivation remains open.
- **Part II (21)**: its three next steps, re-scoped by Part I. The endpoint
  constant is achieved by smoothing; the area-local estimate is not proved.
  Constants and parity are answered, with the numerical value open. The
  strong ratio is answered, with corrections open. D-finiteness is not
  addressed.

**Wrong claim, kept on record (Remark 4.2).** The density displayed in
Denisov–Wachtel's Theorem 1 is not a probability density: its mass is
`0.11545529600527263025…`, proved by an elementary integral. The x- and
y-integrals of the kernel give `erf(w√(3/(2(1−s))))`, and the rest is a
two-dimensional quadrature. Part I's (18) copies it with the printed constant,
and Part II's (76) copies it up to an unspecified `c_0`. Consequently Part I's
(22), `f_Y(0) = 0.0377237…`, is not the velocity marginal of `μ`, and Part I's
(6) evaluated with it would give `A ≈ 0.0374`. The independent check's walk
computation gives `n^{1/4} P_{(1,1)}(τ > n) = 0.835866` at `n = 600`,
extrapolating to `c_{(1,1)} ≈ 0.83360`, while the exact counts give
`C_n n^{3/4} 2^{−n} = 0.3762, 0.3989` at `n = 320, 321` and `A ≈ 0.387`
(`0.3868892(2)` by parity fits; uncertified extrapolation). The corrected
value predicts `A = 2^{1/4} c_{(1,1)} f⋆(0) ≈ 0.38689`. The statements stay
printed as delivered, with the correction beside them. (Dated note,
5 October 2026: this paragraph first read "would give `A ≈ 0.038`", cited
"the placement's Monte Carlo" with `c_{(1,1)} = 0.8355` at `n = 500` and
`0.8426` at `n = 2000`, and predicted "`≈ 0.388–0.391`"; the value at
`n = 2000` was about 0.009 too large.)

- **Unaffected**: the existence of one amplitude for both parities;
  `D_n/C_n → e^{−λ}` and the `λ`, `r` enclosures; the harmonic identity
  (`f_Y(0)` cancels); the inverses and Corollary 10.2; every upper bound of
  both Parts; Part II's theorem and monotonicity.
- **Conditional on the density's shape**, and settled by the write: Part I's
  Lemma 4.1 (and through it Theorem 6.1 and the equivalents), the rectangle of
  Lemma 9.1, and Part II's lower bound in Section 16.2. All three hold for the
  corrected density.
- **Literature** (searched 5 October 2026): no erratum to Denisov–Wachtel was
  found. Bär–Duraj–Wachtel (Ann. Appl. Probab. 33 (2023); read as
  arXiv:2007.13211v1) print GJW's `h̄` with the factor `p_s(0,w;0,0)` and use
  it for the meander density, consistent with the correction, but they do not
  comment on the display. GJW was read in the authors' preprint of
  30 August 1999, whose equation numbers match Denisov–Wachtel's citation.
  The misprint is in the journal version (AIHP 2015) only:
  arXiv:1207.2270v1, the only arXiv version, states Theorem 1 with a
  different density, `C h(x,y) g_1(0,0;x,y)`, with no explicit integral;
  whether that form is correct was not tested (added after the independent
  check). Denisov–Wachtel's Lemma 16 reads
  `p̄_1(x,y;u,v)/h(x,y) → κ h̄(u,v)`; the write's first paraphrase omitted
  `κ` (corrected, dated note).

## Relation to neighbouring reports

`a000571-tournament-score-sequences` (same directory) treats ordinary score
sequences. It is a sibling, not the host: no question or theorem is in common,
and the methods differ (singularity analysis there, exit times of integrated
walks here). Its `λ = 0.3302375439859293` is this report's `λ`. Part I's
`T_k`, `S_k` are its `I_k`, `S_k`, and `r = e^{−λ} = 1 − I(1/4)` in its
notation; its value lies inside Part I's certified enclosure.

The strong fraction is `e^{−λ}` here but `I_n/S_n → e^{−2λ}` there. There,
`S = e^A` and `I = 1 − e^{−A}` are both transforms of one singular series, so
`S_n ~ e^{λ}[zⁿ]A` and `I_n ~ e^{−λ}[zⁿ]A`. Here
`D(z) = C(z)e^{−A(z²)}`: the factor `C` (order `2ⁿn^{−3/4}`) dominates, and
the summable multiplier contributes only its value `e^{−λ}`. Part I's Lambert
inverse is the same mechanism as a000571's `tss:eq:lambert`.

a000571's sentence "No other report of the repository treats tournament score
sequences …" (its article, Part I write note, and the batch-85 note) becomes
incomplete with this report. A dated reciprocal note there is a separate
commit; this write edits no other report. No other report treats A345470,
A351869, integrated random walks or the Denisov–Wachtel exit-time theorem
(searched 5 October 2026).

## Relation to the formal project

Placement in the collection confers no formal status, and no statement of this
report is formalized. No Lean or Rocq file in the repository mentions
tournament score sequences, A345470 or A351869 (searched 5 October 2026).

## Delivery names, renames and discrepancies

- Every staged delivered file keeps its bytes. All 27 staged files were
  checked against fresh extractions of the arrival archives at the write, with
  0 differences. Only names changed (tables at the end). The delivered code
  and markdown use delivery paths (`checks/…`, `replay.py`, `manifest.json`,
  `report11N.tex`, `report11N.pdf`, `README.md`), which are shipped under other
  names or not at all. **None of the scripts runs in this directory**:
  `replay.py` first verifies the sealed package against `manifest.json` (not
  shipped), and `validate.py` reads `fixtures.json` beside itself.
- **CRLF on Windows.** Python on Windows writes CRLF to standard output and
  through `Path.write_text`, so a bare rerun of `replay.py` on Windows fails
  ("exact results differ"). At placement, 294 lines of 114's mutation results
  differed only in SHA-256 values of CRLF mutant files. This is a platform
  artifact, not a defect: with the LF shim below both replays pass byte for
  byte.
- **In-place writes.** `validate.py --output PATH` and the mutation campaigns
  write files. The delivered guides warn against writing into the sealed
  package, whose strict manifest rejects extra files. Run everything on a copy.
- **Sandbox paths.** The delivered README and `.tex` examples write to
  `/tmp/…`, and the integrity tests use the attack string `/tmp/outside.txt`.
  Use a scratch directory outside the repository.
- **The delivered density checks.** `116-leading-checks-reader_validation.md`
  ("Universal marginal-factor expression", "dominating s power is 3/4") and
  `data/116-leading-checks-results.json` (`outer_s_power`, the `f_Y(0)`
  formula) verify the algebra of the printed display. They cannot detect its
  misprint (Remark 4.2). Report 114's "Gaussian density-ratio algebra" check
  is the same for the printed and the true density.
- The delivered `README.md` of Report 116, staged at placement, promised
  `report116.pdf` and `manifest.json`, which are not shipped; it is replaced
  by this guide.

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. Recreate the
delivered layout from the arrival commit:

```
git show 60f54ea06:docs/incoming/Self_Complementary_Tournament_Scores_Leading_Constants_and_Inverses_Source.zip > s116.zip
git show 60f54ea06:docs/incoming/Self_Complementary_Tournament_Scores_Growth_and_Inverse_Source.zip > s114.zip
mkdir r116 r114 && unzip -q s116.zip -d r116 && unzip -q s114.zip -d r114
cd r116/report116 && python3 replay.py          # POSIX: manifest, checks, mutations, attacks, normal and -O
cd ../../r114/report114 && python3 replay.py
```

On Windows, put this `sitecustomize.py` in a directory **outside** the package
and set `PYTHONPATH` to that directory (and `PYTHONDONTWRITEBYTECODE=1`, since
the strict manifest rejects `__pycache__`). Then use `py` instead of `python3`:

```python
# POSIX-newline emulation for running the delivered suites on Windows (copy only).
import sys, pathlib, builtins
sys.stdout.reconfigure(newline="\n")
_orig_wt = pathlib.Path.write_text
def _wt(self, data, encoding=None, errors=None, newline=None):
    return _orig_wt(self, data, encoding=encoding, errors=errors,
                    newline="\n" if newline is None else newline)
pathlib.Path.write_text = _wt
_orig_open = builtins.open
def _open(file, mode="r", buffering=-1, encoding=None, errors=None, newline=None, *a, **k):
    if "b" not in mode and ("w" in mode or "a" in mode or "x" in mode) and newline is None:
        newline = "\n"
    return _orig_open(file, mode, buffering, encoding, errors, newline, *a, **k)
builtins.open = _open
```

For the exact arithmetic alone, `py checks/validate.py --output ../../v116.json`
(and the same in `report114`) writes the result outside the package. Compare
it with `checks/results.json`, which is `data/11N-…-checks-results.json` here.

Results:
- **At placement** (5 October 2026, on copies with the shim, recorded in the
  batch-103 dossier): both replays passed, with all regenerated outputs
  byte-identical to the delivered ones. Report 114: manifest of 16 files,
  37 named mutants with 74 rejected runs, 17 integrity mutants, normal and
  `-O`, 2 min 12 s. Report 116: 49 named mutants with 98 rejected runs and
  17 integrity mutants, 3 min 7 s. Without the shim both fail on CRLF only.
- **At the write** (5 October 2026, Python 3.14.4, Windows, fresh
  extractions): `checks/validate.py --output` with the shim reproduced both
  `checks/results.json` files byte for byte, in about 2 s (116) and 3 s (114).
  Without the shim, Report 114's output differs, by CRLF.
- `--build-pdf` was not run. Byte identity needs the recorded TeX Live
  2025/dev toolchain (`data/11N-…-build-environment.txt`), and MiKTeX cannot
  reproduce the bytes.

## Rights

Repository contents are MIT-0. The sequence terms in the article and data are
OEIS data or coincide with it. Report 114's fixtures carry 35 terms of
A345470 and 39 of A351869, retrieved from the OEIS on 2 October 2026. Report
116's fixtures copy them from Report 114's exact enumeration, with ordinary
score counts (A000571) computed by its checker. OEIS data are available under
CC BY-SA 4.0 ([OEIS license](https://oeis.org/LICENSE)). The OEIS entries are
credited for the sequences. Credited elsewhere: Stockmeyer for the families,
the Landau criteria and the convolution identities; Kolesnik and
Bassan–Donderwinkel–Kolesnik for the ordinary asymptotics and `λ`;
Denisov–Wachtel for the exit-time theorem; Groeneboom–Jongbloed–Wellner for
the limit density; Bär–Duraj–Wachtel for its restatement. No source PDF is
bundled, and nothing was submitted to the OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy; commit only `article.pdf`. The write's
build (5 October 2026) has 41 pages and no errors. It has no undefined or
multiply defined references or citations, no duplicate destinations, and no
overfull or underfull boxes. The log carries one "Infinite glue shrinkage
found in box being split" message, from the notation longtable breaking across
a page, as in other reports with longtables. Builds of the delivered
`report116.tex` (14 pages) and `report114.tex` (11 pages) had one underfull box
(116's bibliography) and an amsmath `\atopwithdelims` warning (114's
`\choose`). The ragged-right bibliography and `\binom` remove both here.

Rebuilt on 5 October 2026 after the independent check, in a scratch copy with
four pdfLaTeX passes: 43 pages (was 41). No errors, no undefined or multiply
defined references or citations, no duplicate destinations, and no overfull
or underfull boxes; the longtable's infinite-glue message no longer occurs.
The `.aux` files of the committed and the new text agree on all 128 label
numbers and all 9 citations; no label was added. The changed pages (4, 15,
18–19, 28–30, 43) were rendered and inspected.

## Delivered path → shipped path

Report 116 (`116-leading-`; base):

| Delivered | Shipped |
|---|---|
| `report116.tex` | `article.tex` (Part I) |
| `README.md` | replaced by this guide |
| `checks/reader_validation.md` | `116-leading-checks-reader_validation.md` |
| `build_pdf.py`, `integrity.py`, `integrity_tests.py`, `make_archive.py`, `replay.py` | `code/116-leading-<name>` |
| `checks/validate.py`, `checks/mutation_campaign.py` | `code/116-leading-checks-<name>` |
| `checks/fixtures.json`, `checks/results.json`, `checks/mutation_results.json` | `data/116-leading-checks-<name>` |
| `build-environment.txt`, `integrity_results.json` | `data/116-leading-<name>` |
| `report116.pdf`, `manifest.json` | not shipped |

Report 114 (`114-growth-`):

| Delivered | Shipped |
|---|---|
| `report114.tex` | not shipped; printed as Part II of `article.tex` |
| `checks/reader_validation.md` | `114-growth-checks-reader_validation.md` |
| `build_pdf.py`, `integrity.py`, `integrity_tests.py`, `make_archive.py`, `replay.py` | `code/114-growth-<name>` |
| `checks/validate.py`, `checks/mutation_campaign.py` | `code/114-growth-checks-<name>` |
| `checks/fixtures.json`, `checks/results.json`, `checks/mutation_results.json` | `data/114-growth-checks-<name>` |
| `build-environment.txt` | `data/114-growth-build-environment.txt` |
| `README.md`, `report114.pdf`, `manifest.json`, `integrity_results.json` (byte copy of 116's) | not shipped |

## Provenance

Two manuscripts (bundle Reports 116 and 114) were merged into one report, with
116 as the base. Arrival `60f54ea06`, placement `9c995cefe`, write batch 103
(5 October 2026). Neither manuscript pins a ProveIt commit. The merge choices
are listed in the article's front matter, "Provenance and merge decisions":
the base and the order, the union with second routes, the density correction,
the typography (`\binom`, title, running heads, merged bibliography with three
added entries) and the package text. An independent adversarial check of the
write followed the same day; its outcome is recorded in the article (dated
notes and the paragraph at the end of Section 12.1) and in this guide.
