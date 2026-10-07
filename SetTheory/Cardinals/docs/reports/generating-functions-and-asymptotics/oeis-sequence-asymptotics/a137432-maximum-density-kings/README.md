# Maximum-Density Kings on Cylinders and Planes

**OEIS A137432, A061593 and A061594: the aspect-ratio transition at `w/h = log 2` for kings on a cylinder, with uniform asymptotics, a critical window, limit laws and inverse brackets; every fixed order on the square cylinder, the exact third coefficient and the ratio expansion that proves the A137432 conjecture; degree and pole-order bounds for the planar board, Wilf's dominant term and a Lambert-W threshold bracket; three of Kotěšovec's 2011 conjectures settled in whole or in part**

This is a research report built on 6 October 2026 (write batch 109) from three
manuscripts of one external research session, Reports 174, 173 and 175 of the
session bundle of Reports 1–243, all dated 3 October 2026. A placement of `hw`
mutually nonattacking kings on a `2h × 2w` board of labelled squares is a
maximum-density placement: each of the `hw` disjoint `2 × 2` blocks holds
exactly one king. Write `A(h,w)` for the number of such placements when the
`2h` rows are open and the `2w` columns cyclic, `a_n = A(n,n)` for the square
cylinder ([A137432](https://oeis.org/A137432)), and `P_h(w)` for the ordinary
board ([A061593](https://oeis.org/A061593) at `h = 2`,
[A061594](https://oeis.org/A061594) at `h = 3`).

- **Part I** (Report 174, the base): for `w/h` in a compact positive interval,
  `A(h,w) = S(h,w)(1 + O(1/h))` with an explicit marked-star sum `S`; the free
  energy `Φ(λ)` with a transition at `λ = log 2`; the subcritical equivalent
  `h^{w+3/2} B(λ_h) e^{hΦ(λ_h)}`; above the transition every fixed order
  `A = h^w C(λ_h)(Σ c_j(λ_h) h^{−j})`, `C(λ) = 2e^λ F(e^{−λ})²`,
  `F(q) = (1−q)/(1−2q)`, with explicit `c_1`, `c_2`; the critical window
  `A/h^w = hG(t) + √h H(t) + J(t) + O(h^{−1/2})`; three limit laws (finite,
  Rayleigh-type and linear defect); floor corrections; Lambert-W first-crossing
  brackets along rational rays; and, at fixed height, squarefree denominators,
  every irreducible factor of degree at most `⌊h/2⌋ + 1`, equality at the
  heights `h = p − 3`, and small closed forms.
- **Part II** (Report 173): `a_n = C n^n (Σ_{j≤M} c_j n^{−j} + O(n^{−M−1}))`
  with `C = 2e(e−1)²/(e−2)² = 31.11168357204905…` (Kotěšovec's constant) and
  `c_j ∈ Q(e)`, the exact `c_1 = −13.57205215904638…`,
  `c_2 = 576.33175529505071…`, `c_3 = −32709.35316578946…`; a boundary law with
  total-variation rate `O(1/n)`; the ratio expansion
  `a_{n+1}/(n a_n) = e(1 + 1/(2n) + (−c_1 − 1/24)/n² + O(n^{−3}))`, which proves
  the OEIS conjecture that this ratio tends to `e`; and an integer bracket for
  the threshold.
- **Part III** (Report 175): every irreducible factor of the reduced
  denominator of `F_h(z) = Σ_{w≥1} P_h(w) z^w` has degree `d ≤ ⌊h/2⌋ + 1` and
  exponent at most `h − 2d + 3` (entrywise for the transfer resolvent), so for
  even `h` the top-degree factors are simple; an exponential-polynomial formula
  with degree bounds; Wilf's dominant term `(α_h w + β_h)(h+1)^w` with
  `α_h ≥ 1`; a Lambert-W inverse with an exponentially small real error and a
  two-ceiling threshold bracket; all-width generating-function certificates
  through `h = 6`.
- **Added by the write**: the front matter; **Remark 20.1**, a proof that
  `2(h+1)^w ≤ A(h,w) ≤ 2^h (h+1)^w` for all `h, w ≥ 1`, with equality in the
  upper bound exactly when `h = 1` or `w = 1` and in the lower bound exactly
  when `h = 1` (so the strict upper bound for `a_n` that Part II reads in
  Kotěšovec's book holds exactly for `n ≥ 2`); **Remark 25.2**, a proof that
  the dominant planar factor `1 − (h+1)z` has exponent exactly two at every
  height; the check that Part I's `c_1(1)`, `c_2(1)` are Part II's `c_1`, `c_2`;
  the classification of the inverses against the transseries volume; dated
  notes; Section 31.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Aspect ratio transition for cylindrical kings: Uniform asymptotics and inverse thresholds for maximum density rectangles* (empty author line; title block "Report 174", 3 October 2026); the base | 174 | `Rectangular_Kings_Aspect_Ratio_Transition_Source.zip` (477,514 bytes, 13 files in the wrapper `Report174/`; `Report174.tex`, 805 lines, 22 pp.) | none | `f7e9e5c2f` | Part I, Sections 1–10 and Appendices A–C |
| *Maximum density kings on a cylinder: All fixed order asymptotics and inverse thresholds for A137432* (empty author line; title block "Report 173", 3 October 2026) | 173 | `Cylindrical_Kings_All_Order_Asymptotics_and_Inverses_Source.zip` (523,435 bytes, 23 files; `Report173.tex`, 627 lines, 17 pp.) | none | `f7e9e5c2f` | Part II, Sections 11–21, plus the write's Remark 20.1 |
| *Planar Maximum Density Kings: Factor degree and pole multiplicity with fixed height asymptotics and inverses* (author line "Research report 175", 3 October 2026) | 175 | `Planar_Kings_Pole_Bounds_and_Inverses_Source.zip` (546,797 bytes, 21 files; `report.tex`, 489 lines, 13 pp.) | none | `f7e9e5c2f` | Part III, Sections 22–30, plus the write's Remark 25.2 |

All three archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `f7e9e5c2f` (batch 109, cluster 109-KINGS) removed them from
`docs/incoming/`. The write is "Write batch 109 (a137432-maximum-density-kings):
new report, maximum-density king placements on cylinders and planes".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. Report 175's code provenance says it was "prepared 2026-10-03
with OpenAI assistance"; Reports 173 and 174 name no author or tool. No
manuscript carries "prepared for private review" wording (intake search of the
text files, PDF metadata and PDF text). Every result, proof, remark, question
and limitation of the three manuscripts is printed.

## Why the Parts are in this order

The order follows dependency. Report 174 is the base and Part I: it contains
Report 173's main theorem as the case `λ = 1` of its supercritical theorem
(Theorem 1.2), and it answers the question about rectangular cylinders with
which Report 173 ends. Report 173 is Part II: its own uniform proof is a second
route, and only it has the exact `c_3` and the ratio expansion that proves the
A137432 conjecture. Report 175 is Part III: it reuses the component-incidence
Gram factorization of Parts I and II on the planar board ("reused from
companion cylindrical analysis"), and with Part I's Appendix A it splits one
family of Kotěšovec's conjectures between the cylinder and the plane. The
manuscripts were written in the order 173, 174, 175 within about 80 minutes on
3 October 2026; Report 174 says that "No reading of an earlier square report is
needed", and none cites another in its bibliography. Two separate reports
(cylinder; plane) were considered at intake and not taken.

## Files

The directory holds 48 files: 7 at the root, 23 in `code/`, 18 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 174, prefix `174-aspect-`** (9 files): `code/`: the companion
(verification runner, independent geometric/trace/integer checks, exact
symbolic checks) and the package tools (build, verify, shared helpers, their
tests); `data/`: the recorded verification and build information.

```
code/174-aspect-build_package.py
code/174-aspect-companion-exact_checks.py
code/174-aspect-companion-run_checks.py
code/174-aspect-companion-symbolic_checks.py
code/174-aspect-package_tools.py
code/174-aspect-test_package_tools.py
code/174-aspect-verify_package.py
data/174-aspect-build_info.json
data/174-aspect-verification.json
```

**Report 173, prefix `173-square-`** (19 files): the companion's README and
the source notes; `code/`: the companion (exact counts, coefficient
certificates, residuals, the optional SymPy all-orders engine, rebuild and its
manifest check, the runner) and the package tools; `data/`: the term fixture
and the recorded default, optimized, build and residual outputs.

```
173-square-companion-README.md
173-square-sources-REFERENCES.md
code/173-square-build.py
code/173-square-companion-coefficient_certificates.py
code/173-square-companion-exact_counts.py
code/173-square-companion-rebuild.py
code/173-square-companion-residuals.py
code/173-square-companion-run_checks.py
code/173-square-companion-symbolic_all_orders.py
code/173-square-companion-verify_manifest.py
code/173-square-test_build.py
code/173-square-verify_package.py
data/173-square-companion-fixtures-a137432_selected.json
data/173-square-generated-BUILD_INFO.json
data/173-square-generated-build_checks.json
data/173-square-generated-build_checks_optimized.json
data/173-square-generated-checks.json
data/173-square-generated-checks_optimized.json
data/173-square-generated-residuals.json
```

**Report 175, prefix `175-planar-`** (17 files): the code README and the source
notes; `code/`: the standard-library verifier, the corruption guard tests, the
optional SymPy regeneration and the build tools; `data/`: the exact
generating-function certificates through `h = 6` and the recorded default,
extended, guard, regeneration and build outputs.

```
175-planar-README_CODE.md
175-planar-SOURCES.md
code/175-planar-build.py
code/175-planar-guard_tests.py
code/175-planar-regenerate.py
code/175-planar-test_build.py
code/175-planar-verify.py
code/175-planar-verify_manifest.py
data/175-planar-data-certificates.json
data/175-planar-data-default_results.json
data/175-planar-data-guard_results.json
data/175-planar-data-regeneration_results.txt
data/175-planar-data-verified_results.json
data/175-planar-generated-BUILD_INFO.json
data/175-planar-generated-build_guards.json
data/175-planar-generated-verification.json
data/175-planar-generated-verification_guards.json
```

Three pairs are equal by design and both are kept as delivered records: Report
173's `checks.json` = `checks_optimized.json` and `build_checks.json` =
`build_checks_optimized.json` (normal and `-O` runs), and Report 175's
`data/…default_results.json` = `generated/…verification.json`.

**Not shipped** (all retrievable from `60f54ea06`): the three PDFs;
`Report173.tex` and `report.tex` (printed as Parts II and III) and the
delivered top-level `README.md` of Reports 173 and 175 (Report 174's was staged
and is replaced by this guide); the checksum manifests (Report 173
`SHA256SUMS.json`, 22/22; Report 174 `manifest.json`, 12/12, which lists only
bytes and SHA-256; Report 175 `SHA256SUMS.json`, 20/20; all verified at
placement; repository policy drops checksum manifests).

## Labels and numbering

Label prefix **`mdk:`** (none at HEAD before this report): Part I uses
`mdk:asp:` (Report 174's 95 labels), Part II `mdk:sq:` (Report 173's 64),
Part III `mdk:pl:` (Report 175's 42). Twenty-seven bare names occur in two or
three manuscripts (`eq:M`, `eq:gram`, `eq:C`, `eq:schur`, `eq:implicit`,
`eq:cauchy`, `sec:tree`, `sec:inverse`, `eq:Lambert`, `thm:inverse`,
`sec:checks`, `sec:sources`, …); under the Part prefixes they are distinct. The
write added the three Part labels `mdk:asp:part`, `mdk:sq:part`, `mdk:pl:part`;
Remark 20.1's `mdk:sq:rem:book-bounds` and Remark 25.2's
`mdk:pl:rem:linear-exponent`; `mdk:pl:rem:source` for the delivered Remark
25.1; eight section labels of Part III, `mdk:pl:sec:scope`, `…:gram`,
`…:chains`, `…:exppoly`, `…:dominant`, `…:lambert`, `…:verification`,
`…:remaining` (Report 175 labelled only its Section 2, `sec:transfer`); the
front matter's `mdk:sec:guide`, `…:status`, `…:oeisconj`, `…:book`, `…:oeis`,
`…:inverses`, `…:notation`, `…:provenance`, `…:trust`, `…:neighbours`; and
Section 31's `mdk:sec:further` with the twelve items `mdk:q:smallratio`,
`mdk:q:window`, `mdk:q:effective`, `mdk:q:subcritical`, `mdk:q:degree`,
`mdk:q:lowdeg`, `mdk:q:cancel`, `mdk:q:uniform`, `mdk:q:largeorder`,
`mdk:q:history`, `mdk:q:book`, `mdk:q:data`. 238 labels in all, all distinct
(201 delivered, 37 added).

| Part | Manuscript | Section here | Statements | Equations |
|---|---|---|---|---|
| I | Report 174 | 1–10 and A–C, unchanged | unchanged | unchanged |
| II | Report 173 | `k + 10` (11–21) | `(k + 10).j`; Remark 20.1 added | `(k + 10).j` |
| III | Report 175 | `k + 21` (22–30); 31 added | `(k + 21).j`; Remark 25.2 added | unchanged, (1)–(31) |

Report 174 and Report 173 number statements and equations within sections;
Report 175 numbers statements within sections but equations consecutively
through the manuscript, and Part III keeps its equation numbers (an equation
number without a dot belongs to Part III). So Report 173's Theorems 1.1, 1.2
and Corollary 1.3 → **11.1, 11.2, 11.3**, Remark 2.1 → **12.1**, Lemmas 3.1,
3.2 → **13.1, 13.2**, Lemmas 4.1, 4.2 → **14.1, 14.2**, Proposition 7.1 →
**17.1**, equations (1.1)–(8.3) → (11.1)–(18.3); Report 175's Theorem 1.1 and
Corollary 1.2 → **22.1, 22.2**, Lemma 2.1 → **23.1**, Lemmas 3.1, 3.2 →
**24.1, 24.2**, Remark 4.1 → **25.1**, Theorem 5.1 → **26.1**, Lemma 6.1 and
Theorem 6.2 → **27.1, 27.2**, Theorem 7.1 → **28.1**, Table 1 → Table 1. A
comparison of the build's `.aux` with separate builds of the three delivered
`.tex` files (22, 17 and 13 pages, no warnings) confirmed all 201 delivered
labels under these offsets and prefixes. The delivered READMEs, code and data
use the manuscripts' own numbers.

## Notation

No delivered symbol was renamed. The front matter's "Notation across the three
Parts" lists every letter whose meaning changes, with the tempting false
readings, and each Part opens with a short reading-conventions table. The main
collisions: **`c_j`** is a threshold (the row offset changes in block column
`j`) in the encodings of Parts I and II and an asymptotic coefficient
elsewhere; **`q`** is `e^{−λ}` (Part I), the ray denominator (Part I, Section
10), `e^{−1}` (Part II) and the Hamming weight `|b|` (Part III); **`n`** is the
board size in Part II, a ray index in Part I and `h + 1` in Part III; **`e`**
is Euler's number in Parts I–II and a factor exponent in Part III; **`L`** is
`log 2` (Part I), `log(x/C)` (Part II) and a recurrence onset (Part III);
**`h`** is the height, but `k + 1` in Part II's Section 15; **`d`, `D`**
(several meanings in each Part); **`N`** (a Lambert value in Parts I–II, the
number of states `(h+1)2^h` in Part III); **`S`, `T`, `R`, `C`, `F`, `G`,
`H`, `J`, `K`, `B`, `α`, `β`, `ρ`, `η`, `t`, `u`, `v`, `x`, `y`**. Part III
writes `a_{i,j}`, `b_{i,j}` for the row and column offsets that Parts I and II
call `x_{ij}`, `y_{ij}`. Identifications: Part I's `A(n,n)`, `C(1)`, `c_j(1)`,
`R_i(z)`, `𝓗_1` are Part II's `a_n`, `C`, `c_j`, `G_i(z)`, `H`; Part III's
`X_0`, `X_1`, `C` are Part I's `R_0`, `R_1`, `C_b`. The transseries volume's
symbols are subscripted `vol` where they meet these.

## What the report claims

**Part I (Report 174).**
- Theorem 1.1 (uniform marked-star approximation), Theorem 1.2 (free energy,
  transition at `log 2`, subcritical equivalent, every fixed order above, with
  `c_j ∈ Q(λ, e^{−λ})`), Theorem 1.3 (critical window, with the endpoint
  `29/12` and the spectral `4LG(t)`); Sections 2–3 (encoding, `M_b = E_0E_1`,
  Gram and tree traces, caterpillar, norm and Schur bounds), 4 (Lemma 4.1 and
  the proof of Theorem 1.1), 5 (subcritical evaluation), 6 (localization,
  analytic remainder, the finite coefficient procedure, explicit `c_1`, `c_2`),
  7 (the critical expansion; `G(0) = 1/log 2`, `H(0)`, `J(0)` in closed form).
- Theorems 8.1–8.3 (finite defect with total-variation rate `O(1/h)`;
  square-root defect with density `x e^{−tx−Lx²/2}/G(t)`, Rayleigh at `t = 0`;
  Gaussian run in the subcritical regime); Section 9 (floor corrections);
  Theorem 10.1 (integer first-crossing bracket along rational rays) and
  Section 10.1 (higher order).
- Appendix A: squarefree fixed-height denominators (Kotěšovec's Conjecture 1),
  the degree bound `⌊h/2⌋ + 1` (upper half of Conjecture 2, cylinder),
  equality at `h = p − 3`, `A(h,w) ~ 2(h+1)^w` (prior, p. 192). Appendix B:
  the table `1 ≤ h ≤ 6`, `1 ≤ w ≤ 6`, the closed forms (B.1)–(B.4).

**Part II (Report 173).**
- Theorem 11.1 (every fixed order; second route: Part I at `λ = 1`), Theorem
  11.2 (boundary law; second route: Part I's Theorem 8.1 at `λ = 1`),
  Corollary 11.3 (ratio expansion, eventual monotonicity, integer bracket).
- Sections 12–14 (encoding, factorization, caterpillar, Schur complement,
  spectral remainder), 15 (uniform tails, the analytic disk with explicit
  radii), 16 (resolvent recursion, the finite algorithm, exact `c_1`, `c_2`,
  `c_3`, the shorter form for `c_1`, `c_2`), 17 (Proposition 17.1, the law),
  18 (ratio, Lambert inverse, the bracket).

**Part III (Report 175).**
- Theorem 22.1 and Corollary 22.2 (degree and exponent bounds; Conjecture 4;
  upper half of Conjecture 2, planar); Lemmas 23.1, 24.1, 24.2 (the planar
  transfer, the Gram factorization, simple diagonal poles); Section 25 (the
  Boolean-chain proof; the `h = 3` cancellation (15); Remark 25.1);
  Theorem 26.1 (exponential-polynomial formula); Lemma 27.1 and Theorem 27.2
  (Wilf's dominant term, `α_h ≥ 1`; `F_1`, `F_2`, `F_3`; `(α_h, β_h)` for
  `h ≤ 4` printed, through `h = 6` in the data); Theorem 28.1 (inverse and
  bracket) and (30) (the first subdominant correction); Section 29 (the
  all-width Cayley–Hamilton certificate and the bounded checks).

**Added by the write** (all marked `[write]`, dated 6 October 2026): the front
matter; the dated notes; Section 31; and two remarks with proofs.
- **Remark 20.1.** For every word `b`, `tr(M_b^w) = Σ x_i^w` over the
  eigenvalues of `C_b C_bᵀ`, whose sum is the number `h + 1` of unit entries of
  `C_b`; so `tr(M_b^w) ≤ (h+1)^w`, with equality for `w ≥ 2` exactly when
  `C_b` has rank one, that is when `b` is constant. Summing gives
  `2(h+1)^w ≤ A(h,w) ≤ 2^h (h+1)^w` with the stated equality cases; for the
  square, `2(n+1)^n ≤ a_n` for all `n ≥ 1` and `a_n < 2^n (n+1)^n` exactly for
  `n ≥ 2` (`a_1 = 4`). Checked against `a_1, …, a_10`.
- **Remark 25.2.** The pole of `F_h` at `1/(h+1)` comes only from the two
  constant-word blocks, each a simple pole, visited at most once by a strict
  Boolean chain, so its order is at most two, and the proof of Theorem 27.2
  gives `lim (1−(h+1)z)² F_h(z) ≥ 1`: the factor `1 − (h+1)z` has exponent
  exactly two at every height. (Qualified after the independent check of 7
  October 2026: this is a reading of Theorem 27.2, Wilf's dominant term with
  `α_h ≥ 1`, which already forces exponent two; the remark adds no new
  result.)

## Kotěšovec's book and the OEIS conjecture

**The A137432 conjecture** (entry read 6 October 2026, internal format and
revision history). The formula line "Conjecture: limit of a(n+1)/(n*a(n)) as
n->infinity is e." is unsigned; it is in revision #19, the entry's first
version under its present name, made by Vaclav Kotesovec on 31 August 2011
(the entry's author line: "Vaclav Kotesovec, Aug 31 2011"). **Proved** by
Part II's Corollary 11.3; only the leading equivalent is needed for the limit.
The entry's "a(n) ~ c * n^n" with `c = 2e(e−1)²/(e−2)²` ("Vaclav Kotesovec, Jul
29 2023, updated Mar 18 2024") is proved with every fixed order by Parts I and
II; its 46 printed decimals are correct (70-digit evaluation).

**The book.** All three Parts cite V. Kotěšovec, *Non-attacking Chess Pieces*,
sixth edition, 2013 (author's PDF). **The write did not read it, and neither
did the intake** (a large download, not fetched without Vladimir's
permission); page numbers and statements below are the Parts'. Report 173's
source notes say the pages "were rendered and independently inspected".

| p. 83 (Parts' description) | Status |
|---|---|
| Conjecture 1 (29 August 2011, per Part I): squarefree cylinder denominators; Alekseyev's checks through `h = 20` | proved, Part I, Appendix A (no first-proof claim) |
| Conjecture 2 (15 September 2011, per Part I): maximal irreducible degree `⌊h/2⌋ + 1`, planar and cylindrical | upper bound proved for the cylinder (Part I, (A.2)) and the plane (Part III, Theorem 22.1); equality on the cylinder at `h = p − 3`; equality at every height open for both |
| Conjecture 3 (planar exponents, per Part III) | not settled; Part III's Remark 25.1: the page prints `⌊(h+1)/2⌋` while listing exponent 2 at `h = 1, 2`; the exponents are confirmed (Remark 25.2; `F_1`, `F_2`; A061593); recorded as an inconsistency of the page as Part III reports it, not as a refutation |
| Conjecture 4 (planar): even `h`, top-degree factors simple | proved, Part III, Corollary 22.2 (no first-proof claim) |

Other pages the Parts cite: pp. 82–83, 169–196 (Section 2.6), 178 (Alekseyev's
2011 factor-generation method and an `h + 1` degree bound), 178–180, 192 (the
fixed-height law), 193, 209–210 (Part I); 209–210 (Part II); 82–90 and 178
(Part III). **Recorded as Part II states it:** the strict upper bound
`a_n < 2^n (n+1)^n` of pp. 209–210 fails at `n = 1`, where `a_1 = 4` is
equality; the arithmetic is right, and the write's Remark 20.1 proves the bound
for every `n ≥ 2` together with the lower bound `2(n+1)^n ≤ a_n`. Neither Part
recovered Alekseyev's 2011 argument or the Zealint discussion, and both
disclaim priority.

## The OEIS entries and the fixture

- **A137432**: data `a(0), …, a(18)`; b-file "Rintaro Matsuo, Table of n, a(n)
  for n = 0..384 (terms 1..31 from Alex V. Breger)"; a separate file "Rintaro
  Matsuo, a(1)..a(800)" (`a137432.txt`). Part II's counts `a_1, …, a_10` and
  Part I's table diagonal agree with the entry.
- **The fixture discrepancy (disclosed).**
  `data/173-square-companion-fixtures-a137432_selected.json` holds
  `a_1, …, a_10, a_100, a_200, a_400, a_800` and names as its `source_url` the
  OEIS b-file `https://oeis.org/A137432/b137432.txt` (with a SHA-256 and the
  date 2026-10-03). The live b-file stops at `n = 384`, so `a_400` and `a_800`
  cannot come from it; Report 173's text and `173-square-sources-REFERENCES.md`
  attribute the large terms to Matsuo's table through `n = 800` (GitHub
  `b137432.txt`), and the entry also links Matsuo's `a(1)..a(800)` file. The
  field therefore names the wrong file for the two largest terms, unless the
  b-file was longer on 3 October; which file the recorded SHA-256 belongs to
  was not determined (the write fetched neither). (Added after the
  independent check of 7 October 2026, which fetched all three files: the
  recorded SHA-256 `a05d926f…ced88` is that of Matsuo's GitHub table
  `b137432.txt`, `n = 1, …, 800`, and the entry's `a137432.txt` is
  byte-identical to it; the b-file has another hash and agrees with the table
  on `1 ≤ n ≤ 384`; all fourteen fixture terms equal the table's entries. Only
  the `source_url` names the wrong file.) The write's only check of the
  large terms is indirect: the residuals `R_2(n)`, `R_3(n)` recomputed from the
  fixture reproduce Part II's printed `R_2(800) = 538.86987220110762…` and
  `R_3(800) = −29969.50647515447…`, and `R_2 = 381.7, 455.3, 507.0, 538.9` at
  `n = 100, 200, 400, 800` approach `c_2 + c_3/n = 249.2, 412.8, 494.6, 535.4`.
  Consistent with the terms; not a verification of them.
- **A194644, A194647, A195656** (the fixed-height cylinder rows `h = 2, 5, 12`
  of Part I): the first six terms of A194644 and A194647 agree with Part I's
  table; A195656 starts with `53248 = A(12,1)`.
- **A061593, A061594** (Antonio G. Astudillo, 22 May 2001): `F_2` equals
  A061593's generating function identically, and its closed form
  `(17n−109)3^n + 2F(2n+10)` gives `(α_2, β_2) = (17, −109)`; A061594 has
  offset 0, its generating function minus 1 is `F_3`, and its explicit formula
  has the term `(231n−2377)4^n`. **Nothing was submitted to the OEIS.**

## The inverses and the transseries volume

(`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.)
Instances: Part II's `N = L/W_0(L)` (18.2) and Part I's
`N = (Y/p)/W_0(e^d Y/p)` (10.3) of the factorial core
`p0:prop:factorial-core` (`κ_vol = 1, d_vol = 0`; `κ_vol = p, d_vol = b`);
Part III's `w_0(y)` (25) of the Lambert core `p0:thm:lambert-core` after the
shift `X = x + β/α` and a logarithm (`a_vol = log(h+1)`, `b_vol = 1`); Part
III's threshold statements of Theorem 28.1 of `p0:thm:staircase` items (1) and
(2), with the real extension `f_h` on `[n_1, ∞)` as the admissible
interpolation (for targets `y ≥ P_h(n_1)`; the article's range "above
`P_h(n_1−1)`" was corrected after the independent check of 7 October 2026). Analogues: the one-step corrections (10.5), (10.8), (18.3), (30)
are exactly the first-order term of `p0:eq:operator-series` about the
respective cores, with the Parts' own error bounds. Not instances: Part I's
Theorem 10.1 and Part II's bracket (11.5), proved directly at the integers
without an interpolation; when their ceilings agree they reach the conclusion
of `p0:thm:staircase` (2).

## What the report does not claim

Every limitation is printed in place. In short: the encodings (Knuth 1994,
Wilf 1995, Matsuo, Brown), Kotěšovec's leading constant and fixed-height law,
Wilf's dominant term, partial fractions and Lambert-W inversion are prior, as
the manuscripts say; no Part makes an exhaustive priority claim, and the
appendix and Part III prove published conjectures without claiming the first
proof. **Part I**: compact `w/h` only (no `λ_h → 0`); bounded critical
windows; no convergence of the series in `h^{−1}` or uniformity in growing
order; star-sum diagnostics test `S`, not `A`; existential constants; no
every-height degree equality, no planar statement. **Part II**: fixed orders
only, no large-order control; existential bracket constants, no certified
finite-input inverse; the large terms not recomputed; residuals uncertified.
**Part III**: fixed height only; no degree attainment, no sharper low-degree
bound, no cancellation criterion; existential constants; Alekseyev's argument
not recovered. **All packages**: finite checks prove no asymptotic statement;
manifests detect changes and authenticate nothing.

## Independent check of the write (7 October 2026)

An adversarial check made by the intake after the write (`3625d8199`), with
its own code, after fetching again the OEIS entries A137432 (revision #62 and
its revision history), A194644, A194647, A195656, A061593, A061594, the b-file,
the entry's `a137432.txt` and Matsuo's table.

- **Remark 20.1**: the proof holds; the bounds and both equality cases hold for
  all 64 rectangles `h, w ≤ 8` (the encoding itself checked against a direct
  row-mask count), the per-word bound for `h ≤ 7`, `w ≤ 5`, and the square
  bounds for `a(1), …, a(18)`. Part I's 6 × 6 table and `a_1, …, a_12`
  reproduced.
- **Remark 25.2**: the proof holds, but it is a reading of Theorem 27.2
  (Wilf's `α_h ≥ 1`); qualified in the article. An exact Berlekamp–Massey
  reduction of `P_h(w)` for `h ≤ 5` gives exponent two for `1 − (h+1)z`, the
  denominator degrees 2, 4, 7, 17, 31 and the per-degree maximal exponents of
  Table 1, and `(α_h, β_h)` equal to the package's certificate.
- **The A137432 conjecture**: first in revision #19 (Kotesovec, 31 August 2011,
  the first version under the present name, on a recycled number), proved as
  stated.
- **Coefficients**: Part I's operator and explicit `c_1(λ)`, `c_2(λ)` agree
  identically; at `λ = 1` they are Part II's `c_1`, `c_2`, and Part II's short
  forms agree (SymPy). **Correction**: the write said every printed digit of
  `C, c_1, c_2, c_3, G(0), H(0), J(0)` agrees; the last printed digit of the
  delivered `c_1` (16.5), `c_3` (16.7) and `H(0)` (7.13) is rounded, not
  truncated (notes added; delivered digits kept). The values in this README are
  truncations.
- **Fixture**: its SHA-256 identified (Matsuo's table, above); `R_2`, `R_3` at
  `n = 100, …, 800` reproduced at 3000 digits.
- **Transseries volume**: every instance and analogue re-derived; the range of
  the staircase reading corrected to `y ≥ P_h(n_1)`.
- **Provenance**: archive sizes, file counts, line and page counts and bundle
  index times confirmed. Kotěšovec's book was not read at the check either.

No other defect was found. The check is recorded at the end of Section 31.

## Further questions, and the standing rule

Section 31 collects (Vladimir's standing rule of 4 October 2026), with sources,
sketches and what is missing:

1. the regimes `w/h → 0` (Part I);
2. growing critical windows and matching (Part I);
3. effective constants and onsets for all inverses (all Parts);
4. subcritical corrections beyond `O(1/h)` (Part I; the residue of Part II's
   rectangular question, otherwise answered by Part I);
5. the maximal degree at every height, cylinder and plane (Parts I, III;
   Conjecture 2);
6. low-degree multiplicities and the status of Conjecture 3 (Part III);
7. cancellation criteria (Part III);
8. height-uniform planar analysis (Part III);
9. large order of the `c_j` (Part II);
10. history of the 2011 conjectures (Parts I, III);
11. reading the book's pages (the write);
12. the data behind the residuals (Part II; the fixture discrepancy above).

**Answered within the report, sentences kept** (dated notes): Part II's
rectangular question (by Part I); Part I's "does not prove … the planar
conjecture" (Part III proves its upper half and Conjecture 4). **Recorded as
the sources state them, with what could be checked**: the strict bound of pp.
209–210 at `n = 1` (Part II; proved for `n ≥ 2` in Remark 20.1); the printed
Conjecture 3 against the page's exponents (Part III; exponents confirmed by
Remark 25.2, page not read). No mathematical statement of the three manuscripts
was found wrong.

## Relation to neighbouring reports

- `a201513-sparse-chess-placements` is the only other report on nonattacking
  kings (searched 6 October 2026). It treats the sparse regime (`n` kings on
  an ordinary `n × n` board, A201513, carrier `e^{−9/2} n^{2n}/n!`, cluster
  expansion); this report treats the dense regime (`hw` kings on `2h × 2w`,
  density `1/4`, block encoding and transfer spectra). No lemma is shared; its
  `K_n` and `B_n` are not this report's `a_n`, `A(h,w)`, `K` or `B_j`. A
  reciprocal note there is proposed separately.
- The transseries volume, for the inverses (above).

## Relation to formal projects

Placement in the collection confers no formal status, and no statement of this
report is formalized: no Lean or Rocq file treats king placements (searched 6
October 2026).

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (the 45 staged code, data and markdown
  files and the two staged base files were checked against a fresh extraction
  from `60f54ea06` at the write: 0 differences; `article.tex` and this README
  then replaced the two staged base files). Only names changed (tables at the
  end).
- **Nothing should be run in this directory.** The companions are written for
  the delivered layouts: Report 173's runner and residual script import their
  sibling modules by delivered names and read `fixtures/…`; Report 174's runner
  imports `exact_checks` and `symbolic_checks`; the package and manifest tools
  expect the unshipped manifests (`SHA256SUMS.json`, `manifest.json`) and
  allowlists naming `Report17x.tex`, `companion/…`, `generated/…`, `data/…`.
  Report 175's verifier reads its certificate from an explicit path, so on a
  copy of this directory
  `python -B code/175-planar-verify.py --data data/175-planar-data-certificates.json`
  works under the shipped names (checked at the write). Rerun the rest from the
  archives (below).
- The markdown files `173-square-companion-README.md`,
  `173-square-sources-REFERENCES.md`, `175-planar-README_CODE.md`,
  `175-planar-SOURCES.md` and the JSON build records use delivered paths
  (`companion/…`, `generated/…`, `data/…`, `Report173.tex`, `report.tex`,
  `/tmp/…`) and name the unshipped PDFs and manifests.
- The fixture's `source_url` (above).
- On Windows the companions write CRLF line ends to a redirected standard
  output; compare after removing carriage returns.
- The manuscripts' bibliographies cite the same works with different details
  (the book's page ranges; Wilf by journal link or DOI; Brown by preprint or
  journal; two descriptions of A137432 and of Matsuo's repository); the merged
  bibliography keeps all of them, attributed to the Parts.

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. Recreate the
delivered layout from the arrival commit:

```
git show 60f54ea06:docs/incoming/Cylindrical_Kings_All_Order_Asymptotics_and_Inverses_Source.zip > r173.zip
git show 60f54ea06:docs/incoming/Rectangular_Kings_Aspect_Ratio_Transition_Source.zip > r174.zip
git show 60f54ea06:docs/incoming/Planar_Kings_Pole_Bounds_and_Inverses_Source.zip > r175.zip
mkdir x173 x174 x175 && unzip -q r173.zip -d x173 && unzip -q r174.zip -d x174 && unzip -q r175.zip -d x175
cd x173
python -B companion/run_checks.py | tr -d '\r' | cmp - generated/checks.json
python -B companion/residuals.py --precision 80 | tr -d '\r' | cmp - generated/residuals.json
python -B companion/run_checks.py --extended          # transfer identities to n = 10
python -B companion/symbolic_all_orders.py --order 3  # optional, needs SymPy
cd ../x174/Report174
python -B companion/run_checks.py | tr -d '\r' | cmp - verification.json
python -B companion/run_checks.py --extended --output ../extended-results.json
python -B companion/symbolic_checks.py --max-defect 16
python -B test_package_tools.py
cd ../../x175
python -B verify.py | tr -d '\r' | cmp - data/default_results.json
python -B guard_tests.py | tr -d '\r' | cmp - generated/verification_guards.json
python -B verify.py --extended                        # compare with data/verified_results.json
python -B regenerate.py --compare data/certificates.json   # optional, needs SymPy
```

Each also runs with `python -B -O`. Python 3.10 or later; standard library only
except the optional SymPy scripts. Results: at placement (dossier of batch 109,
6 October 2026, Python 3.14.4, Windows, on copies) every computation reproduced
its delivered output after removing carriage returns, in normal and `-O` mode:
Report 173's default, extended (2046 words to `n = 10`) and residual runs, and
its SymPy order-3 run (about 27 s) reproduces the printed `c_3` numerator;
Report 174's default (about 23 s) and extended (about 50 s) runs, its symbolic
checks and its packaging tests (10/10); Report 175's default, extended, guard
and SymPy regeneration (`h ≤ 4`) runs. At the write (6 October 2026, fresh
extractions) Report 173's `run_checks.py` and `residuals.py --precision 80`,
Report 174's `run_checks.py`, and Report 175's `verify.py` (on a copy of this
directory, shipped names) reproduced the shipped files byte for byte after
removing carriage returns. The PDF and ZIP builds were not run.

## Rights

Repository contents are MIT-0. OEIS data are available under CC BY-SA 4.0
([OEIS license](https://oeis.org/LICENSE)): Report 173's fixture holds
`a_1, …, a_10` (entry data) and `a_100, …, a_800` (from Rintaro Matsuo's
tables, linked from the entry; the licence of his repository was not checked);
the small counts printed in the Parts and the planar generating functions
match A137432, A194644, A194647, A195656, A061593 and A061594. No paper, book
or third-party code is shipped. Credited: Kotěšovec for the leading constant,
the fixed-height cylinder results and the conjectures; Matsuo for the
cylindrical encoding, the polynomial-time algorithm and the tables; Knuth,
Wilf and Brown for the planar encodings and Wilf for the dominant term;
Alekseyev for the 2011 factor-generation work; Breger and Kotěšovec for terms.
Nothing was submitted to the OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy of `article.tex` (no other inputs);
commit only `article.pdf`. The build (70 pages at the write; 71 after the
independent check of 7 October 2026, label numbers unchanged, aux files
compared): no errors, no undefined or
multiply defined references or citations, no duplicate destinations, no
overfull or underfull boxes, no warnings. The log carries one "Infinite glue
shrinkage found in box being split" message, from the notation longtable
breaking across pages. The three delivered `.tex` files compile with MiKTeX
pdfLaTeX to 22, 17 and 13 pages with no warnings.

## Delivered path → shipped path

Report 174 (`174-aspect-`; delivered in the wrapper `Report174/`):

| Delivered | Shipped |
|---|---|
| `Report174/Report174.tex` | `article.tex` (Part I) |
| `Report174/README.md` | replaced by this guide |
| `Report174/companion/<name>.py` | `code/174-aspect-companion-<name>.py` |
| `Report174/build_package.py`, `package_tools.py`, `test_package_tools.py`, `verify_package.py` | `code/174-aspect-<name>` |
| `Report174/verification.json`, `build_info.json` | `data/174-aspect-<name>` |
| `Report174/Report174.pdf`, `manifest.json` | not shipped |

Report 173 (`173-square-`; delivered flat):

| Delivered | Shipped |
|---|---|
| `Report173.tex` | not shipped; printed as Part II of `article.tex` |
| `companion/README.md` | `173-square-companion-README.md` |
| `sources/REFERENCES.md` | `173-square-sources-REFERENCES.md` |
| `companion/<name>.py` | `code/173-square-companion-<name>.py` |
| `build.py`, `test_build.py`, `verify_package.py` | `code/173-square-<name>` |
| `companion/fixtures/a137432_selected.json` | `data/173-square-companion-fixtures-a137432_selected.json` |
| `generated/<name>.json` | `data/173-square-generated-<name>.json` |
| `README.md`, `Report173.pdf`, `SHA256SUMS.json` | not shipped |

Report 175 (`175-planar-`; delivered flat):

| Delivered | Shipped |
|---|---|
| `report.tex` | not shipped; printed as Part III of `article.tex` |
| `README_CODE.md`, `SOURCES.md` | `175-planar-<name>` |
| `build.py`, `guard_tests.py`, `regenerate.py`, `test_build.py`, `verify.py`, `verify_manifest.py` | `code/175-planar-<name>` |
| `data/<name>` | `data/175-planar-data-<name>` |
| `generated/<name>` | `data/175-planar-generated-<name>` |
| `README.md`, `Report175.pdf`, `SHA256SUMS.json` | not shipped |

## Provenance

Three manuscripts (bundle Reports 174, 173, 175) → one report; base 174,
printed as Part I. Arrival `60f54ea06`, placement `f7e9e5c2f`, write batch 109
(6 October 2026). No manuscript pins a commit. Merge choices (base first, then
173 and 175 by dependency; repeated encodings and uniform arguments printed in
each Part as delivered, with pointers; members' section and statement numbers
offset, Part III's equation numbers kept; running heads dropped; the merged
bibliography with unified keys) are listed in the article's front matter,
"Provenance and merge decisions".
