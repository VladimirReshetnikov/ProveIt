# Inversion Sequences Solved by Kernel Orbits

**Square-root asymptotics to every fixed order and threshold inverses for OEIS A279544, A279567, A279569 and A279558**

*[Dated note, 7 October 2026: this subtitle, and the article's, read
"… and Lambert-W₋₁ threshold inverses …", the error that the independent
check corrected in the abstract (below) but left in both subtitles: Part
III's inverse contains no `W₋₁`. The abstract's dated note now quotes the old
subtitle.]*

This is a research report built on 5 October 2026 (write batch 104) from
three manuscripts of one external research session, Reports 118, 119 and 122
of the session bundle of Reports 1–243, all dated 2 October 2026. An
inversion sequence of length `n` is an integer vector with `0 ≤ e_i < i`.
Britt and Beaton (*Completing the enumeration of inversion sequences avoiding
triples of relations*, arXiv:2512.21943v3, 29 September 2026) gave exact
generating trees and catalytic equations for the classes avoiding a triple of
relations, and stated numerically — explicitly as non-rigorous, in their
Section 4.2 — laws `a_n ~ C μⁿ n^(−3/2)` for four classes whose generating
functions they believe to be nonalgebraic. The three manuscripts prove these
four laws by one method: a kernel substitution reduces the catalytic equation
to a scalar affine functional equation, solved by a normally convergent sum or
quotient along contracting Möbius-type orbits seeded at an algebraic kernel
root; global continuation, exclusion of competing singularities and an exact
certificate of a nonzero square-root amplitude then give coefficient
asymptotics to every fixed order and a threshold inverse, centred at a
Lambert-W₋₁ root in Parts I and II and expanded in powers of `1/log M` with
coefficients polynomial in `log log M` in Part III.

- **Part I** (Report 118, the base): class 214 = A279544 (`μ = 4`) and class
  1509 = A279567 (`μ = 3 + 2√2`); a forward orbit sum, and for 1509 a backward
  orbit quotient with a global nonvanishing-denominator certificate; the
  generic threshold-inverse theorem.
- **Part II** (Report 119): class 1953A = A279569 (`μ = 27/4`), from both small
  roots of a cubic kernel; continuation by a real determinant gap,
  Pringsheim's theorem and removal of boundary poles; the explicit log-log
  inverse. By the Wilf-equivalence that Britt and Beaton record, the counting
  statements hold also for class 1953B.
- **Part III** (Report 122): class 830 = A279558 (`μ = 27/4`), from a
  re-derived tree, the ternary anchor `R = 1 + zR³` and two contracting orbits,
  with a zero-free orbit product on a larger disc; the inverse in `log M`
  coordinates with all-order discrete localization.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Inversion sequence asymptotics from iterated kernels: Rigorous asymptotics and counting index inverses* (base); title block "REPORT 118", no author line | 118 | `Inversion_Sequences_A279544_A279567_Asymptotics_and_Inverses_Source.zip` (413,366 bytes, 16 files; `report118.tex`, 1,100 lines, 18 pp.) | none | `612787fb4` | Part I, Sections 1–9 |
| *Inversion sequence asymptotics from two kernel roots: A279569 and class 1953A*; "REPORT 119" | 119 | `A279569_Two_Kernel_Asymptotics_and_Inverses_Source.zip` (398,990 bytes, 18 files; `report119.tex`, 1,005 lines, 16 pp.) | none | `612787fb4` | Part II, Sections 10–19 |
| *A279558 asymptotics and inversion: A ternary root and two contracting orbits*; "REPORT 122" | 122 | `A279558_Asymptotic_Expansion_and_Inverse_Thresholds_Source.zip` (407,593 bytes, 28 files; `report122.tex`, 1,065 lines, 17 pp.) | none | `612787fb4` | Part III, Sections 20–30 |

All three archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `612787fb4` (batch 104, "Place batch 104: twelve bundle reports as four
new reports") removed them from `docs/incoming/` and split the triage's
eight-source Britt–Beaton cluster into three reports by method. The write is
"Write batch 104 (a279544-inversion-kernel-classes): new report, four
algebraic-kernel inversion-sequence classes".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. None of the manuscripts names an author or a tool, says it is
AI-assisted, or carries "prepared for private review" wording; none pins a
ProveIt commit. The packages' own "exact reproducibility companions" and
mutation campaigns are the delivering session's checks of its own work, not an
assessment by a referee or by this repository. Every result, proof, remark,
question and limitation of the three manuscripts is printed; no passage is
shared verbatim between them (8-gram overlap at most 3.3%, longest common run
27 words of title-page matter), so every Part is complete.

## Files

The directory holds 49 files: 6 at the root, 30 in `code/`, 13 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 118, prefix `118-kernels-`**: 11 files besides the article (1 at the
root, 7 in `code/`, 3 in `data/`); its `report118.tex` is the base of
`article.tex`. Root: the guide to its exact checks. `code/`: the exact checker
and its companion module, the mutation and replay harness, the outer integrity
check and its negative tests, the deterministic PDF build and ZIP packer.
`data/`: the closed fixture (certificate), the recorded campaign summary
(738 negative runs: 312 fixture leaves and 369 named cases, each in normal and
optimized mode) and the tested toolchain.

```
118-kernels-checks-README.md
code/118-kernels-build.py
code/118-kernels-checks-check.py
code/118-kernels-checks-companion.py
code/118-kernels-checks-validate_bundle.py
code/118-kernels-integrity.py
code/118-kernels-pack.py
code/118-kernels-test_integrity.py
data/118-kernels-build-environment.txt
data/118-kernels-checks-fixtures-certificate.json
data/118-kernels-verification_results.json
```

**Report 119, prefix `119-tworoot-`**: 12 files (1 at the root, 8 in `code/`,
3 in `data/`). Root: the guide to its exact checks. `code/`: the runner, the
exact algebra and enumeration module, the `Q(√3)` jet certificate, the shared
support module, the mutation campaign, the outer negative tests, the PDF build
and packer. `data/`: the fixture, the recorded campaign summary (690 negative
runs: 232 fixture leaves and 345 named cases, in both modes) and the tested
toolchain. Its `integrity.py` is a byte copy of Report 118's and is not shipped
again: `code/118-kernels-integrity.py` is the same file.

```
119-tworoot-checks-README.md
code/119-tworoot-build.py
code/119-tworoot-checks-exact_math.py
code/119-tworoot-checks-jet_certificate.py
code/119-tworoot-checks-mutation_tests.py
code/119-tworoot-checks-run_checks.py
code/119-tworoot-checks-support.py
code/119-tworoot-pack.py
code/119-tworoot-test_integrity.py
data/119-tworoot-build-environment.txt
data/119-tworoot-checks-fixtures.json
data/119-tworoot-verification_results.json
```

**Report 122, prefix `122-anchor-`**: 23 files (1 at the root, 15 in `code/`,
7 in `data/`). Root: the guide to its exact companion. `code/`: the
authoritative verifier, its exact model and analytic modules and negative
tests; the five auxiliary `scripts/` programs (original certificate formulas,
assertion-based, refusing `-O`); the outer integrity check and its tests; the
full replay driver, PDF build (`build.py`, `build.sh`) and packer. `data/`: the
151 exact terms `a_0..a_150` generated from the tree (not an OEIS b-file), the
certificate fixture, the recorded verifier and negative-test results, the
original certificate and correction outputs, and the tested toolchain.

```
122-anchor-checks-README.md
code/122-anchor-build.py
code/122-anchor-build.sh
code/122-anchor-checks-exact_analytic.py
code/122-anchor-checks-exact_model.py
code/122-anchor-checks-negative_tests.py
code/122-anchor-checks-verify.py
code/122-anchor-integrity.py
code/122-anchor-repack.py
code/122-anchor-reproduce.py
code/122-anchor-scripts-certify.py
code/122-anchor-scripts-certify_corrections.py
code/122-anchor-scripts-global_bounds.py
code/122-anchor-scripts-verify_model.py
code/122-anchor-scripts-verify_orbit.py
code/122-anchor-test_integrity.py
data/122-anchor-a279558_n0_150.txt
data/122-anchor-build-environment.txt
data/122-anchor-certificate_output.txt
data/122-anchor-checks-certificate.json
data/122-anchor-correction_output.txt
data/122-anchor-negative_results.json
data/122-anchor-verification_results.json
```

**Not shipped** (all retrievable from `60f54ea06`): the three PDFs; the three
`CHECKSUMS.sha256` files and the inner manifests `checks/MANIFEST.json`
(Reports 118, 119) and `checks/inventory.json` (Report 122) — checksum
manifests, verified at placement (15, 17 and 27 entries; 5, 7 and 6 inner
entries; no mismatch, nothing unlisted); the delivery READMEs (Report 118's
`README.txt` was staged as `README.md` and is replaced by this guide; Report
119's `README.txt` and Report 122's `README.md`, which holds its replay
instructions, were not staged); `report119.tex` and `report122.tex` (printed as
Parts II and III); Report 119's `integrity.py` (byte copy, see above).

## Labels and numbering

Label prefix **`ivk:`**: Part I uses `ivk:orb:` (Report 118's 79 labels), Part
II `ivk:two:` (Report 119's 64), Part III `ivk:anc:` (Report 122's 85). The
write added 24 labels: the front matter (`ivk:sec:guide`, `ivk:sec:status`,
`ivk:sec:pipeline`, `ivk:sec:notation`, `ivk:sec:provenance`,
`ivk:sec:neighbours`); the Parts (`ivk:orb:part`, `ivk:two:part`,
`ivk:anc:part`); the further-questions subsections (`ivk:orb:sub:further`,
`ivk:two:sub:further`, `ivk:anc:sub:further`); the two remarks
(`ivk:two:rem:wilf`, `ivk:anc:rem:strict`); and ten delivered headings that had
no label (`ivk:orb:sec:slit`, `ivk:orb:sec:amplitude`, `ivk:orb:sec:reproduce`,
`ivk:orb:sec:questions`, `ivk:two:sec:contrast`, `ivk:two:sec:amplitude`,
`ivk:two:sec:inverses`, `ivk:two:sec:loglog`, `ivk:two:sec:reproduce`,
`ivk:two:sec:questions`). 252 labels in all, all distinct.

Sections are numbered continuously and statements within sections; equations
are numbered continuously through the report, as in the deliveries:

| Part | Manuscript | Section here | Statement `k.j` | Equation `(m)` |
|---|---|---|---|---|
| I | Report 118 | `k` (unchanged, 1–9) | unchanged | unchanged, (1)–(72) |
| II | Report 119 | `k + 9` (10–19) | `(k+9).j` | `(m+72)`, (73)–(128) |
| III | Report 122 | `k + 19` (20–30) | `(k+19).j` | `(m+128)`, (129)–(195) |

For example Report 119's Theorem 8.1 is Theorem 17.1 and its equation (55) is
(127); Report 122's Proposition 9.1 is Proposition 28.1. The write's additions
are unnumbered notes, Remarks 10.2 and 28.2 (each the last statement of its
section) and Subsections 9.1, 19.1 and 30.1 (each at the end of its Part), so
no delivered number moved. A comparison of the build's `.aux` with separate
builds of the three delivered `.tex` files confirmed all 228 delivered labels
under these offsets. The delivered READMEs and code use the manuscripts' own
numbers.

## Notation

No symbol was renamed. Each Part keeps its manuscript's letters and opens with
a short reading-conventions table; the front matter's "Notation across the
three Parts" lists every letter whose meaning changes. The most dangerous:
**the correction letters** — Part I writes `c_j` (relative), `d_j`
(logarithmic), `e_j` (inverse), Parts II and III write `d_j` for the *relative*
corrections (`ℓ_j`, `ℓ_k` logarithmic; `η_j`, `P_j(log L)` inverse), and Part II
also has orbit coefficients `e_j, c_j, d_j^orb`; **`b`** — Part I's `b_n` counts
A279567 while its `b(z, x)` is an orbit forcing term, and Parts II–III's `b_m`,
`b_j` are Puiseux coefficients (Part I's `h_m`, `ĥ_j`); **`A`** — the generating
function in Parts I and II, the constant `log C + p log λ` in Part III (whose
generating function is `F`); **`L`** — `log μ` in Part I, `log T` or `log M`
(the target) in Parts II and III. Others: `F`, `H`, `P`, `Q`, `R`, `K`, `M`,
`X`, `u`, `t`, `y`, `α`, `β`, `E_N`, and the target letter (`Y`, `T`, `M`).
Citation keys: Report 119's `oeis` is `oeis1953`, Report 122's is `oeis830`.

## What the report claims

**Part I (Report 118).**
- Theorem 1.1 (A279544): radius `1/4`, holomorphic continuation to the slit
  disc `|z| < R`, `R < 1/2`, unique dominant singularity, and for every fixed
  `K`, `a_n = C 4ⁿ n^(−3/2)(1 + Σ_{j≤K} c_j n^(−j) + O(n^(−K−1)))`, `C > 0`; the
  orbit representation `A = Φ(z, r(z))/z` (Proposition 2.1), normal
  convergence (Lemma 3.1), `C = 4Φ_x(1/4, 1)/√π` with a rational recurrence and
  a proved tail; `C` enclosed to 52 decimals (24), `c₁ ≈ 27.6041`,
  `c₂ ≈ 43.9889` to 24 decimals (32).
- Theorem 6.1 (A279567): radius `3 − 2√2`, all fixed orders; the backward
  orbit quotient (45), the global bound `|1 − yV| > 1/3` (49),
  `Ĉ ≈ 0.0660857088256494310036700131193`, `ĉ₁ ≈ 8.05528`, `ĉ₂ ≈ −17.4929`
  certified (63).
- Theorem 7.1 (both sequences): the Lambert-W₋₁ centre, the all-order inverse
  recursion and the two-ceiling bracket `⌈y_K − E_K u^(−K−1)⌉ ≤ N(Y) ≤
  ⌈y_K + E_K u^(−K−1)⌉` (existential `E_K`, `Y_K`); strict monotonicity for
  `n ≥ 1` by an injection plus an extra object.

**Part II (Report 119).**
- Theorem 10.1 (A279569): radius `4/27`, unique dominant singularity,
  Δ-domain, convergent Puiseux series, all fixed orders;
  `C = 0.01116841071267033797867998293487861864…` (38 decimals, (115)),
  `d₁ ≈ 26.9486067786116`, `d₂ ≈ 53.3933565681159` certified (114).
- The continuation: Proposition 12.1 (the even quotient of two orbit limits is
  the germ), Lemma 13.1 (explicit product domain), Lemma 14.1 (real
  determinant gap), Proposition 14.2 (Pringsheim, absolute convergence at `ρ`,
  removable boundary poles), the certificate `F_v(ρ, 3, 3/4) > 0` (107).
- Theorem 17.1 and (128): the same inverse theorem for A279569, with the
  explicit log-log form; strict monotonicity by injection plus the all-zero
  sequence.

**Part III (Report 122).**
- Theorem 20.1 (A279558): radius `4/27`, unique dominant singularity,
  Δ-domain, convergent Puiseux series, all fixed orders;
  `C = 0.000180963775465117907270430806495787169143…` (43 decimals, (133)),
  `d₁ ≈ 137.2216`, `d₂ ≈ 4914.561` certified (134)–(135).
- The tree with its all-zero correction (Proposition 21.1), the anchor
  `H(z, Y) = R` (151), the formal two-orbit representation (Lemma 22.1),
  normal convergence (Proposition 23.1), the zero-free product
  `|P(z)| > e^(−32/3)` on `|z| ≤ 149/1000` (Proposition 24.1), transfer
  (Proposition 27.1).
- Theorem 20.2 and Proposition 28.1: the inverse in `L = log M` with
  polynomials `P_j(log L)` and error `B_J(1 + log L)^(J+1)/L^(J+1)`; monotonicity
  `a_{n+1} ≥ a_n` by injection, strict for large `n` from the ratio limit.

**Added by the write** (all marked `[write]`, dated 5 October 2026):
- Remark 10.2: the counting statements of Part II hold for class 1953B
  (`(≠, ≥, >)`, avoidance of 100, 120, 210), by the Wilf-equivalence that
  Britt and Beaton (Table 1, Section 3.7) attribute to Martinez and Savage:
  Theorem 60 (Section 3.2.1) of arXiv:1609.08106v2, proved there by showing
  that their bijection between the inversion sequences avoiding {110, 210}
  and those avoiding {100, 210} preserves avoidance of 120 (the journal
  version, J. Integer Seq. 21 (2018), Article 18.2.2, was not consulted). A
  brute force at the write gives equal counts for `n ≤ 10`, and an
  independent dynamic program at the independent check for `n ≤ 80`. The
  citation replaced "not consulted here" after the independent check, with a
  dated note.
- Remark 28.2: `a_{n+1} ≥ a_n + 1` for `n ≥ 1` for class 830, by the extra
  object `(0, …, 0, n)` outside the image of "append the current maximum".
  Report 122 proves only weak monotonicity directly and strictness from the
  asymptotics; the remark says so and completes it.
- Notes: Theorem 20.2 is the case `J = 1` of Proposition 28.1 (with
  `(1 + log L)² ≤ 4(log L)²` for `L ≥ e`); Part II's (128) and Part III's (136)
  are the same expansion (`B(L) = q_L`), and the error term of (128) is proved
  by Part III's argument; the three inverse theorems are one theorem; the
  checks against Britt–Beaton v3 and the OEIS; cross-references between the
  three continuation devices; the front matter ("The common pipeline" prints
  the shared method once, with pointers to each class).

**Checks recorded** (placement dossier and write, 5 October 2026): the proofs
were read in full with no gap found; 58 symbolic identities and 25 rational
certificate premises re-derived; brute force from each forbidden-relation
definition agrees with the generating trees for `n ≤ 9`; independent dynamic
programs to `n = 1500` give bounded, converging residuals
`(a_n/(Cμⁿn^(−3/2)) − 1 − c₁/n − c₂/n²)·n³` (about −1062, 21.04, −489 and 26826
at `n = 1500` for classes 214, 1509, 1953A, 830) with the certified constants.
Kotěšovec's OEIS amplitudes (7 October 2021 for A279544, A279567, A279569;
13 January 2026 for A279558, normalization `c = C√π`) lie inside the certified
intervals for A279544 and A279567 and agree digit for digit, as far as they are
displayed, with those for A279569 and A279558. **No digits are new**: the
contribution is proof and certification.

**Independent check of the write (5 October 2026).** An adversarial check
made by the intake after the write (`37c5ebe97`) reread the seven items of the
write that carry mathematics or citations — Remark 10.2 and the transfer to
class 1953B; Remark 28.2; the note identifying Theorem 20.2 with Proposition
28.1 at `J = 1`, `B = 4B_1`; the note identifying (128) with (136) and its
error term with Proposition 28.1's proof; the amplitude comparisons with
Kotěšovec's values; the transseries-volume citations; and the transfer
formulas for `c₁`, `c₂` — and found every mathematical claim valid, with no
counterexample and no gap in any proof chain. Changes, each with a dated note
keeping the first wording where wording was replaced:

- The abstract and the front-matter row on threshold inverses no longer say
  that every Part proves a Lambert-W₋₁ inverse with error `O(u^(−K−1))`: Part
  III's inverse contains no `W₋₁` (Theorem 20.2 and Proposition 28.1 expand
  in powers of `1/L` with polynomials in `log L`), and its error is
  `O((1 + log L)^(J+1)/L^(J+1))`.
- The transseries volume's `p0:thm:flattening`, the theorem that Part III's
  expansion and Part II's (128) instantiate, and `p0:rem:accuracy-claim`,
  which names the `(1 + log L)^(J+1)` factor as the only rigorous difference
  from the Lambert-centred form, are now cited in the front matter, the note
  after Proposition 28.1 and the bibliography (both labels and statements
  confirmed in the volume).
- The hedges on Martinez and Savage in Remark 10.2, Part II's
  further-questions item 6 and the bibliography are replaced by the precise
  citation, Theorem 60 of arXiv:1609.08106v2, read at arXiv; the statement that
  no bijection carrying Part II's generating tree to 1953B is given stands.
- Two precisions in notes: the note after Theorem 20.2 writes `ε₁^P` for
  Proposition 28.1's error at `J = 1`, which it had also called `ε₁`, the
  theorem's letter; and the staircase of `p0:def:three-inverses` is matched to
  `N(Y)` for `Y > 1` with `n_1 = 1` (`a_0 = a_1 = 1`).

The tests, none of which used the delivered or the write's programs: brute
force from the forbidden-relation definitions for `n ≤ 10` for classes 214,
1509, 1953A, 1953B and 830; its own generating-tree recurrences, derived from
the definitions (class 830's reproducing Part III's "ends on its maximum or
premaximum" rule and its S/T split), equal to the brute force and to the OEIS
b-files for `n ≤ 60`; the 1953B recurrence equal to the 1953A recurrence and
the A279569 b-file for every `n ≤ 80`; `a_{n+1} − a_n ≥ 1` for class 830 for
`1 ≤ n < 60`; the extra object of Remark 28.2 checked against the injection the
remark uses (append the maximum; under "append `n`" it would lie in the
image); SymPy confirmation of `P_1`, `P_2` (zero residual through `L^(−2)`)
and of `B(L) = q_L`, `pB − λd₁ = P_1`; `(ν₁(log a_n) − n)L²/(log L)²` bounded
on the b-files (between −246 and −181 for A279558 at `100 ≤ n ≤ 1000`; at most
25 in absolute value for A279569 at `100 ≤ n ≤ 400`); 80-digit comparisons of
Kotěšovec's amplitudes with the certified intervals (inside for A279544,
A279567 and A279569's (77); equal to both truncated endpoints of (115) at 31
decimals, and of `C√π` for A279558 at 39 decimals); a re-derivation of the
transfer formulas for `c₁`, `c₂`; and a reading of each transseries-volume
citation against the volume. The record is an unlabelled dated paragraph at
the end of Section 30.1. This was a careful reading with numerical tests, not
a formal verification.

## What the report does not claim

Every limitation is printed in place. In short: **no nonalgebraicity or
non-D-finiteness** (Britt and Beaton's belief is not proved; a square-root
singularity is compatible with both); no convergence of the `1/n` series as the
order grows, optimal truncation, Stokes data, exponentially small sectors or
complete transseries; **the inverse constants** `E_K, Y_K` / `M_K, T_K` /
`B_J, L_J` **and the transfer onsets are existential** — not a certified
finite-target inverse routine, and dropping the error inside the ceiling is
invalid; only the first two corrections per class are certified; Part I's
`R < 1/2` is a sufficient domain, not a claim of a singularity at `1/2`; Part
II claims no zero-free region for its orbit determinant (only boundary zeros
cancel); Part III gives no explicit `n_0`, and its higher orders are "a theorem
with an algorithm", run only for the first coefficients. **All three**: no
literature priority and no external review; the numerical amplitudes were known
(Kotěšovec); finite checks corroborate, they do not prove continuation or
transfer; byte reproducibility holds only in the tested toolchain; checksums
are not signatures; OEIS b-files were not used, and terms beyond the displayed
prefixes are internally generated (the independent check of the write, above,
compared its own counts with the b-files).

## Further questions, and the standing rule

Each Part's last section keeps its delivered question list and gains a
subsection "Further questions and research" (9.1, 19.1, 30.1). Under
Vladimir's standing rule of 4 October 2026 the write moved there every claim
stated without proof or left open, with source, sketch and what is missing:

- **Effective thresholds** (118 Q1, 119 Q1, 122 Q1): explicit Δ-domains,
  transfer constants and inverse constants.
- **Algebraic / D-finite status** (118 Q2, 119 Q4, 122 Q5), crediting Britt and
  Beaton's belief (Sections 2.4, 3.5–3.7, 4.2).
- **Secondary singularities and maximal continuation** (118 Q3, 122 Q4); the
  complex zeros of Part II's determinant and their cancellation (119 Q2).
- **Higher coefficients** (only `c₁, c₂` certified), sign pattern, large-order
  growth, optimal truncation; why class 830's corrections are so large
  (`d₁/n > 1` at `n = 100`) (119 Q3, 122 Q2–Q3).
- **Other classes** admitting a contracting orbit with an effective
  nonvanishing or determinant-gap certificate (118 Q4, 119 Q5); refined
  statistics through the catalytic variables (122 Q6).
- **Class 1953B** directly (Part II, item 6): the transfer of Remark 10.2 rests
  on Martinez and Savage's Theorem 60, a Wilf-equivalence proved by an
  explicit bijection (checked here for `n ≤ 80`), but neither a direct
  treatment of 1953B nor a bijection carrying Part II's generating tree to it
  is given.
- **Earlier rigorous proofs**: the wider literature was not searched beyond
  Britt–Beaton and the OEIS, at placement or at the write.

**Nothing in any of the three manuscripts was found to be wrong; no claim was
refuted.** One statement proved only in a weaker form (Report 122's strict
monotonicity, from the asymptotics) is completed by Remark 28.2, and one error
term stated after a sketch (Report 119's (128)) is covered by Report 122's
proof (note after (128)).

## Relation to neighbouring reports

All in `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`:

- **Sibling reports** placed in the same commit from the same Britt–Beaton
  paper, by unrelated methods: `a279571-inversion-cone-walk` (A279571, Reports
  125 and 123: a quadrant cone walk, irrational exponent, non-D-finiteness) and
  `a279551-inversion-log-deficit` (A279551/A279556, Reports 126, 127 and 129:
  stretched-exponential deficits, refuting Britt–Beaton's numerical `n^(3/8)`
  forms). No shared lemma; only the source paper, the definition and the
  existence of a threshold inverse are common.
- The **transseries volume**
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`:
  the three threshold inverses are instances of `p0:thm:lambert-core` (its
  `b < 0` branch rule gives `W₋₁`), `p0:thm:lambert-centered` (the all-order
  reversion; Parts I and II), `p0:thm:flattening` (the direct
  polynomial–logarithmic reversion, whose remainder carries the factor
  `(1 + log L)^(J+1)` that `p0:rem:accuracy-claim` compares with the
  Lambert-centred form; Part III's inverse and Part II's (128), cited after
  the independent check), `p0:def:three-inverses` / `p0:thm:staircase` (the
  integer staircase, with `n_1 = 1` for targets above 1, and the separation
  condition) and `p0:cor:forward-to-inverse` (the mean-value step). The manuscripts bracket by two smooth envelopes
  instead of an admissible interpolation; same conclusion. Cited as context;
  not new inverse mechanics.
- No other report treats A279544, A279567, A279569 or A279558 (searched
  5 October 2026). This write edits no other report; suggested sibling
  cross-links are left to a reciprocal-notes commit. *[Dated note,
  7 October 2026: no such commit was needed. Both siblings name this report
  in their own batch-104 writes: `a279551-inversion-log-deficit` (`80adcb910`)
  and `a279571-inversion-cone-walk` (`4d3a6730f`), in their READMEs' sections
  on neighbouring reports.]*

## Relation to the formal project

Placement in the collection confers no formal status, and no statement of this
report is formalized: no Lean or Rocq file in the repository mentions
inversion sequences (searched 5 October 2026).

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (all 46 staged delivered files other
  than `article.tex` and `README.md` checked against a fresh extraction at the
  write: 0 differences; no CR bytes). Only names changed (tables below). The
  delivered code and markdown use delivery paths (`checks/…`, `data/…`,
  `scripts/…`, `CHECKSUMS.sha256`, `checks/MANIFEST.json`,
  `checks/inventory.json`, `report11N.tex`, `report11N.pdf`, `README.md`), most
  of which are shipped under other names or not at all. The integrity checks
  and harnesses read a **closed inventory** of the delivered layout, so **none
  of the scripts runs in this directory**.
- `README.md` at placement was Report 118's `README.txt`, renamed byte for
  byte; this guide replaces it (the original is in the archive).
- The delivered guides name `/tmp/report118-checks.json`,
  `/tmp/report118-validation.json`, `/tmp/report118-reproducibility.zip`,
  `/tmp/report119-check-results.json` and similar outputs; use a scratch
  directory outside the repository instead.
- **In-place writes.** `integrity.py --write` (all three packages) rewrites the
  outer inventory, and Report 118's and 119's `build.py` rewrite `report11N.pdf` in the
  package; run them only on a copy, and never to validate a received package.
- `122-anchor-checks-README.md` names `inventory.json` (not shipped) and
  provenance hashes of "audited producer" snapshots that were never delivered;
  `119-tworoot-checks-README.md` says its infrastructure is adapted from Report
  118's.
- Report 119's `integrity.py` is not shipped; `code/118-kernels-integrity.py`
  is byte-identical.

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. Recreate the
delivered layout from the arrival commit:

```
git show 60f54ea06:docs/incoming/Inversion_Sequences_A279544_A279567_Asymptotics_and_Inverses_Source.zip > s118.zip
git show 60f54ea06:docs/incoming/A279569_Two_Kernel_Asymptotics_and_Inverses_Source.zip > s119.zip
git show 60f54ea06:docs/incoming/A279558_Asymptotic_Expansion_and_Inverse_Thresholds_Source.zip > s122.zip
mkdir r118 r119 r122 && unzip -q s118.zip -d r118 && unzip -q s119.zip -d r119 && unzip -q s122.zip -d r122
cd r118/report118
python3 -B integrity.py .
python3 -B checks/check.py                       # also with python3 -B -O
python3 -B test_integrity.py
python3 -B checks/validate_bundle.py --output ../validation118.json   # see the caveats below
cd ../../r119/report119
python3 -B integrity.py .
python3 -B checks/run_checks.py                  # also with python3 -B -O
python3 -B test_integrity.py
python3 -B checks/mutation_tests.py --output ../results119.json      # POSIX only
cd ../../r122/report122
python3 -B integrity.py
python3 -B checks/verify.py --output ../results122.json              # also with -O
python3 -B checks/negative_tests.py --output ../negative122.json
python3 -B test_integrity.py
python3 -B reproduce.py --skip-pdf --output ../replay122.json        # byte comparisons need LF output
```

Python 3.10 or later and its standard library suffice (on Windows use `py`
for `python3`). Always pass `-B`: the inventories are closed, and a bytecode
cache file makes them fail.

**Results.** At placement (5 October 2026, Windows, Python 3.14.4, on copies;
recorded in the batch-104 dossier): every `integrity.py` and
`test_integrity.py` passed; Report 118's `checks/check.py` passed in normal and
`-O` mode (about 48 s each), its output equal as parsed JSON to the baseline in
`data/118-kernels-verification_results.json`; Report 119's
`checks/run_checks.py` passed in both modes (20 s, 16 s), equal to its
baseline; Report 122's `checks/verify.py` passed in both modes (32 s each) and
`checks/negative_tests.py` passed (125 s), their outputs equal to
`data/122-anchor-verification_results.json` and
`data/122-anchor-negative_results.json` up to CRLF line ends, and its five
`scripts/` programs passed with outputs equal to the shipped `data/` files up
to CRLF. **Three harness runs did not pass unmodified on Windows**, none for a
mathematical reason:

- Report 118's `checks/validate_bundle.py` stopped with `HARNESS_TIMEOUT` after
  845 s: it caps each subprocess at 45 s, and `check.py` needed 47–48 s on the
  loaded machine (119 s at the write, under heavier load).
- Report 119's `checks/mutation_tests.py` stopped with an error after 481 s:
  one case uses `os.mkfifo`, which Windows lacks (Report 118's harness has the
  same case).
- Report 122's `reproduce.py --skip-pdf` stopped at `CHECKER_BYTE_MISMATCH`:
  on Windows the checker writes CRLF, so its output differs from the shipped
  LF bytes although the content is equal; its remaining steps, run by hand,
  passed. The ZIP repack was not attempted.

As a diagnostic only, the two campaigns were also run on scratch copies with
the harness patched (the FIFO case removed, budgets raised to 600 s per process
and 7200 s in all, inner manifests resealed in the copy): Report 118's passed
in 538 s (736 runs: 312 fixture leaves and 368 named cases), Report 119's in
332 s (688 runs: 232 leaves, 344 named), each with normal output equal to
optimized, a fresh replay and unchanged sources. These are runs of modified
harnesses; the FIFO case remains untested, and an unmodified campaign is
expected to pass only on a POSIX host without heavy load. The delivered
`data/118-kernels-verification_results.json` and
`data/119-tworoot-verification_results.json` record the delivering session's
own passing campaigns (738 and 690 negative runs). The PDF and ZIP replays
(`build.py`, `pack.py`, `repack.py`) need the TeX Live pdfTeX 1.40.26 toolchain
of the `build-environment.txt` files for byte identity and were not run.

At the write (5 October 2026, fresh extractions of the three archives, Windows,
Python 3.14.4), the integrity checks and main checkers were rerun to confirm
this route: Report 118 `integrity.py` (15 files) and `checks/check.py` passed
(119 s); Report 119 `integrity.py` (17 files) and `checks/run_checks.py`
passed (53 s); Report 122 `integrity.py` (27 files) and `checks/verify.py`
passed (64 s), its output equal to the shipped record up to CRLF.

## Rights

Repository contents are MIT-0. The sequence terms printed in the article and
contained in the fixtures and data (A279544, A279567, A279569, A279558) are
recomputed by the shipped programs; the fixtures embed the displayed OEIS
prefixes as external checks (29 and 26 terms in Report 118's, 26 in Report
119's, 26 in Report 122's), and Report 122's 151-term table is generated from
its tree, not an OEIS b-file. OEIS data are available under CC BY-SA 4.0
([OEIS license](https://oeis.org/LICENSE)). The OEIS entries are credited for
the sequences and Kotěšovec for the numerical amplitudes; Britt and Beaton for
the generating trees, catalytic equations and the numerical laws; Martinez and
Savage for the class-1953 Wilf-equivalence. No third-party code or paper is
shipped. Nothing was submitted to the OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy; commit only `article.pdf`. The write's
build: 65 pages; no errors, warnings, undefined or multiply defined references
or citations, duplicate destinations, or overfull or underfull boxes. The log
carries one "Infinite glue shrinkage found in box being split" message, from
the front matter's notation longtable breaking across a page, as in other
reports with longtables. Builds of the three delivered `.tex` files (18, 16 and
17 pages) are warning-free; their 228 labels keep their numbers here under the
offsets above (`.aux` compared).

Rebuilt on 5 October 2026 after the independent check, in a scratch copy with
four pdfLaTeX passes: 66 pages (the appended record adds a page before the
references), no errors, warnings, undefined or multiply defined
references or citations, duplicate destinations, or overfull or underfull
boxes, and the same single infinite-glue message; all 252 labels keep their
numbers and pages (`.aux` compared with a build of the committed text).

Rebuilt on 7 October 2026 (cleanup pass: the subtitle without
"Lambert-W₋₁", and the abstract's dated note quoting the old one) with three
pdfLaTeX passes: 66 pages, equally clean, the same single infinite-glue
message; all 252 labels keep their numbers and pages (`.aux` compared with
a build of the committed text); page 1 rendered and inspected.

## Delivered path → shipped path

Report 118 (`118-kernels-`; `README.txt` replaced by this guide):

| Delivered | Shipped |
|---|---|
| `report118.tex` | `article.tex` (Part I) |
| `README.txt` | staged as `README.md`, replaced by this guide |
| `build.py`, `integrity.py`, `pack.py`, `test_integrity.py` | `code/118-kernels-<name>` |
| `checks/<name>.py` (check, companion, validate_bundle) | `code/118-kernels-checks-<name>.py` |
| `checks/fixtures/certificate.json` | `data/118-kernels-checks-fixtures-certificate.json` |
| `verification_results.json`, `build-environment.txt` | `data/118-kernels-<name>` |
| `checks/README.md` | `118-kernels-checks-README.md` |
| `report118.pdf`, `CHECKSUMS.sha256`, `checks/MANIFEST.json` | not shipped |

Report 119 (`119-tworoot-`):

| Delivered | Shipped |
|---|---|
| `report119.tex` | not shipped; printed as Part II of `article.tex` |
| `build.py`, `pack.py`, `test_integrity.py` | `code/119-tworoot-<name>` |
| `checks/<name>.py` (exact_math, jet_certificate, mutation_tests, run_checks, support) | `code/119-tworoot-checks-<name>.py` |
| `checks/fixtures.json` | `data/119-tworoot-checks-fixtures.json` |
| `verification_results.json`, `build-environment.txt` | `data/119-tworoot-<name>` |
| `checks/README.md` | `119-tworoot-checks-README.md` |
| `integrity.py` | not shipped (byte copy of Report 118's) |
| `README.txt`, `report119.pdf`, `CHECKSUMS.sha256`, `checks/MANIFEST.json` | not shipped |

Report 122 (`122-anchor-`):

| Delivered | Shipped |
|---|---|
| `report122.tex` | not shipped; printed as Part III of `article.tex` |
| `build.py`, `build.sh`, `integrity.py`, `repack.py`, `reproduce.py`, `test_integrity.py` | `code/122-anchor-<name>` |
| `checks/<name>.py` (exact_analytic, exact_model, negative_tests, verify) | `code/122-anchor-checks-<name>.py` |
| `scripts/<name>.py` (certify, certify_corrections, global_bounds, verify_model, verify_orbit) | `code/122-anchor-scripts-<name>.py` |
| `checks/certificate.json` | `data/122-anchor-checks-certificate.json` |
| `data/<name>` (a279558_n0_150.txt, certificate_output.txt, correction_output.txt, negative_results.json, verification_results.json) | `data/122-anchor-<name>` |
| `build-environment.txt` | `data/122-anchor-build-environment.txt` |
| `checks/README.md` | `122-anchor-checks-README.md` |
| `README.md`, `report122.pdf`, `CHECKSUMS.sha256`, `checks/inventory.json` | not shipped |

## Provenance

Three manuscripts (bundle Reports 118, 119, 122) → one report; base 118.
Arrival `60f54ea06`, placement `612787fb4`, write batch 104 (5 October 2026).
No manuscript pins a ProveIt commit. Merge choices (a report of its own rather
than a Part of an eight-source Britt–Beaton umbrella; base and bundle order;
every Part printed in full since nothing is shared verbatim; the shared method
summarized once in "The common pipeline"; prefixed labels and renamed citation
keys; the merged bibliography with two added entries, Martinez–Savage and the
transseries volume) are listed in the article's front matter, "Provenance and
merge decisions".
