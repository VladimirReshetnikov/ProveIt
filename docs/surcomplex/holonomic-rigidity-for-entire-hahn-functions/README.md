# Holonomic Rigidity for Entire Hahn Functions

**A sharp order-unit criterion for dilations, with uniform exclusion bounds,
and the exact boundary of nonlinear differential rigidity: first-order for
every value group, all orders when the value group has no order unit, an
explicit series of minimal differential order three when it has one, no
equation of order two, nor of order three and jet degree at most three, for
any value group, unbounded minimal orders over `C((t^R))`, lacunary series
with no equation at one order-unit scale, mixed differential–dilation
equations decided by the relative scale of their dilations,
polynomial-composition equations with a dominant argument of degree at least
two rigid for every value group, and Hahn-valued recurrences whose unit-root
coefficient sequences lie in one finitely generated algebra, while one Conway
coefficient of a first-order omnific recurrence can be any real sequence**
Merged research report, 22–23 September 2026, from thirteen manuscripts: 08
and 09, written independently on the same day; 10, which adds the nonlinear
part; 11 and 12, written independently and delivered together later, which
add the coefficient-field part; 13, delivered later still, which adds the
theta-descent part; 14, which adds the order-three-threshold part; five
manuscripts of batch 31: 18 and 19, which add the unit-dilation and
Newton-rigidity parts, 16 and 17, which add the theta-hierarchy and
single-scale parts, and 15, which adds the polynomial-composition part; and
20 (batch 33, manuscript 01), which adds the recurrence part.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 245 pages
README.md     this guide
08-finite-recurrences-PROOF_AUDIT.md          source 08: assumptions and critical proof steps
08-finite-recurrences-SOURCES_AND_SCOPE.md    source 08: sources, repository pin, priority limits
09-entire-hahn-holonomic-literature_audit.md  source 09: literature audit
10-nonlinear-rigidity-PROOF_AUDIT.md          source 10: dependency chain, sign checks, boundary
10-nonlinear-rigidity-SOURCES_AND_SCOPE.md    source 10: repository pin, literature, novelty limits
11-coarsening-differential-rigidity-PROOF_AUDIT.md        source 11: hypotheses, proof chain, pitfalls
11-coarsening-differential-rigidity-SOURCES_AND_SCOPE.md  source 11: repository pin, literature, scope
12-coefficient-field-rigidity-SOURCE_AUDIT.md             source 12: sources, novelty, dependency checks
13-theta-descent-PROOF_AUDIT.md               source 13: assumptions, proof dependencies, non-claims
13-theta-descent-SOURCES_AND_SCOPE.md         source 13: repository pin, literature, priority boundary
14-order-three-threshold-SOURCE_AUDIT.md      source 14: repository pin, prior manuscript, novelty, checkpoints
15-polynomial-composition-SOURCE_AUDIT.md     source 15: repository pin, files read, literature, novelty limits
16-theta-hierarchy-PROOF_AUDIT.md             source 16: hypotheses, dependency separation, proof checks
16-theta-hierarchy-SOURCES_AND_SCOPE.md       source 16: repository snapshot, public sources, priority limits
17-single-scale-PROOF_AUDIT.md                source 17: core mechanism, relation ideals, base fields, boundary
17-single-scale-SOURCES_AND_SCOPE.md          source 17: repository pin, literature, not-claimed-new list
18-unit-dilation-SOURCES_AND_SCOPE.md         source 18: repository pin and blob, literature, review priorities, non-claims
19-newton-rigidity-PROOF_AUDIT.md             source 19: assumptions, dependency chain, critical inequality, limits
19-newton-rigidity-SOURCES_AND_SCOPE.md       source 19: repository pin, files read, literature, priority limits
20-recurrences-SOURCE_AUDIT.md                source 20: repository pin and blob, the gap it addressed, literature, candidate-original list, checks
code/
  08-finite-recurrences-verify.py             source 08 checks (3,705)
  09-entire-hahn-holonomic-verification.py    source 09 checks (2,043)
  10-nonlinear-rigidity-verify.py             source 10 checks (2,113)
  10-nonlinear-rigidity-build.py              source 10's build script (see "Build and reproduce")
  11-coarsening-differential-rigidity-verify.py   source 11 checks (8,673 cases; needs SymPy)
  11-coarsening-differential-rigidity-build.py    source 11's build script (see "Build and reproduce")
  12-coefficient-field-rigidity-verify.py         source 12 checks (9,308)
  12-coefficient-field-rigidity-Makefile          source 12's Makefile (see "Build and reproduce")
  13-theta-descent-verify.py                      source 13 checks (1,622; needs SymPy)
  13-theta-descent-build.py                       source 13's build script (see "Build and reproduce")
  14-order-three-threshold-verify.py              source 14 checks (600; needs SymPy; run on a copy)
  15-polynomial-composition-Makefile              source 15's Makefile (see "Build and reproduce")
  15-polynomial-composition-verify.py             source 15 checks (2,369; needs SymPy; pass --output)
  16-theta-hierarchy-Makefile                     source 16's Makefile (see "Build and reproduce")
  16-theta-hierarchy-verify.py                    source 16 checks (standard library; pass --output)
  17-single-scale-build.py                        source 17's build script (see "Build and reproduce")
  17-single-scale-verify.py                       source 17 checks (8,608; needs SymPy; pass --output)
  18-unit-dilation-verify_finite.py               source 18 checks (16,579; standard library; pass --output)
  19-newton-rigidity-verify.py                    source 19 checks (259; needs SymPy; run on a copy)
  19-newton-rigidity-build.py                     source 19's build script (see "Build and reproduce")
  20-recurrences-build.sh                         source 20's build script (see "Build and reproduce")
  20-recurrences-verify.py                        source 20 checks (4,605; standard library; prints only)
data/
  08-finite-recurrences-verification.txt, 08-finite-recurrences-build_report.txt
  09-entire-hahn-holonomic-verification_results.txt, 09-entire-hahn-holonomic-build_report.txt
  10-nonlinear-rigidity-verification.json     recorded run of the source 10 checks
  10-nonlinear-rigidity-build_report.json     build log audit of the 23-page source 10 manuscript
  10-nonlinear-rigidity-layout_audit.json     page-layout audit of that manuscript
  11-coarsening-differential-rigidity-verification.json   recorded run of the source 11 checks
  11-coarsening-differential-rigidity-requirements.txt    sympy>=1.12,<2
  11-coarsening-differential-rigidity-build_audit.json    build audit of the 20-page source 11 manuscript
  12-coefficient-field-rigidity-verification.json         recorded run of the source 12 checks
  12-coefficient-field-rigidity-build_report.json         build report of the 23-page source 12 manuscript
  13-theta-descent-verification.json      recorded run of the source 13 checks (precision q^128)
  13-theta-descent-requirements.txt       sympy>=1.12,<2
  13-theta-descent-build_report.json      build and validation record of the 21-page source 13 manuscript
  14-order-three-threshold-verification.json   recorded run of the source 14 checks (through q^47)
  14-order-three-threshold-requirements.txt    sympy>=1.13,<2
  14-order-three-threshold-build_report.json   build and validation record of the 26-page A4 source 14 manuscript
  15-polynomial-composition-verification.json  recorded run of the source 15 checks (2,369 in 12 groups)
  15-polynomial-composition-requirements.txt   sympy==1.14.0
  15-polynomial-composition-BUILD_REPORT.json  build report of the 24-page source 15 manuscript
  16-theta-hierarchy-verification.json         recorded run of the source 16 checks (precision p^128)
  16-theta-hierarchy-build_audit.json          build audit of the 25-page source 16 manuscript
  17-single-scale-verification_results.json    recorded run of the source 17 checks (8,608 in 21 groups)
  17-single-scale-requirements.txt             sympy==1.14.0
  17-single-scale-build_audit.json             build audit of the 24-page source 17 manuscript
  17-single-scale-visual_audit.json            layout audit of that manuscript
  18-unit-dilation-finite_verification.json    recorded run of the source 18 checks (16,579 in 11 categories)
  19-newton-rigidity-verification.json         recorded run of the source 19 checks (259 in 17 groups)
  19-newton-rigidity-requirements.txt          sympy==1.14.0
  19-newton-rigidity-build_audit.json          build and layout audit of the 24-page source 19 manuscript
  20-recurrences-verification.txt              recorded run of the source 20 checks (4,605 in 12 families)
```

Every label in `article.tex` carries the prefix `hol:`; the nonlinear part
uses the sub-prefix `hol:nl:`, the coefficient-field part `hol:cf:`, the
theta-descent part `hol:td:`, the order-three-threshold part `hol:ot:`, the
unit-dilation part `hol:ud:`, the Newton-rigidity part `hol:nr:`, the
theta-hierarchy part `hol:th:`, the single-scale part `hol:fh:`, the
polynomial-composition part `hol:pc:` and the recurrence part `hol:rc:`.
The merge of sources 11 and 12 renamed or removed no label: the report had 199 labels before it and had 274 after it,
all 199 original labels still present. The later coefficient-field review
adds `hol:cf:cor:meromorphicmixed`, giving 275 labels while preserving every
earlier label and number. The merge of source 13 adds 85 labels, all with the
prefix `hol:td:`, giving 360; all 275 earlier labels are present and keep
their numbers (checked against the `.aux` files of the builds before and after
the merge). The merge of source 14 adds 52 labels, all with the prefix
`hol:ot:`, giving 412; all 360 earlier labels are present and keep their
numbers, checked the same way. The merge of sources 18 and 19 adds 116 labels,
67 with the prefix `hol:ud:` and 49 with `hol:nr:`, giving 528; all 412 earlier
labels are present and keep their numbers, checked the same way. The merge of
sources 16 and 17 adds 116 labels, 50 with `hol:th:` and 66 with `hol:fh:`,
giving 644; all 528 earlier labels are present and keep their numbers,
checked the same way. The merge of source 15 adds 56 labels, all with
`hol:pc:`, giving 700; all 644 earlier labels are present and keep their
numbers, checked the same way. The merge of source 20 adds 51 labels, all with
`hol:rc:`, giving 751; all 700 earlier labels are present and keep their
numbers, checked the same way. The audit files and programs keep the source
numbers `08` to `20` of the batches they arrived in (`15` to `19` are this
report's local numbers for batch 31's manuscripts 01, 02, 03, 05 and 08, and
`20` for batch 33's manuscript 01), and
the audit files keep their sources' own
notation and theorem numbering. No source manuscript is shipped.

## Why one report

Manuscripts 08 and 09 are one report written twice. Both prove the same
holonomic rigidity theorem, the same order-unit dilation criterion, the same
finite-step escape lemma, the same partial-theta sharpness witness, and the
same explicit counterexample series. **08 is the base** because it assumes only
`Γ ≠ 0`, while 09 assumes divisibility. Every proof taken from 09 was re-read
for a hidden division before it was attached to an 08 statement. Divisibility
now enters in three threshold constructions, and each prints the hypothesis itself
(Section 1.4):

1. the refined recurrence threshold of Corollary 3.5 (`hol:cor:periodic`),
   whose divisibility-free predecessor is Corollary 3.4 (`hol:cor:boundedcost`);
2. the refined coarsened threshold in Theorem 7.4 (`hol:thm:coarse`), which
   also states the divisibility-free form;
3. the worked sparse threshold of Example 13.1 (`hol:ex:sparse`), an
   instance of (1).

The torsion eigenspace equivalence, Proposition 9.1(c), now needs no
divisibility. The review below replaces root extraction by inward stability
of strong evaluation.

The divisibility-free predecessors are weaker in the constant only, not in the
conclusion. The nonlinear, coefficient-field, theta-descent, unit-dilation,
single-scale, polynomial-composition and recurrence parts use no divisibility; the order-three-threshold and
Newton-rigidity parts pass to the divisible hull `Γ ⊗ Q`, in which `Γ` is
cofinal, and transfer their conclusions back; the theta-hierarchy part works
in `Γ = R` only.

## Source 10: the nonlinear part

Source 10 (pinned at `048b72c`, where this report was exactly the 08+09
merge) answers the first-order case of the report's open nonlinear question,
then Question 15.1 and now Question 19.1 (`hol:q:nonlinear`). It forms
Sections 14–17, placed after the linear theory, with Theorem D in the
introduction. Its method is not the escape chain: at one large scale the
whole series leaves a finite initial polynomial, and a corner polynomial
controls its top coefficient.

- **Coefficient field.** Source 10 works over `k((t^Γ))` for any field `k`
  of characteristic zero; Sections 1–13 are stated over `C`. This generality
  is recorded for the nonlinear part only (Convention 14.1) and is **not**
  transferred to Theorems A–C, whose extension to other fields is the
  separate remark of Section 12.
- **Renamed symbols** (Section 14.1), to avoid collisions: `D, W → d_P, w_P`
  (`D_z` is the derivative), `H_P → χ_P` (`H ∈ Γ` in the linear part),
  `B_P → κ_P` (a rational cutoff, not an element of `Γ`), `r, r_0 → δ, δ_0`,
  `h_r, p_r → γ_δ, φ_δ`, `M → n_*`, `E_q → ϑ_q` (`E_η` is the formal
  exponential). Source 10's Theorems A, B, C are Theorem D,
  Theorem 16.5 and Theorem 16.1 here.
- **Printed once:** the support calculus (Lemma 2.1, Proposition 2.7), the
  cofinal-valuation criterion (Lemma 2.3(a)), the positive-support lemma
  (Lemma 2.1(2), which source 10 imports without proof), the surreal embedding
  (Section 2.4), strong entireness of `Σ ω^(−ω^n) z^n` (Theorem 11.2), its
  failure after enlarging the group (Section 11.2) and the `Γ = 0` remark
  (Section 12).

## Sources 11 and 12: the coefficient-field part

| | Manuscript | Pin | Contributes |
|---|---|---|---|
| **11** | *Coarsening Descent and Nonlinear Differential Rigidity for Entire Hahn–Surcomplex Functions* (20 pages) | `465a54b` | The all-order theorem for entire functions and for quotients of entire functions (Theorem E(a),(c)); coarsening descent for arbitrary coefficient fields (Theorem 21.11); rational systems and Painlevé I in the fraction field (Corollaries 21.16, 21.17); the joint-independence criterion (Theorem 22.2) and the continuum family (Theorem 22.6); Question 19.7. Files `11-coarsening-differential-rigidity-*`. |
| **12** | *Coefficient-Field Rigidity at Unbounded Surreal Scales* (23 pages) | `465a54b` | **The base.** The all-order theorem with dilations (Theorem E(a),(b)); the coefficient-value-rank criterion (Theorem F) and the order-unit dichotomy (Theorem G); the rank-one family (Theorem 21.20); all orders for `Σ ω^(−ω^n) z^n` (Theorem 22.1); Questions 19.8 and 19.9. Files `12-coefficient-field-rigidity-*`. |

Both manuscripts answer the no-order-unit case of Question 19.1 by the same
five steps, printed once in Sections 20–21 with both sources credited at each
statement: a minimal relation linearized along its solution puts all Taylor
coefficients into one finitely generated field (Theorem 21.2); the
valuation-rank inequality (Lemma 20.6); a principal convex bound, proper
without an order unit (Lemma 20.7); an exterior obstruction (Proposition 20.9);
and the same worked example, whose linearization multiplier along `a z^m` is
`a (T − m)^2` (Example 21.6). The hypotheses of the two are identical, so
**12 is the base** because its dilation theorem contains 11's entire-function
statement (the dilation set `{1}`), answers the no-order-unit case of Question
19.4, and has the exact order-unit boundary. Two of 11's proofs are genuinely
different and are kept as marked second routes: its minimal-order choice of
relation (Remark 21.3) and polynomiality through coarsened reduction (proof of
Theorem E). Every 11 proof was re-read before being attached; 11 has no
stronger standing hypothesis, its cardinal equality uses `k = C` while its lower
bound holds for every `k`, and its coefficient principle over a Laurent field
`k_0((z))` is kept because the joint-independence criterion needs it.

- **Placement.** The part forms Sections 20–22, after Section 19, so that
  Sections 1–19, Questions 19.1–19.6 and Theorems A–D keep their numbers (the
  shipped audits of 11 and 12 cite Questions 19.1 and 19.4). Its principal theorems are
  Theorems E–G in the introduction; its questions are 19.7–19.9.
- **Coefficient field.** Any field `k` of characteristic zero, as for the
  nonlinear part (Convention 20.1); not transferred to Theorems A–C.
- **Renamed symbols** (Section 20.1): `D → D_z`; `K, E → 𝕂, E_Γ(k)`;
  11's `M = Frac E → Frac E_Γ(k)` (`M(S)` is a support monoid); `H, H_δ, H_h →
  Δ, Δ_β`; 11's coarsened valuation `w`, residue field `L` and `res` →
  `v_Δ, k_Δ, red_Δ`; the offset and multiplier (11's `s, Q(T)`, 12's `ℓ, B(T)`)
  → `θ, Ξ(T)`; 12's coefficient-value rank `ρ(f) → cvr(f)` (`ρ` is the
  residue of Lemma 14.2); 11's branch series `F_α → 𝓕_α`; 12's `F_ω → F`,
  `Θ_u → Θ_p`, `E_h → E_η`, `F_τ → R_τ`; 12's Theorems A, B, C → Theorem E(a),(b),
  F, G. Dilation means argument dilation `f(z) ↦ f(λz)` throughout; the order
  "differentiate, then dilate" of `(D_z^j f)(λz)` is stated against `D_z^r σ_q^ℓ`
  of equation (10.1), which differs by the scalar `q^(ℓr)`.
- **Printed once:** the definition of strong summability, the sufficiency half
  of the all-scale criterion (Lemma 2.3(a)), closure of entire series under
  derivatives and dilations (Proposition 2.7), the surreal embedding (Section
  2.4), `Γ_∞` and strong entireness of `F` (Theorem 11.2), its failure after
  adjoining `e_* = ω^ω` (Section 11.2), the formal-exponential domain
  (Proposition 5.3) and the positive-characteristic failure (Example 17.3).
  The necessity half of the all-scale criterion is new to this report
  (Proposition 20.2).
- **Disclosed discrepancy.** Source 11 indexes `Γ_∞` from 1 and calls
  `f_* = Σ_{n≥1} ω^(−ω^n) z^n` "this exact entire example" of the report. The
  report's `F` of Theorem 11.2 starts at `n = 0`, so `F = f_* + ω^(−1)`: off by
  a constant, harmless for every jet statement, disclosed in Section 20.1 and
  not corrected in the shipped audit files.
- **A merge observation.** Source 12 does not claim Question 19.6. Checked for
  this merge: a group generated by multiplicatively independent parameters is
  torsion free, so its distinct elements have quotients that are not roots of
  unity, and Theorem E(b) applies (Corollary 22.8). The later review combines
  source 12's coefficient theorem and source 11's descent to prove the mixed
  statement for nonrational quotients of entire series (Corollary 22.9).
  Neither delivered source states that additional consequence.

## Source 13: the theta-descent part

| | Manuscript | Pin | Contributes |
|---|---|---|---|
| **13** | *Theta Descent and the Exact Boundary of Differential Rigidity* (21 pages, 23 September 2026) | `4cdeaec` | The exact boundary (Theorem H); the series `𝒯_p = 1 + Σ_{n≥1} p^(n²) C_n(z)`, its Taylor coefficients, exact strong domain, product, zeros and local valuations (Section 23); its cleared third-order equation and the elliptic identity behind it (Theorem 24.1); algebraic independence of `𝒯_p, 𝒯_p', 𝒯_p''`, the differential field and non-D-finiteness (Theorems 24.8, 24.10, Corollary 24.9, Proposition 24.11); surreal, omnific and example consequences (Sections 25.3–25.4); Question 19.10. Files `13-theta-descent-*`. |

Source 13 answers Question 19.1 (`hol:q:nonlinear`) in the case sources 11
and 12 left open, groups with an order unit. At its pin `4cdeaec` this report
was exactly the five-source text (no commit touched the directory between the
pin and the placement), so its references to Question 19.1, its statement and
status passage, Theorem E and the coefficient-field part were accurate.

- **Placement.** The part forms Sections 23–25, after Section 22, so that
  Sections 1–22, Questions 19.1–19.9 and Theorems A–G keep their numbers; the
  conclusion became Section 26 (Section 28 since the merge of source 14). Its principal theorem is Theorem H in the
  introduction, and its one new question is Question 19.10.
- **Coefficient field.** Any field `k` of characteristic zero, as for the two
  previous parts (Convention 23.1); not transferred to Theorems A–C.
- **Renamed symbols** (Section 23.1): the variable `x → z`; `h, q = t^h → μ,
  p = t^μ`; `H_h, D_h → Δ_μ, O_{Δ_μ}`; `F_q → 𝒯_p` (`F` is the series of
  Theorem 11.2); the bilateral `Θ_q → Ψ_p` (`Θ_p` is the partial theta series);
  zeros `r_m → x_m`; `Q = q², s_r(Q), c → p², 𝒬_r(p²), 𝔠`; `A_f, H_f, J_f,
  B_f → 𝒜[f], ℋ[f], 𝒦[f], ℬ[f]`; `δ = u d/du, s = u − u⁻¹ → ϑ_u, ž`;
  `σ, τ → 𝖲, 𝖲_a`; the Laurent ring `𝒜 → 𝒰_μ`; `L, A, V (in u) → ψ_1, ψ_2,
  ψ_3`; `ℓ, B = A', R(T) → 𝓛, 𝒜_1, Φ(T)`; the Newton profile `w_γ` is the
  coefficient Gauss value `γ_δ`; `No(i) → No[i]`; source 13's Theorem 1.2 is
  Theorem H. The shipped audit files keep the source's notation.
- **Printed once:** the definitions of an order unit and of strong
  summability, the cofinal-valuation lemma (Lemma 2.3(a)), the positive-support
  lemma (Lemma 2.1(2)), the surreal embedding (2.4), the bilateral theta
  domain (the Hahn–Tate report's `tate:thm:theta`, since `Ψ_p(u)` is that
  report's theta series at the nome `p²` and argument `−pu`), and source 13's
  Section 7, the no-order-unit direction, which is Theorem E(a) (its
  Euler-derivative presentation is recorded in Remark 25.1). For `k = C`,
  non-D-finiteness of `𝒯_p` is also a case of Theorem A; source 13's proof,
  valid for every `k`, is kept.
- **Two steps written out by the merge.** Lemma 24.5 states and proves that
  substituting `z = u + u⁻¹` is a ring homomorphism from the strongly entire
  series into the Laurent ring `𝒰_μ`, compatible with `ϑ_u = ž D_z`; source
  13's minimal-order proof used this without stating it. Lemma 24.7 replaces
  source 13's "formal meromorphic germs" argument for `ψ_3 = ϑ_u ψ_2 ≠ 0` by
  the global identity `Ψ_p³ ψ_3 = p(u − u⁻¹) + O(p²)`, transferred to the Hahn
  field by the injective map `p ↦ t^μ`. The passage from the complex elliptic
  identity to `k((t^Γ))` is written as three ring maps (Section 24.3).
- **Merge additions** (marked "merge"): the corner data of the cleared
  equation (Proposition 24.2: `d_P = 6`, `w_P = 0`, `χ_P = 0`, and
  `I_P = −(4𝔠³ − g₂𝔠 − g₃) = 4p² + 48p⁴ + …`, a nonzero constant, so
  `I_P ≠ 0` alone does not force polynomiality; the weight-zero part of `ℋ` is
  the vanishing-corner equation of Proposition 16.4); clause (iv) of Theorem G
  ("some nonpolynomial `f ∈ E_Γ(k)` is differentially algebraic"), proved in
  Section 25.1 from Theorem H; Corollary 25.2 (Theorem E(a) and (c) hold
  exactly when there is no order unit, and with one `𝒯_p` gives the mixed
  dependence of Theorem G(iii) for every nontorsion `q`, including
  `v(q) = 0`); and the consistency statements of Section 25.2.
- **Consistency.** Without an order unit `𝒯_p` is not entire, so Theorem E
  is not contradicted; its domain equals the necessary region of Proposition
  20.9. Theorem D (order one) and the corner criterion hold (`χ_P = 0`).
  `cvr(𝒯_p) = 1`, so Theorem F does not apply. The coefficient values of `𝒯_p`
  lie in `Zμ`, whose convex hull is all of `Γ`, so the descent theorem does not
  apply. `Θ_p` and `G` are untouched; whether they are differentially
  algebraic stays open. Question 19.4 (linear mixed equations at unit
  valuation) stays open. Question 19.8 stays open; `𝒯_p` shows what any answer
  must avoid.
- **Verified for this merge.** The source 13 suite was rerun on a copy
  (Python 3.14.4, SymPy 1.14.0) and reproduced its record apart from the
  interpreter version and elapsed time. An independent SymPy script (not
  shipped) checked the cleared equation and the product modulo `p^50`, the
  expansions of `𝔠, g₂, g₃`, the rational forms, the identities behind Lemmas
  24.5 and 24.7, and the corner data (19 corner monomials).

## Source 14: the order-three-threshold part

| | Manuscript | Pin | Contributes |
|---|---|---|---|
| **14** | *The Order-Three Threshold for Entire Hahn–Surcomplex Functions: Second-order rigidity, Newton-corner spectra, and sharp theta examples* (26 pages, A4, 23 September 2026) | `b895e86` | Second-order rigidity for every value group and the exact least order three (Theorem I); cofinal scalar extension, local finiteness and late breaks, the exterior form and the finite endpoint lemma (Lemmas 26.2–26.5, 26.8); three-jet transcendence, two-state systems, polynomial-denominator quotients (Corollaries 26.9–26.11); the third-order endpoint–gap obstruction and certificate (Theorem 27.2, Corollary 27.3); the exterior form of the theta equation, the classification of its polynomial solutions and eventual Newton convexity (Section 27.2, Theorems 27.4, 27.5); the full-class boundary (Proposition 27.6); Questions 19.11–19.18. Files `14-order-three-threshold-*`. |

Source 14 answers Question 19.1 (`hol:q:nonlinear`) as it stood after source
13: no nonpolynomial strongly entire series satisfies a nonzero algebraic
differential equation of order at most two, for **every** ordered value group
and every coefficient field of characteristic zero, whatever the residue
corner. With Theorem H, the least order is exactly three when `Γ` has an order
unit. At its pin `b895e86` this report's article and README were still the
five-source text (source 13's audit, code and data files had been placed, but
its manuscript was not yet merged); source 14 read this README there and took
source 13 from the author's file library, answering its question `q:order2`,
which is the question merged into 19.1. Its statements about this report were
accurate at the pin.

- **Placement.** The part forms Sections 26–27, after Section 25, so that
  Sections 1–25, Questions 19.1–19.10 and Theorems A–H keep their numbers; the
  conclusion is now Section 28. Its principal theorem is Theorem I in the
  introduction, and its eight further questions are Questions 19.11–19.18.
- **Coefficient field.** Any field `k` of characteristic zero (Convention
  26.1); not transferred to Theorems A–C. Divisibility of `Γ` is used only
  after a cofinal extension to `Γ ⊗ Q` (Lemma 26.2), and the conclusions are
  transferred back.
- **Renamed symbols** (Section 26.1): radius `r → δ`; `α_f(r), φ_r, I_f(r),
  m_f(r), N_f(r) → γ_δ, φ_δ, Act_δ, N̲_δ, N_δ` (the Gauss data of the nonlinear
  part); "Newton corner" → **break** (a *corner* stays the finite term
  selection of Section 14.4); the exterior homogeneous polynomial `H → 𝔥_P`;
  `Q, R, s, S_H → 𝔮, 𝔯, i_0, Sp(𝔥)`; `u, V_φ, W_φ → 𝗎_φ, 𝗏_φ, 𝗐_φ`;
  `χ_H(T,G) → Υ_𝔥(T,G)` (not the residue corner `χ_P`); gaps `g, e → 𝗀⁺, 𝗀⁻`;
  `q = t^h, Q = q², s_r(Q), c, F_q, H_f, J_f, B_f → p = t^μ, p², 𝒬_r(p²), 𝔠,
  𝒯_p, ℋ, 𝒦, ℬ`; `r_n → δ_n`; `F = g/p → F_0 = g/𝗉`; the characteristic
  `p → 𝔭`; `L → 𝔏`; source 14's Theorems 1.1 and 1.3 are Theorem I(a),(b).
  The shipped audit file keeps the source's notation.
- **Printed once:** the all-scale criterion (Proposition 20.2); the restricted
  series ring and its reduction (Lemma 14.2); the first half of its escape
  lemma (Lemma 14.5); its Proposition 5.2, which is the vanishing-corner
  equation of Proposition 16.4; its Painlevé corollary (Proposition 16.3; its
  route through Theorem I is Remark 26.12); its Section 8, the theta example
  (Theorems 23.5, 24.1, Sections 24.2–24.3), except the minimality argument,
  kept as a second route (Remark 26.14); its Section 10, the no-order-unit
  direction (Theorem E(a), Remark 25.1); its Examples 10.4–10.5 (Examples 25.6,
  25.5); the surreal witness, zeros and omnific rounding (Section 25.3,
  Theorem 23.6, Corollary 25.3); its positive-characteristic example
  (Example 17.3); the `Γ = 0` remark (Section 12).
- **Merge additions** (marked "merge"): the exterior form is the residue
  corner written in Euler jets, and its values on monomials are `χ_P`
  (Remark 26.6), which connects the endpoint lemma to the corner criterion of
  Theorem 16.1; the late break is named explicitly (Lemma 26.4); Corollaries
  26.9–26.10 are stated in a differential field containing `𝕂((z))`; `𝒯_p` is
  an observable of a four-state rational system, so two states cannot be
  raised to four with an order unit; and Corollary 26.13 gives three
  independent jets for `Σ t^(n²) z^n` and for `Θ_p`.
- **Consistency.** Theorem I contains the polynomiality conclusions of Theorem
  D and of Theorem 16.1 in orders at most two, but not their exclusion bounds.
  For the theta equation the dehomogenized exterior form is `W² − V² + 4V³`,
  whose value at `V = W = 0` is `χ_P = 0`, as in Proposition 24.2. Its
  endpoint–gap polynomial is `G² − 1`, and the breaks of `𝒯_p` are
  `δ_n = (2n+1)μ` with initial polynomials `X^n(1 + X)`, as in the Newton
  profile of Section 23.4.
- **Verified for this merge.** The source 14 suite was rerun on a copy
  (Python 3.14.4, SymPy 1.14.0) and reproduced its record apart from the
  interpreter version and the elapsed time. The Sebbar reference's
  bibliographic data were checked against Crossref; its content was not.

## Source 18: the unit-dilation part

| | Manuscript | Pin | Contributes |
|---|---|---|---|
| **18** | *Unit-Dilation Rigidity at Surreal Scales: A valuation form of Skolem–Mahler–Lech and an exact relative-scale criterion for mixed differential–dilation equations* (26 pages, A4, 23 September 2026; batch 31, manuscript 05, archive `Surreal_Unit_Dilation_Rigidity`) | `bcac55a` | The finite-word lemma with proof (Lemma 28.2); one period for residue torsion (Lemma 28.3); the support envelope, eventually periodic valuations at unit valuation and the bivariate estimate for `v(P(n, q^n))` (Lemma 28.4, Theorem 28.5, Corollary 28.7); periodic-affine valuations of Hahn exponential polynomials (Theorem 28.10); exact shift polynomials, rigidity for noncofinal relative scales, the answer to Question 19.4, mixed linear independence (Lemma 29.1, Theorem 29.4, Corollaries 29.6, 29.7); the relative-scale dichotomy and the cyclic mixed criterion (Theorem 29.9, Corollary 29.11) and the top Archimedean scale (Proposition 29.12); surcomplex corollary, examples and boundaries (Sections 29.4–29.5); the finite solution space (Proposition 29.18); Theorem J; Questions 19.19–19.29. Files `18-unit-dilation-*`. |

Source 18 answers Question 19.4 (`hol:q:mixedunit`) **positively, for every
value group**: for nontorsion `q` with `v(q) = 0`, every strongly entire
solution of a nonzero mixed equation in `D_z` and powers of `σ_q`, with
polynomial or rational forcing, is a polynomial, with a uniform degree bound
and exterior obstruction for each equation. More generally, for multipliers
`λ_1, …, λ_m` with no root-of-unity quotient, some nonzero mixed linear
equation supported on them has a nonpolynomial strongly entire solution
**iff** some `|v(λ_i/λ_j)|` is an order unit; two multipliers and first
derivatives then suffice (Theorem J). This partly answers Question 19.6
(existence of *some* equation; not prescribed operators or systems). Its pin
`bcac55a` is a commit; `86fc492…` in its scope file is the blob of this
report's `article.tex` there, when the report was the five-source text
(sources 08–12). Its description of the report was accurate at the pin; its
"higher-order nonlinear equations with an order unit: left open" and its
Research question 11.1 are stale now (answered by Theorems H and I and
Corollary 25.2; Remark 29.19).

- **Placement.** Sections 28–29, after Section 27, so that Sections 1–27,
  Questions 19.1–19.18 and Theorems A–I keep their numbers; the conclusion is
  now Section 32. Principal theorem: Theorem J in the introduction; questions
  19.19–19.29.
- **Coefficient field.** Any `k` of characteristic zero (Convention 28.1); the
  part contains Theorem A, the negative direction of Theorem B and Theorem
  10.2 as special cases over every such `k` (Remark 29.5). No divisibility.
- **Renamed symbols** (Section 28.1): `K → 𝕂`, `D → D_z`; multipliers
  `u_j → λ_j`, `u = c(1+ε) → λ = ζ(1+τ)`; `A(n) = Σ P_j(n)u_j^n → 𝒴(n) =
  Σ R_j(n)λ_j^n`; recurrence coefficients `A_j(n), Q_{j,ℓ} → c_j(n), R_{j,ℓ}`;
  coefficient polynomials `Q_{j,γ} → r_{j,γ}`; envelope `T → Σ`; shift
  `S → Sh`; period `M → 𝖬`, residue class `r → b`; slopes `λ_r → ϖ_b`;
  relative scale `μ → rs(λ_1, …, λ_m)`; noncofinality witness `η → γ`;
  operator coefficients `c_{ℓ,r,k} z^k → ϰ_{ℓ,r,i} z^i`, output index
  `m → n̄`; right side `h → 𝗁`, `deg h ≤ e → deg 𝗁 ≤ ē`; `Θ_q → Θ_p`; order unit
  `H → μ`, `H_* → e_*`, `F → G_μ`, `G → G_μ(z^h)`; maximal proper convex
  subgroup `Δ → Δ^top`. The shipped scope file keeps the source's notation.
- **Printed once:** its support lemmas (Lemmas 2.1–2.3), except its proof of
  the finite-word lemma, printed as Lemma 28.2 because the report imports that
  lemma from Higman; its exponential-polynomial independence and zero-set
  lemma (Lemma 21.1); the imported Skolem–Mahler–Lech theorem; its escape
  theorem, exterior corollary and jump-sensitive certificate (Lemma 3.1,
  Theorem 3.3, Corollary 3.4, the last with the closed region); the partial
  theta domain (Theorem 8.1); its Example 4.8 (Remark 4.3); its parity example
  (Example 4.6); its torsion example (Section 9); its positive-characteristic
  series (Example 17.3); the `Γ = 0` remark (Section 12).
- **Merge additions** (marked "merge"): Remark 29.5 (what Theorem 29.4
  contains, and the comparison with Theorem E(b)); the closed exterior region
  in Theorem 29.4; Remark 29.19 (source 18's nonlinear question is answered
  negatively by `𝒯_p`, whose order-three relation fails for `f = z`); the
  reading of Corollary 29.11 beside Theorem B (derivatives add no existence
  case).
- **Stale text corrected in this report:** Section 10 (the remark after
  Theorem 10.2), the tables of Section 11.3, the ledger and the statuses of
  Questions 19.4 and 19.6 in Section 19, Section 22.5, the consistency list of
  Section 25.2, Appendix B's exclusions and this README.
- **Verified for this merge.** The source 18 suite was rerun on a copy
  (Python 3.14.4) and reproduced its record exactly (the record names no
  interpreter). The proofs were re-read against the statements they are
  attached to.

## Source 19: the Newton-rigidity part

| | Manuscript | Pin | Contributes |
|---|---|---|---|
| **19** | *Low-Order Nonlinear Rigidity at Surreal Scales: Newton transitions, Euler-jet geometry, and omnific coefficient descent* (24 pages, US letter, 23 September 2026; batch 31, manuscript 08, archive `surreal_newton_rigidity`) | `3d40856` | An independent re-derivation of Theorem I(a), printed once (its route: Remark 30.2); the first polar and its double factor, the eventual-side lemma, the first-polar criterion, the secant lemma and the factor criterion (Definition 30.3, Lemmas 30.4–30.5, Proposition 30.6, Lemma 30.7, Corollary 30.9); Theorem K; external constants, surcomplex and Gaussian-omnific coefficients (Corollaries 30.12–30.15, Lemma 30.14); algebraic two-state systems (Theorem 30.16, Corollary 30.17); the exact classifications of `𝖧_3` and `𝖰_4` and the sparse series (Theorems 31.1–31.2, Example 31.3); the order-unit family (Proposition 31.5); Questions 19.30–19.35. Files `19-newton-rigidity-*`. |

Source 19's principal claim, second-order rigidity for every value group and
every differential degree, is **Theorem I(a)** of source 14, with identical
hypotheses and in substance the same proof (break construction, exterior
reduction with the same sign-sensitive inequality, and the conic
factorization `𝔥 = 𝔰^e 𝔥_1`, which is the endpoint lemma in homogeneous
coordinates since `𝔰(1, U, U² + V) = V`); the two were written the same day,
each against a text without the other, and no priority is asserted. It is
printed once. New: **Theorem K**, no nonpolynomial strongly entire solution of
an equation of order three and total jet degree at most three, for every
`Γ`. At its pin `3d40856` the report was the five-source text; its abstract's
"the unrestricted all-order, order-unit case is not resolved" and its
Question 12.1 are answered negatively by Theorem H.

- **Placement.** Sections 30–31; principal theorem Theorem K; questions
  19.30–19.35. Its Questions 12.4, 12.6, 12.8 are Questions 19.15–19.17
  (status notes added); 12.1 is answered.
- **Coefficient field.** Any `k` of characteristic zero (Convention 30.1);
  divisibility only through the cofinal extension to `Γ ⊗ Q`.
- **Renamed symbols** (Section 30.1): `∂ → D_z`, Euler `𝖤 → ϑ`; `α_n, I_δ,
  F_δ → v(a_n), Act_δ, t^(−γ_δ) f(t^(−δ)X)`; Newton transition → break;
  `D, W, μ` and the residue corner `H` → `d, w, β` and the exterior form `𝔥_P`;
  `c_2, c_3, c_r → 𝐦_2, 𝐦_3, 𝐦_r`; `S = Y_0Y_2 − Y_1² → 𝔰`, `H = S^e Q →
  𝔥 = 𝔰^e 𝔥_1`; `χ_H → χ_𝔥`; first polar `A_H, a, b → Pol_𝔥, a_𝔥, b_𝔥`;
  `H_3, Q_4, B(m,n) → 𝖧_3, 𝖰_4, 𝖡(m,n)`; `A(N), B(N), N → 𝖠_1(𝗇), 𝖠_2(𝗇), 𝗇`;
  `U = 𝖤f/f → 𝗎_f`; constants `L → 𝕃`, fields `F, F_1 → 𝔐, 𝔐_1`, minimal
  polynomial `q → 𝗆`; order unit `u → μ`, `c_n → b_n`, its
  `Θ(z) = 1 + t^u zΘ(t^(2u)z)` → `G_μ(z) = Θ_(p²)(pz)`, `p = t^μ` (not `Θ_p`);
  the field `F` of its Section 10 → `K_0`, `p = a_m z^m + a_(2m) z^(2m) → 𝖽_0`;
  characteristic `p → 𝔭`; its Theorems A, B, C → Theorem I(a), Theorem K,
  Corollary 30.12 with Theorem 30.16. The shipped audit files keep the
  source's notation.
- **Printed once:** Theorem A (Theorem I(a)); its all-scale criterion
  (Proposition 20.2), closure (Proposition 2.7), cofinal extension (Lemma
  26.2), escape of active support (Lemma 14.5), break construction (Lemma
  26.4), exterior reduction (Lemma 26.5), conic lemma and proposition
  (Lemma 26.8, Remark 30.2); its degenerate example (Proposition 16.4);
  its finite linear descent (Proposition 22.7, whose basis proof preserves
  total degree); the full-class obstruction (Proposition 27.6); the embedding;
  its characteristic-`p` and `Σ z^n/n!` examples (Example 17.3, Section 27.4,
  equation (2.3)).
- **Merge additions** (marked "merge"): Remark 30.11 — with `χ = 0` the first
  polar is nonzero exactly when `i_0 = 1`, then
  `Υ_𝔥(T, G) = a_𝔥(T)(T − G) + b_𝔥(T)` and source 19's two linear conditions
  are the two endpoint conditions of Theorem 27.2; the cubic
  `2Y_0²Y_3 − 5Y_0Y_1Y_2 + 3Y_1³` (first polar `(U − T)²(2U − T)`,
  `Υ = T − 2G`) is covered by Theorem K but not by Corollary 27.3, which uses
  the upper endpoint only; Corollary 31.4 — `𝒯_p` satisfies no equation of
  order three and jet degree ≤ 3, its explicit equation has degree six, so the
  least such degree is 4, 5 or 6 (irreducibility of that equation not
  checked), and its exterior form `W² − V² + 4V³` has `i_0 = 2` and vanishing
  first polar; the sparse series is a negative instance for Question 19.11;
  `𝖧_3` has `Υ = (G + T)(2G − T)`; the comparison of Theorem 30.16 (entire
  states, algebraic right-hand sides, external constants) with Corollary
  26.10 (rational systems, arbitrary states).
- **Verified for this merge.** The source 19 suite was rerun on a copy
  (Python 3.14.4, SymPy 1.14.0) and reproduced its record apart from the
  recorded interpreter version (recorded run: Python 3.13.5). The resultant
  identity, the identity `Y_0𝖠_2 − Y_1𝖠_1 = −3𝔰𝗇 + (Y_0Y_3 − Y_1Y_2)`, the
  pair kernel, `[z^5]𝖰_4 = −126 t^17`, the secant Jacobian, the first polars
  and endpoint–gap polynomials above were rechecked with an independent SymPy
  script, which is not shipped.

## Source 16: the theta-hierarchy part

| | Manuscript | Pin | Contributes |
|---|---|---|---|
| **16** | *Independent Theta Families and Unbounded Differential Order in Hahn–Surcomplex Analysis: Valuation growth, bounded polynomial jet compression, and a continuum-sized differential-algebraic function field* (25 pages, A4, 23 September 2026; batch 31, manuscript 02, archive `Surreal_Theta_Hierarchy`) | `0fffc26` (a snapshot recorded while the repository was changing) | Polynomial growth, the exact quadratic Gauss profile of `𝒯_(t^μ)`, superlinear growth separation, a noncancellation threshold and its example (Lemma 32.2, Theorems 32.3–32.4, Proposition 32.5, Example 32.6); the Kähler criterion, grid lemma and bounded polynomial jet compression (Lemmas 32.7–32.8, Theorem 32.9, Remark 32.10, Example 32.11, Corollary 32.12); minimal differential order, finite composita, no finite bound, the exact order at the compositum dimension (Definition 32.13, Lemma 32.14, Corollaries 32.15–32.16, Remark 32.17, Theorem 32.19); the continuum family and field (Lemma 33.1, Corollary 33.2, Lemma 33.3); integer sampling (Theorem 33.5, Corollaries 33.6–33.7); a third route to order three (Theorem 33.8, Corollary 33.9); Theorem L; Questions 19.36–19.44. Files `16-theta-hierarchy-*`. |

Over `𝕂 = k((t^R))`, `k = R` or `C` (**`Γ = R` only**): the theta descents
`𝒯_(t^μ)` of Theorem H at scales `μ` with `Q`-independent reciprocals are
algebraically independent (a family of size `2^ℵ0`), since their Gauss values
are `−δ²/(4μ) + O(1)`; polynomially weighted sums
`Σ_i (Σ_(j<N) c_ij z^j) 𝒯_(t^(μ_i))` with `c_ij ∈ {0,…,N}`, `μ_i = 1/√p_i`,
include one of minimal order in `[N, 3N]`; so minimal orders are unbounded,
and the differentially algebraic strongly entire series generate a field of
transcendence degree `2^ℵ0` and differential transcendence degree 0 (Theorem
L). At its snapshot the article was the five-source text and source 13's
audit files were placed; source 16 credits the seed, its equation and its
minimal order three to source 13. Its Question 11.2 (order two) and the
statement that order two is unresolved are stale: Theorem I answers them.

- **Placement.** Sections 32–33, after Section 31, so that Sections 1–31,
  Questions 19.1–19.35 and Theorems A–K keep their numbers; the conclusion is
  now Section 36. Principal theorem: Theorem L; questions 19.36–19.44.
- **Renamed symbols** (Section 32.1): `X → z`, `∂ → D_z`; `h → μ`, `q = t^h →
  p = t^μ`, `Q = q² → p²`, `s_k → 𝒬_k(p²)`; `F_h → 𝒯_(t^μ)`; the Laurent
  variable `z → u`, `Θ → Ψ_p`, `D → ϑ_u`, `G → ψ_1`, `H → 𝗑 = −ψ_2 − 2𝒬_1(p²)`,
  `Y → ž`; `Δ = X² − 4 → z² − 4`; its `A, B → ℬ[f] − f²/12, ℋ[f]`; radius
  `r → δ`, `w_r → γ_δ`; `ord_∂ → dord`; `𝔠 = 2^ℵ0 → 2^ℵ0` (`𝔠` is a theta
  constant); in compression `F ⊆ L, s, a_i, p_i, c_ij, W, U_ir, λ_i → 𝔎_0 ⊆
  𝔎_1, 𝗌, y_i, 𝖯_i, 𝖼_ij, 𝖶, 𝖴_ir, ε_i`; primes `p_i → p_i` (roman);
  threshold data `m, A_m, B_m, … , R_0, R → e, κ_e, κ'_e, …, δ^(0), δ^cert`;
  Hamel set `B → 𝔙`; `𝒜, 𝒟 → 𝒜_DA, 𝒟_DA`; sampling `G, w_0(G), Ḡ → g, γ_0(g),
  φ_0`; `ℒ, w, σ → 𝒰_μ, γ^𝒰, 𝖲`. The shipped audit files keep the source's
  notation.
- **Printed once:** escape lemma (Lemma 2.3(a)), entireness (Definition 1.2,
  Proposition 20.2), closure (Proposition 2.7), Gauss multiplicativity
  (Corollary 14.3), seed coefficients (Proposition 23.3), product (23.12),
  seed equation (24.7), failure at `ω^ω` (Section 25.3), Laurent ring and
  shift (Lemma 24.4, (23.10)), integer-evaluation lemma (Lemma 4.1), the
  embedding. Source 16's Tate-normalized equation, with `𝖠 = ℬ[f] − f²/12`,
  `g_2 = 1/12 − 4a_4`, `g_3 = −1/216 + a_4/3 − 4a_6`, **is** the cleared
  equation (24.7) as a polynomial identity (checked with SymPy).
- **Merge additions** (marked "merge"): the identity of the two seed
  equations; Remark 32.18 (with Theorems I and K the order spectrum lies in
  `{3, 4, …}`, contains 3, is unbounded; `d_N ≥ max(N, 3)`); Remark 33.4
  (with source 17's family, `dtrdeg FE = 2^ℵ0` also over `k((t^R))`, while its
  differentially algebraic part has `trdeg 2^ℵ0`, `dtrdeg 0`); Remark 33.10
  (three routes to minimal order three: source 13's three field-theoretic
  obstructions, source 16's quadratic valuation growth of shift iterates,
  proved for `Γ = R`, `k = C` only, and source 14's universal second-order
  rigidity).
- **Stale text corrected in this report:** the remark after Corollary 25.7
  ("classifies neither … nor the possible minimal orders"), the status of
  Question 19.1, Section 19's ledger, Section 18, Appendix B and this README.
- **Verified for this merge.** The source 16 suite was rerun on a copy
  (Python 3.14.4) and reproduced its record apart from the elapsed time (the
  record names no interpreter).

## Source 17: the single-scale part

| | Manuscript | Pin | Contributes |
|---|---|---|---|
| **17** | *Differential Freedom at a Single Surreal Scale: Factorial-height entire functions, exact relation ideals, and omnific codes* (24 pages, A4, 23 September 2026; batch 31, manuscript 03, archive `single_scale_surreal_research`) | `bcac55a` | Rapid heights, height separation, bands, polarization, density (Definition 34.2, Lemma 34.3, Corollary 34.4, Lemma 34.5, Example 34.6, Lemma 34.7); joint numerical and mixed independence (Definition 34.8, Theorems 34.9–34.10, Corollary 34.11, Remark 34.12); the exact relation ideal, jet degrees, examples, finite alphabets (Theorem 34.13, Corollary 34.14, Examples 34.15–34.16, Corollary 34.17); all scalars in the equation (Theorem 34.18, Remark 34.19); entire freedom at one order-unit scale, continuum field, Hermite data (Theorem 35.1, Corollary 35.3, Theorem 35.4); Berarducci–Mantova jets and bounded-support descent (Lemma 35.5, Theorem 35.6, Lemma 35.7, Corollary 35.8, Remark 35.9); the exact domain in `No[i]` (Theorem 35.10, Propositions 35.11, 35.13, Remark 35.14); omnific codes and floors (Lemma 35.15, Theorem 35.16, Remark 35.17, Theorem 35.18); the polynomial-height obstruction (Proposition 35.19); Theorem M; Questions 19.45–19.54. Files `17-single-scale-*`. |

For heights `𝖻_n` with `𝖻_n/𝖻_(n−1) → ∞` (e.g. `n!`) and
`𝒢_A(p, z) = Σ_(n∈A) p^(𝖻_n) z^n`: after explicit finite polynomial
corrections, the whole differential relation ideal of any finite family over
`k(p, z)` (derivations `z d/dz`, `p d/dp`) is generated by the linear
relations among the membership patterns that recur infinitely often; with an
order unit `μ` and `p = t^μ`, every infinite subseries is a nonpolynomial
strongly entire series **satisfying no algebraic differential equation over
`𝕂(z)`**, although its coefficients lie in `Q(p)` and its coefficient values
span `Qμ` (Theorem M). This fills the gap recorded after Theorem 21.20
(coefficient-value rank one, `C((t^Q))`); `Θ_p` and `Σ t^(n²) z^n` (quadratic
heights) are not decided. Single-series gap differential transcendence is
classical (Grönwall, via Ostrowski 1920) and not claimed. At its pin the
report was the five-source text; its "the general order-unit question remains
open" and Question 12.1 are stale (answered by Theorems H and I).

- **Placement.** Sections 34–35; principal theorem Theorem M; questions
  19.45–19.54.
- **Renamed symbols** (Section 34.1): formal `q → p`, `q = t^η → p = t^μ`,
  `η → μ`; `δ = q d/dq → ϑ_p`, `Θ → ϑ`, `D → D_z`; `S_A → 𝖭_A`,
  `F_A → 𝒢_A` (`𝓕_α` is source 11's branch family), heights `b_n → 𝖻_n`;
  `E(K) → E_Γ(k)`; patterns `v_n, T_v, E_0, p(q,z), s(q), V, d, λ_j, L → 𝐯_n,
  A_𝐯, A_fin, 𝖼, 𝖼_0, 𝖵, d_pat, ℓ_j, 𝖫`; Lemma 3.1's `D, H, T, U, k → d̄, h̄,
  𝐓, 𝐔, n_*`; polarization `L, Q, J, U, X, W_Q → 𝔎, 𝔓, 𝒥, ε, 𝐱, 𝖶_𝔓`;
  domain `𝒟 → 𝒪_⟨1⟩`; `ℬ_Γ(k), ℱ_Γ(k) → ℬ^bd_Γ(k), ℱ^bd_Γ(k)`; `ξ_A → 𝔵_A`
  (the tail-span report's `ξ_A` differ); `Λ, M, Z_A, I_A → Ω, M_Ω, 𝔷_A, 𝖨_A`;
  Hermite `a_i, m_i, c_ij, M, H_α, P, G_α → x_i, e_i, 𝗒_ij, ē, 𝖱_α, 𝖱_0,
  𝒢*_α`; `h(n) → 𝗁(n)`; `𝔠 → 2^ℵ0`. The shipped audit files keep the
  source's notation.
- **Printed once:** the entire class (Proposition 20.2), the entire ring
  (Proposition 2.7), the Euler–Stirling change (26.2), support facts (Lemma
  2.1), constant extension (the argument of Proposition 22.7 over `Q(p)`; the
  source's coefficient-minor proof is recorded), the embedding, the
  binary-prefix device (Section 22.2); bounded-support descent is
  `bst:thm:descent` of [transcendence-over-bounded-support] and the floor
  profile a case of `odg:thm:floor`, both reproved briefly.
- **Merge additions** (marked "merge"): Remark 35.2 (placement beside
  Theorems F, G, H and L: a finitely generated coefficient field is necessary
  for differential algebraicity but, with an order unit, not sufficient);
  Remark 35.12 (the domain has the shape of the domain of `𝒯_p`); Remark
  35.20 (the universal question is answered).
- **Stale text corrected in this report:** the remark after Theorem 21.20,
  the status of Question 19.1, Section 19's ledger, Section 18, Appendix B and
  this README.
- **Verified for this merge.** The source 17 suite was rerun on a copy
  (Python 3.14.4, SymPy 1.14.0) and reproduced its record apart from the
  recorded interpreter version.

## Source 15: the polynomial-composition part

| | Manuscript | Pin | Contributes |
|---|---|---|---|
| **15** | *Polynomial-Composition Rigidity at Surreal Scales: Weighted nonlinear equations, finite degree bounds, and omnific Diophantine universality* (24 pages, US letter, 23 September 2026; batch 31, manuscript 01, archive `Surreal_Polynomial_Composition_Rigidity`) | `bcac55a` | Polynomial composition in `E_Γ(k)` (Proposition 36.2); superlinear escape, integer convexity, exact pullback profile (Lemmas 36.3–36.4, Proposition 36.5); operator bound, exact operator profile, exact leading term (Lemma 36.6, Proposition 36.7, Lemma 36.8); the weighted theorem (Theorem N), mixed differential–Mahler equations, Newton-weight condition (Corollaries 36.9, 36.11); resonant degree bounds and extension-stable loci (Theorem 36.12, Corollary 36.13, Proposition 36.14); matrix rigidity (Theorem 36.15); omnific coefficients and linear solution modules (Proposition 37.1, Theorem 37.2); universal encoding and undecidability (Theorem 37.3, Remark 37.4, Corollaries 37.5–37.6); worked equations and boundaries (Sections 37.3–37.4, Example 37.7); Questions 19.55–19.62. Files `15-polynomial-composition-*`. |

Let `P` have degree `d ≥ 2` and let every other argument `P_ν` have degree
`e_ν < d`. If `c_*(z) ∏ L_ℓ(f(P(z))) = 𝖦(z, L'_ν(f(P_ν(z))))` with nonzero
linear differential operators and every monomial `Y^𝐚` of `𝖦` of composition
weight `Σ a_ν e_ν < s̄d`, then every strongly entire `f` is a polynomial of
degree at most an explicit `B_cmp` that keeps the integer roots of the exact
indicial polynomials `I_(L_ℓ)(dT)` (Theorem N, Theorem 36.12). **No order unit
and no condition on scales enters**: the lower arguments may be dilations
`λz`, so a strictly dominant argument of degree at least two defeats the
partial theta mechanism of Theorems B and J (Remark 36.10, merge). With
ordinary integer data the linear omnific solutions form an explicit
`𝔒`-module computed by a Smith normal form (Theorem 37.2); every affine
hypersurface over `Q` is the entire-solution locus of one equation of the
class, so omnific solvability is undecidable there (MRDP), even with degree
bound ten (Sun's eleven unknowns). The complex entire-Mahler lemma (Bell,
Coons and Rowland, Lemma 6) is credited, not claimed.

- **Placement.** Sections 36–37; principal theorem Theorem N; questions
  19.55–19.62.
- **Renamed symbols** (Section 36.1): source `χ_L` (exact) and `χ̄_L`
  (residue) become `I_L` and `χ_L` — the names are **reversed** to match this
  report's `I_P` and `χ_P`; `h_L, α_L → w_L, β_L`; radius `ρ`, height
  `M_f(ρ)`, `I_f(ρ)`, `in_ρ(f)` → scale `δ`, `−γ_δ(f)`, `Act_δ(f)`, `φ_δ(f)`
  (signs of inequalities reversed); `R → δ_ref`; `𝒯_ρ → 𝓔^(δ)`; `κ → v(lc_z P)`
  (`lc` is the Hahn leading coefficient here, `lc_z` the leading coefficient in
  `z`); `A, Q, q, s, T_ν → c_*, 𝖦, m̄, s̄, L'_ν`; weight `w(𝐚) → cw(𝐚)`;
  `H, b → w_top, β_top`; resonance set `ℛ → Rsn`; `B → B_cmp`; `D, R_(D,Γ), R →
  𝔬, 𝔒_(𝔬,Γ), 𝔑`; `E_z, S_j, L_(d,N) → ϑ, Pr_j, Ann_(d,N)`; encoder `q, T →
  deg p, wd(p)`; theta `F → Θ_p`. "Mahler equation" is kept with its meaning
  (argument `z^b`), which is not the exponent dilation of
  [autonomous-dilation-relations](../autonomous-dilation-relations/). The
  shipped audit file keeps the source's notation.
- **Printed once:** the entire class and tails (Definition 1.2, Lemma 2.3 (a)),
  the entire-support criterion (Proposition 20.2), closure (Proposition 2.7;
  polynomial composition is also in `ent:prop:operations`), Gauss algebra
  (Corollary 14.3), injective evaluation (as Theorem 33.5), large active
  degrees (Lemma 14.5), `zD − N + ε` (Example 15.5), the embedding, the
  partial theta series, the characteristic-`p` series (Example 17.3), the
  rank-infinity series (Theorem 11.2), uncountable cofinality (Section 31.3)
  and the full-class failure (Proposition 27.6).
- **Merge additions** (marked "merge"): Remark 36.10 (degree at least two
  removes the order-unit dichotomy; comparison with Theorems B, J, 10.2 and
  Corollary 11.3); the identification of the two indicial polynomials; the
  Mahler references missing from the source (Faverjon–Roques via
  single-dilation-hahn-support, Mahler 1983 via autonomous-dilation-relations).
- **Stale or incorrect source text.** Its description of this report (linear
  rigidity, dilations, first order, higher order without an order unit) was
  accurate at `bcac55a` and is superseded by Theorems H, I and K. Its statement
  that a keyword search for Mahler material returned no matches was **not
  correct at its pin**: single-dilation-hahn-support already discussed Mahler
  difference algebra and cited Faverjon–Roques, as did computable-surreals.
- **Stale text corrected in this report:** the status of Question 19.6,
  Section 19's ledger, Section 18, the appendices and this README.
- **Verified for this merge.** The source 15 suite was rerun on a copy
  (Python 3.14.4, SymPy 1.14.0) and reproduced its record apart from the
  recorded interpreter version; the worked equations were rechecked
  separately with SymPy.

## Source 20: the recurrence part

| | Manuscript | Pin | Contributes |
|---|---|---|---|
| **20** | *Valuation Rigidity and Coefficient Universality in Surreal Recurrences: A mixed differential–dilation theorem and the limits of coefficientwise predictability* (22 pages, US letter, 23 September 2026; batch 33, manuscript 01, archive `surreal_recurrences_research`) | `efc5446` | One finitely generated algebra of coefficient observables (Theorem 38.2, Remark 38.3); one torsion period for all monomials in the residues (Lemma 38.4); recurrences with split characteristic polynomial (Corollary 38.6); coefficient-algebraic conditions, Noetherian compression with one residual period, support and tail recurrence, no common transient (Definition 38.7, Theorem 38.8, Corollary 38.9, Example 38.10, Remark 38.11); surreal and surcomplex recurrence profiles over `No[i]`, `Oz`, `Oz[i]` (Theorem 39.1); a decreasing omnific recurrence (Example 39.2); the coding theorem and the failure of a coefficientwise Skolem–Mahler–Lech theorem (Theorem 39.3, Corollary 39.4, Remark 39.5); determinantal valuation profiles (Corollary 39.7); its convex-scale and finite-group criteria as special cases of Theorem J (Corollaries 39.8–39.9, Remark 39.11); boundary examples (Section 39.5, Example 39.12); Theorem O; Questions 19.63–19.70. Files `20-recurrences-*`. |

For a finite vector of exponential polynomials `Σ_j R_j(n) λ_j^n` over
`𝕂 = k((t^Γ))` whose bases are units (valuation zero) with residues `ζ_j`,
**every coefficient sequence `n ↦ [t^γ]` lies in the one finitely generated
algebra `k[n, ζ_1^n, …, ζ_m^n]`**; so every set-sized family of polynomial
conditions on finitely many coefficients at a time reduces along the orbit to
a finite subfamily (Hilbert's basis theorem), and its hitting set is a finite
union of full classes modulo `𝖬_tor`, the exponent of the torsion subgroup of
`⟨ζ_1, …, ζ_m⟩`, and a finite set, with one `𝖬_tor` for every family
(Theorem O). Without units this fails completely: for every real sequence
`(𝐛_m)` the purely infinite omnific integer `𝔴 = Σ 𝐛_m ω^(ω−m)` has
`[ω^ω](ω^n 𝔴) = 𝐛_n`, so `y_(n+1) = ω y_n` realizes every subset of `N` as the
nonzero set of one fixed Conway coefficient, while the leading exponent of
every recurrence over `No[i]`, `Oz` or `Oz[i]` stays eventually affine on
finitely many progressions (two suffice for real roots, one for positive
roots). The element `𝔴` is the stream `onot:eq:guardbasic` of
[omnific-notations](../../foundations-and-computation/omnific-notations/),
which source 20 does not cite; only its reading as a recurrence observable is
new.

At its pin `efc5446` this report was the seven-source text (sources 08–14, 137
pages); sources 15–19 were already placed in this directory (`9d28e28` is an
ancestor of the pin) but not merged, and source 18 was merged later the same
day (`2c4debb`). Source 20's statement that the text after `hol:thm:mixed`
leaves the mixed unit-valuation case open was **accurate at its pin and is
stale now**: source 18 answers Question 19.4 for every `Γ` and proves Theorem
J. Source 20's valuation theorem and mixed unit rigidity are an independent
second derivation of source 18's and are printed once; its Theorems 10.3 and
10.4 are special cases of Theorem J (strictly: Example 29.15's common cofinal
scale lies outside its Theorem 10.3), and its Theorem 10.4 needs finite
generation only for the convex-hull form of the criterion.

- **Placement.** Sections 38–39, after Section 37, so that Sections 1–37,
  Questions 19.1–19.62 and Theorems A–N keep their numbers; the conclusion is
  now Section 40. Principal theorem: Theorem O in the introduction; questions
  19.63–19.70.
- **Coefficient field.** Any `k` of characteristic zero (Convention 38.1);
  no divisibility.
- **Renamed symbols** (Section 38.1): `K, 𝓔(K) → 𝕂, E_Γ(k)`; unit roots
  `q_i = c_i(1+ε_i)`, `u_n = Σ P_i(n) q_i^n` → `λ_j = ζ_j(1+τ_j)`,
  `𝒴(n) = Σ R_j(n) λ_j^n` (the unit-dilation notation); envelope `W = A+M(S)`,
  `R_(i,γ)` → `Σ = C+M(S)`, `r_(j,γ)`; `C = ⟨c_i⟩`, `M = exp Tor(C)`, class `r`
  → `⟨ζ⟩`, `𝖬_tor`, `b` (source 18's smaller period is `𝖬`); algebra `𝒜`,
  ring `R_0 = k[T, X_1, …, X_s]` → `𝔄`, `k[U, X_1, …, X_m]`; shift `E → Sh`;
  recurrence terms `u_n → y_n`; `x ∈ K^d`, `X`, `T ⊆ Γ`, `F ∈ k[X_1, …]` →
  `𝐱 ∈ 𝕂^d̄`, `𝒳`, `𝖳`, `F ∈ k[Z_1, …]`; purely infinite ideal `𝒥 → Π`
  (`Oz = Z ⊕ Π`); coding sequence `b`, `A_b`, `S ⊆ N` → `𝐛`, `𝔴_𝐛`, `A`;
  Catalan root `λ`, `C(s)`, `C_k` → `λ_−`, `Cat(X)`, `Cat_k` (`C_n` are
  Chebyshev polynomials here); matrix `A`, `δ_j(n)` → `𝐀`, `mv_j(n)`;
  dilation group `G`, convex hull `H` → `𝔊`, `Δ_𝔊`; operator
  `c_(λ,j,k) z^k D^j σ_λ`, `A_s(n)`, `B_j(n)` → `ϰ_(ℓ,r,i) z^i D_z^r σ_(λ_ℓ)`,
  `c_j(n)`; witness `η` → `γ`, and `η` in examples → `ε`; `Θ_Q → Θ_p`;
  characteristic `p → 𝔭`. The shipped audit file keeps the source's notation.
- **Words with two meanings** (Section 38.1): a *unit* is a valuation-zero
  element, neither an order unit nor a unit of `Oz` (only `±1`);
  *compression* is Noetherian compression of coefficient conditions, **not**
  the bounded polynomial jet compression of Theorem 32.9; *period*: source
  18's `𝖬` suffices for valuations but **not** for hitting sets, which need
  `𝖬_tor` (`(−1)^n`: `𝖬 = 1`, `𝖬_tor = 2`, and `[t^0]x = 1` holds exactly
  for even `n`; Remark 38.5); `deg_ω` is the greatest Conway exponent, not a
  birthday.
- **Printed once:** its definitions (Definition 1.2, order unit, valuation
  unit, the embedding (2.4)); its Lemma 3.1 (Lemma 2.1); Lemma 3.2 and
  Corollary 3.4 (Lemma 21.1); Theorem 3.3 (Skolem–Mahler–Lech, imported);
  Theorem 4.1(a)–(b) (Lemma 28.4) with its Remark 4.2; Example 4.3 (the case
  `d = 2` of Example 29.14); Theorem 5.1 (Theorem 28.5 with the admissible
  period `𝖬_tor`) and Corollary 5.2; Example 5.3 (Example 4.6); Lemma 5.4
  (Lemma 28.9); Theorem 5.5 (Theorem 28.10); Remark 5.6 (Remark 4.3); Lemma
  9.1 (Lemma 29.1, Corollary 29.2); Lemma 9.2 (Lemma 3.1 with Corollary 3.4,
  closed region); Theorem 10.1 and Corollary 10.2 (Theorem 29.4 at relative
  scale 0, Corollary 29.6); the theta witness (Theorem 8.1, (8.2), (8.3));
  the torsion and rank-two examples (Section 29.5, Proposition 9.1, Examples
  8.4 and 29.16).
- **Merge additions** (marked "merge"): Remark 38.5 (the two periods);
  Section 39.4's identification of Theorems 10.3 and 10.4 as special cases of
  Theorem J, with the strictness example; Remark 39.10 (finite generation
  cannot be dropped from the convex-hull form: the monomials `t^(ω^j)` in
  `Γ_∞` have cofinal valuations but no order unit); Remark 39.6 (credit to
  omnific-notations); Example 39.12 keeps the exact formula
  `v((1+t)^n − 1) = 𝔭^(v_𝔭(n))` in `F_𝔭((t))`, of which Section 29.5 records
  the subsequence `n = 𝔭^a`; status notes and the re-scoped Question 19.66.
- **Stale text in the source.** Its "gap explicitly left open" (article
  lines 84, 123; its Corollary 10.2 and Remark 10.5; its audit's "The
  specific gap") was accurate at `efc5446` and is stale against the current
  text (Remark 39.11). Its Question 12.7 (smallest nonlinear classes at unit
  dilation) is partly answered in the current text — `𝒯_p` has an order-three
  relation of degree six without dilation, order two is excluded (Theorem I),
  and order three needs jet degree at least four (Theorem K) — and is printed
  re-scoped as Question 19.66 (does a unit dilation lower the order or
  degree?). Its Questions 12.1, 12.2, 12.5 and 12.11 are Questions 19.24,
  19.21, 19.25 and 19.29 (status notes added); 12.3, 12.4, 12.6, 12.8–12.10
  and 12.12 are 19.63–19.65 and 19.67–19.70.
- **Stale text corrected in this report:** the statuses of Questions 19.4,
  19.21, 19.22, 19.24, 19.25, 19.28 and 19.29, Section 19's ledger and
  proposed-contribution paragraphs, Section 18, Section 13.3's list of
  unformalized parts (which also lacked the polynomial-composition part), the
  abstract and title-page status (now "ten later parts"), the appendices and
  this README.
- **Verified for this merge.** The source 20 suite was rerun on a copy
  (Python 3.14.4) and reproduced its record exactly, after normalizing the
  CRLF line endings of the redirected Windows output. The proofs were re-read
  against the statements they are attached to; the Catalan identity, the
  coding shift and the positive-characteristic formula were rechecked by hand.

## What the report claims

Let `K = C((t^Γ))` for a nonzero set-sized ordered abelian group `Γ`, **not
assumed divisible**. *Entire* means that the evaluation family is strongly Hahn
summable at every point of this one field, not at every point of the full
surcomplex class.

- **Theorem A, differential rigidity.** Every strongly entire D-finite power
  series is a polynomial. More strongly, a fixed nonzero operator `L` has an
  exterior valuation region, computed from finitely many coefficients, on
  which strong evaluation of any formal solution already forces a polynomial
  of degree below a common bound.
- **Theorem B, the sharp dilation criterion.** For `q` of infinite
  multiplicative order, a nonpolynomial strongly entire solution of a nonzero
  linear `q`-difference equation with polynomial coefficients exists **if and
  only if** `v(q) ≠ 0` and `|v(q)|` is an order unit of `Γ`. A nonzero
  valuation is not enough in higher rank. The proof covers units whose
  residues are roots of unity. When the criterion holds, a partial theta
  series is a witness.
- **Theorem C, several variables.** A function strongly summable at every
  point of `K^d` whose mixed partial derivatives span a finite-dimensional
  space over `K(z_1, …, z_d)` is a polynomial.
- Further: mixed differential–dilation rigidity at every nonzero noncofinal
  scale (Theorem 10.2); a recurrence exclusion bound that is **attained**,
  boundary included, by a formal exponential (Proposition 5.3); a coarsened
  exclusion bound valid at every nonzero noncofinal dilation valuation (Theorem 7.4); and the exact strong evaluation domain of
  the partial theta series for an arbitrary Hahn parameter (Theorem 8.1).
- In an explicit surreal workspace with countable cofinality and no order
  unit, `Σ ω^(−ω^n) z^n` is strongly entire (Theorem 11.2) yet satisfies no
  nonzero linear differential equation and no nonzero linear dilation equation for any
  nontorsion parameter of that workspace.

The nonlinear part (source 10, Sections 14–17) works over `k((t^Γ))` for
**any** field `k` of characteristic zero:

- **Theorem D, first-order nonlinear rigidity.** For every nonzero
  `P ∈ k((t^Γ))[z, Y_0, Y_1]`, every strongly entire solution of
  `P(z, f, f') = 0` is a polynomial; for a nonpolynomial formal solution there
  is `δ_0 > 0`, depending on `P` and finitely many coefficients of `f`, with
  `t^(−δ)` outside the strong domain for all `δ ≥ δ_0`. So a nonpolynomial
  strongly entire `f` and `f'` are algebraically independent over `K(z)`.
  No separant, irreducibility or solved-form hypothesis is needed.
- The finite exclusion certificate behind it (Theorem 15.1) applies in any
  order when the residue corner polynomial `χ_P` is nonzero (Theorem 16.1,
  with degree candidates in Proposition 16.2); in order one `χ_P ≠ 0` always.
- Finite candidate degrees for polynomial solutions (Theorem 15.3) and an
  affine algebraic set parametrizing all entire solutions, stable under
  Hahn-field extensions (Corollary 15.6).
- Worked equations: two exact Riccati classifications (Proposition 15.7),
  the attained degree cutoff (Example 15.8), resonant degrees (Example 15.9),
  and the first two Painlevé polynomial equations (Proposition 16.3).
- **The exclusion bound cannot be uniform** (Theorem 15.10): the solutions
  `t^λ/(1 − t^λ z)` of `f' = f²` have exact domain `v(x) > −λ`, unlike the
  operator-only bound of Theorem A.
- **Positive-weight Euler rigidity** (Theorem 16.5): a strongly entire
  `f(x_1, …, x_m)` satisfying `P(x, f, ϑ_q f) = 0` for a nonzero
  `P ∈ 𝕂[x_1,…,x_m,Y,Z]`, with
  `ϑ_q = Σ q_ν x_ν ∂_ν` and all `q_ν` positive integers, is a polynomial; zero
  and mixed weights fail (Section 16.3).
- Two-jet independence of `Σ t^(n²) z^n` over `C((t^Q))` (Corollary 17.1)
  and of `Σ ω^(−ω^n) z^n` (Corollary 17.2); characteristic zero is necessary
  even for `f' = 0` (Example 17.3).

The coefficient-field part (sources 11 and 12, Sections 20–22) also works over
`𝕂 = k((t^Γ))` for any field `k` of characteristic zero, with `E_Γ(k)` its
strongly entire series and `Frac E_Γ(k)` their fraction field in `𝕂((z))`:

- **Theorem E, all-order rigidity without an order unit.** Suppose `Γ` has no
  order unit. (a) (11 and 12) Every nonpolynomial strongly entire `f` is
  differentially transcendental over `𝕂(z)`: every strongly entire solution of a
  nonzero algebraic differential equation of any order, whatever its residue
  corner, is a polynomial. (b) (12) If no two distinct elements of
  `Λ ⊆ 𝕂^×` have a root-of-unity quotient, all `(D_z^j f)(λz)`, `λ ∈ Λ`,
  `j ≥ 0`, are algebraically independent over `𝕂(z)`; in particular for every
  nontorsion `q`, including `v(q) = 0`, all `(D_z^j f)(q^i z)`. (c) (11) The
  differentially algebraic elements of `Frac E_Γ(k)` over `𝕂(z)` are exactly
  `𝕂(z)`.
- **Theorem F** (12). For any `Γ ≠ 0` and any `f ∈ 𝕂[[z]]`, entire or not, if
  the values of its nonzero Taylor coefficients span an infinite-dimensional
  rational space (`cvr(f) = ∞`), the conclusion of E(b) holds.
- **Theorem G** (12). `Γ` has an order unit ⇔ some nonpolynomial strongly
  entire series has coefficients in a field of finite transcendence degree
  over `k` ⇔ for some nonpolynomial strongly entire `f` and nontorsion `q` the
  mixed jets `(D_z^j f)(q^i z)` are algebraically dependent ⇔ (iv, added from
  source 13) some nonpolynomial strongly entire series is differentially
  algebraic. Witnesses: the partial theta series `Θ_p`, `p = t^μ`, for the
  first three, and `𝒯_p` of Theorem H for all of them.
- The engine: **one finitely generated coefficient field** for every finite
  differential relation (11 and 12) and every mixed relation with dilations
  whose quotients are not roots of unity (12, through the Skolem–Mahler–Lech
  theorem) (Theorem 21.2), without any nonsingularity hypothesis.
- **Coarsening descent** (11, Theorem 21.11): if the values of a subfield `L`
  lie in a proper convex subgroup, `E_Γ(k) ∩ L[[z]] = L[z]` and
  `Frac E_Γ(k) ∩ L((z)) = L(z)`.
- **Mixed rigidity in the fraction field** (Corollary 22.9, added consequence):
  with no order unit, every nonrational `u ∈ Frac E_Γ(k)` has independent
  mixed jets for dilations with no root-of-unity quotient. The proof combines
  source 12's coefficient theorem with source 11's descent after multiplying
  the Laurent series by a power of `z`; neither delivered source states it.
- Consequences without an order unit (11): rational ODE systems in the fraction
  field have only rational solutions (Corollary 21.16); `u'' = 6u² + z` has no
  solution in `Frac E_Γ(k)` (Corollary 21.17). A solution-dependent exterior
  certificate (12, Corollary 21.18) and a free differential algebra of dilates
  (12, Corollary 21.14).
- A rank-one example (12, Theorem 21.20): `Σ t^(τ^n) z^n` over `C((t^R))`,
  `τ > 1` transcendental, has independent mixed jets although `R` has an
  order unit.
- `Σ ω^(−ω^n) z^n` satisfies no algebraic differential equation of any order,
  and its jets at dilations as in E(b) are independent (12, Theorem 22.1). For
  multiplicatively independent parameters no nonzero relation, linear or not,
  holds (Corollary 22.8, a merge observation).
- **A continuum family** (11, Theorems 22.2 and 22.6): over
  `C((t^{Γ_∞}))`, the series `𝓕_α = Σ_{n≥1} t^(e_code(α|n)) z^n`, one for
  each infinite binary sequence `α`, are strongly entire with jointly
  independent jets, and the fraction field has differential transcendence
  degree `2^ℵ0` over `K(z)`.

The theta-descent part (source 13, Sections 23–25) also works over
`𝕂 = k((t^Γ))` for any field `k` of characteristic zero. For `μ > 0` put
`p = t^μ`, let `C_n` be the monic Chebyshev polynomials (`C_0 = 2`, `C_1 = z`,
`C_(n+1) = z C_n − C_(n−1)`, so `C_n(u + u⁻¹) = u^n + u^(−n)`), and put
`𝒯_p(z) = 1 + Σ_{n≥1} p^(n²) C_n(z)`.

- **Theorem H, the exact boundary.** `Γ` has an order unit ⇔ some
  nonpolynomial strongly entire series is differentially algebraic over `𝕂(z)`
  ⇔ some nonpolynomial strongly entire `f` satisfies an algebraic differential
  equation of order three while `f, f', f''` are algebraically independent
  and `f'''` has degree two over `𝕂(z)(f, f', f'')`. For an order unit `μ`,
  `𝒯_p` is such an `f`, and it is not D-finite. That the second condition
  implies the first is Theorem E(a), which source 13 proves again.
- **Exact domain** (Theorem 23.5): for every `μ > 0`, the strong domain of
  `𝒯_p` is `{0} ∪ {x : v(x) ≥ −Nμ for some N}`, the valuation ring of the
  coarsening by the convex subgroup generated by `μ`; so `𝒯_p` is entire
  exactly when `μ` is an order unit. The Taylor coefficients are explicit, with
  `v(a_m) = m²μ` (Proposition 23.3).
- **Product and zeros** (Theorem 23.6): `𝒯_p(x) = Π(1 − p^(2m)) Π(1 +
  p^(2m−1) x + p^(4m−2))` on the domain; the zeros are exactly
  `x_m = −(p^(2m−1) + p^(−(2m−1)))`, all simple, with exact derivative
  valuations and an exact linearization on the nearest-root ball
  (Proposition 23.7).
- **The equation** (Theorem 24.1): for `f = 𝒯_p`,
  `(z² − 4)𝒦² − 4ℬ³ + g₂ℬf⁴ + g₃f⁶ = 0`, with
  `ℋ = (z² − 4)(ff'' − f'²) + zff'`, `𝒦 = fℋ' − 2f'ℋ`, `ℬ = 𝔠f² − ℋ` and
  Lambert constants `𝔠, g₂, g₃` in the nome `p²`; equivalently
  `(z² − 4)(𝒜')² = 4(𝔠 − 𝒜)³ − g₂(𝔠 − 𝒜) − g₃` with `𝒜 = ℋ/f²`. It holds for
  every `μ > 0`.
- **Minimal order three** (Theorem 24.8, Corollary 24.9): through
  `z = u + u⁻¹` the series becomes the bilateral theta series `Ψ_p`, and three
  difference-field arguments for `u ↦ p²u` show that `Ψ_p, ϑ_uΨ_p, ϑ_u²Ψ_p`,
  hence `𝒯_p, 𝒯_p', 𝒯_p''`, are algebraically independent. The differential
  field is presented by a rational system of degree two over a rational
  function field (Theorem 24.10); `𝒯_p` satisfies no linear differential
  equation (Proposition 24.11).
- **Surreal and omnific** (Section 25.3): with `Γ = R`, `p = ω⁻¹`, `𝒯_p` is
  entire on `C((ω^(−R))) ⊆ No[i]` but not on `No[i]` (it fails at `ω^ω`); its
  zeros `−ω^(2m−1) − ω^(−(2m−1))` are not omnific integers, with explicit
  omnific floors and ceilings and exact rounding-error valuations
  (Corollary 25.3).
- Examples and the affine corollary (Section 25.4); the merge additions listed
  under "Source 13" above.

The order-three-threshold part (source 14, Sections 26–27) also works over
`𝕂 = k((t^Γ))` for any field `k` of characteristic zero and any `Γ`.

- **Theorem I, second-order rigidity and the order-three threshold.** (a) A
  strongly entire solution of a nonzero algebraic differential equation of
  order at most two over `𝕂(z)` is a polynomial; so for every nonpolynomial
  strongly entire `f`, the series `f, f', f''` are algebraically independent
  over `𝕂(z)`. No divisibility, rank, algebraic-closedness, order-unit or
  corner hypothesis is needed. (b) With an order unit the least order of an
  algebraic differential equation satisfied by a nonpolynomial strongly
  entire series is exactly three (the witness `𝒯_p` of Theorem H); without
  one, no finite order occurs (Theorem E(a)).
- **The mechanism** (Sections 26.2–26.3): at the infinitely many scales where
  the initial polynomial `φ_δ` of a nonpolynomial entire series is not a
  monomial (*breaks*, Lemma 26.4), a fixed equation reduces to one
  homogeneous polynomial `𝔥_P` over `k` (Lemma 26.5); logarithmic Euler
  derivatives confine both endpoints of every nonmonomial `φ` with
  `𝔥_P(φ, ϑφ, ϑ²φ) = 0` to a finite set (Lemma 26.8), even when the
  leading-monomial test (`χ_P`, Remark 26.6) vanishes identically.
- Consequences (Corollaries 26.9–26.11): `trdeg 𝕂(z)(f, f', f'') = 3`;
  strongly entire observables of rational two-state systems are polynomials;
  a quotient `g/𝗉` of an entire series by a polynomial satisfying an equation
  of order at most two is rational. Three independent jets for
  `Σ t^(n²) z^n` and `Θ_p` (Corollary 26.13, merge).
- **Order three** (Section 27): a nonmonomial initial polynomial of an
  order-three equation satisfies `Υ_𝔥(N, 𝗀⁺) = Υ_𝔥(m, −𝗀⁻) = 0` for its
  endpoint–gap pairs (Theorem 27.2), which gives a sufficient rigidity
  certificate (Corollary 27.3). For the theta equation the exterior form is
  `W² − V² + 4V³`, its polynomial solutions are exactly `bX^m` and
  `bX^m(1 + aX)` (Theorem 27.4), and every nonpolynomial strongly entire
  solution has eventually nonzero coefficients with strictly increasing,
  cofinal differences `v(a_(n+1)) − v(a_n)` (Theorem 27.5).
- No nonpolynomial power series with coefficients in `No[i]` is strongly
  summable at every point of `No[i]` (Proposition 27.6).

The unit-dilation part (source 18, Sections 28–29) works over `𝕂 = k((t^Γ))`
for any field `k` of characteristic zero and any `Γ`.

- **Theorem J, the relative-scale criterion.** Let `λ_1, …, λ_m ∈ 𝕂^×` have
  no root-of-unity quotient. (a) If no `|v(λ_i/λ_j)|` is an order unit, every
  formal solution of `Lf = 𝗁` (`L = Σ p_{ℓ,r}(z) D_z^r σ_{λ_ℓ}` nonzero, `𝗁` a
  polynomial of bounded degree) that is strongly evaluable at one point of
  sufficiently negative valuation has degree below a bound depending only on
  `L` and the degree bound; so every strongly entire solution is a polynomial.
  (b) Some nonpolynomial strongly entire `f` satisfies some nonzero `Lf = 0`
  iff some `|v(λ_i/λ_j)|` is an order unit; two multipliers and first
  derivatives suffice (`f(z) = Θ_p(z/λ_i)`, `p = λ_j/λ_i`). In particular
  Question 19.4 has a positive answer for every `Γ` (Corollary 29.6).
- **Valuations of Hahn exponential polynomials** (Theorems 28.5, 28.10):
  `v(Σ_j R_j(n) λ_j^n)` is eventually affine on each of finitely many
  arithmetic progressions, or the sequence vanishes there identically, with
  arbitrary well-ordered Hahn coefficients; at unit valuation it is eventually
  periodic; for `v(P(n, q^n))` the period divides the order of `res(q)`
  (Corollary 28.7). The Skolem–Mahler–Lech theorem is imported.
- Adding derivatives to the powers of `σ_q` creates no new existence case
  (Corollary 29.11); the multipliers matter only through their images in
  `Γ/Δ^top` (Proposition 29.12); a common absolute scale is irrelevant; the
  entire solution space is finite-dimensional (Proposition 29.18); boundary
  examples for root-of-unity quotients, positive characteristic and operator
  shape (Section 29.5).

The Newton-rigidity part (source 19, Sections 30–31) works over `𝕂 = k((t^Γ))`
for any field `k` of characteristic zero and any `Γ`.

- **Theorem K.** A strongly entire solution of a nonzero algebraic
  differential equation of order at most three and total degree at most three
  in `f, f', f'', f'''` is a polynomial; more generally so is every strongly
  entire solution of an equation of order at most three whose exterior form,
  or each irreducible factor of it, is nonzero on the monomial jet curve or
  has a nonzero first polar along it (Proposition 30.6, Corollary 30.9).
- Three-jet independence and the four-jet degree bound survive arbitrary
  extensions of constants, including finitely many surcomplex and
  Gaussian-omnific coefficients (Corollaries 30.12–30.15); entire solution
  pairs of algebraic two-state systems are polynomial (Theorem 30.16).
- The formal solutions of the order-three quartic `𝖧_3` and the order-four
  quadratic `𝖰_4` are exactly `0`, monomials and `a z^n + b z^(2n)`
  (Theorems 31.1, 31.2); `Σ t^(4^j) z^(2^j)` satisfies both exterior equations
  at every scale but neither equation (Example 31.3).

The theta-hierarchy part (source 16, Sections 32–33) works over `k((t^R))`,
`k = R` or `C`.

- **Theorem L.** (a) `𝒯_(t^(μ_1)), …, 𝒯_(t^(μ_N))` are algebraically
  independent over `𝕂(z)` when the `1/μ_i` are `Q`-independent; a family of
  size `2^ℵ0` exists. (b) For every `N` a polynomially weighted sum with
  weights of degree below `N`, coefficients in `{0,…,N}` and scales
  `1/√p_i` is strongly entire, differentially algebraic and of minimal order
  in `[N, 3N]`. (c) The field `𝒟_DA` generated by all differentially algebraic
  strongly entire series has `trdeg 2^ℵ0` and `dtrdeg 0`.
- Bounded polynomial jet compression (Theorem 32.9) in any differential field
  of characteristic zero; the exact Gauss profile and a finite noncancellation
  threshold (Theorem 32.3, Proposition 32.5); exact order `d_N` at the
  compositum dimension (Theorem 32.19); a fixed polynomial relation fails at
  all but finitely many integers (Theorem 33.5, Corollaries 33.6–33.7); a
  valuation proof of the minimal order three of `𝒯_p` (Corollary 33.9).

The single-scale part (source 17, Sections 34–35) works in characteristic zero,
at one order-unit scale.

- **Theorem M.** Exact differential relation ideals of rapid-height lacunary
  families; every infinite subseries is strongly entire and differentially
  transcendental over `𝕂(z)` at an order-unit scale;
  `dtrdeg FE = 2^ℵ0` over `R((t^Q))` and `C((t^Q))` with a family whose
  coefficients lie in `Q(t)`.
- All scalars of a Hahn field may enter the equation (Theorem 34.18); finite
  Hermite data (Theorem 35.4); `∂_BM`-jets of `Σ_(n∈A) ω^(−𝖻_n)` independent
  over `R(ω)` and over the bounded-support field (Theorem 35.6, Corollary
  35.8); common strong domain `{x : v(x) ≥ −m}` in `No[i]`, a valuation ring
  (Theorem 35.10, Proposition 35.11); independent omnific codes
  `ω^Ω Σ ω^(−𝖻_n)` and floors `⌊𝒢_A(ω^(−1), ω^a)⌋_Oz` (Theorems 35.16, 35.18).

The polynomial-composition part (source 15, Sections 36–37) works over
`k((t^Γ))` in characteristic zero, for every `Γ`.

- **Theorem N.** An equation with one product of `s̄` nonzero linear
  differential transforms of `f(P(z))`, `deg P = d ≥ 2`, balanced by a
  polynomial in transforms of `f(P_ν(z))`, `deg P_ν < d`, whose monomials
  have composition weight below `s̄d`, has only polynomial strongly entire
  solutions; in particular every linear equation with a unique argument of
  largest degree `≥ 2` (Corollary 36.9).
- Explicit degree bounds keeping exact indicial resonances, with
  extension-stable finite coefficient loci (Theorem 36.12, Corollary 36.13,
  Proposition 36.14); nonsingular matrix systems (Theorem 36.15); linear
  omnific solution modules over `Oz`, `Oz[i]` and `𝔒_(𝔬,Γ)` (Theorem 37.2);
  every affine hypersurface over `Q` is an entire-solution locus (Theorem
  37.3), so omnific solvability is undecidable in the class, even with degree
  bound ten (Corollaries 37.5–37.6).

The recurrence part (source 20, Sections 38–39) works over `k((t^Γ))` in
characteristic zero, for ordinary recurrences indexed by `n ∈ N`.

- **Theorem O.** (a) For a finite vector of exponential polynomials with unit
  bases (residues `ζ_1, …, ζ_m`), every coefficient sequence lies in the one
  finitely generated algebra `k[n, ζ_1^n, …, ζ_m^n]` (Theorem 38.2). (b) Every
  set-sized family of polynomial conditions on finitely many coefficients at a
  time is equivalent along the orbit to a finite subfamily, and its hitting set
  is a finite union of full classes modulo `𝖬_tor` and a finite set, one
  `𝖬_tor` for all families (Theorem 38.8); supports inside a prescribed set are
  a special case (Corollary 38.9); no common transient bound exists (Example
  38.10). (c) Every real sequence is `n ↦ [ω^ω](ω^n 𝔴)` for a purely infinite
  omnific `𝔴` (Theorem 39.3), so no coefficientwise Skolem–Mahler–Lech theorem
  holds for omnific recurrences (Corollary 39.4); this is no conflict with the
  universal quotient of `Oz`, since `[ω^ω]` is not multiplicative (Remark
  39.5).
- Recurrences over `No[i]`, `Oz`, `Oz[i]` have eventually affine leading
  Conway exponents on finitely many progressions (Theorem 39.1); the omnific
  recurrence `y_(n+2) = ω y_(n+1) − y_n`, `y_n = ω^ω λ_−^n`, has degree
  `ω − n`, decreasing forever without reaching zero (Example 39.2); the least
  valuations of `j × j` minors of `𝐀^n` are eventually affine (Corollary
  39.7); the convex-scale and finite-group criteria are special cases of
  Theorem J (Corollaries 39.8–39.9).

## What the report does not claim

- The arbitrary-rank classification is offered as a **proposed original
  contribution**. Priority is not certified, no named published conjecture is
  claimed solved, and the proofs have not been independently refereed.
  The [Lean ledger](../../FORMALIZATION.md) records support and escape
  lemmas, exponential and partial-theta domains, polynomial-orbit
  valuations, constant-point avoidance, inward stability and torsion
  covariance. In particular, the partial-theta construction proves one
  direction of the dilation classification and of the order-unit detection
  equivalence. The full classifications and the nonlinear, coefficient-field,
  theta-descent, order-three-threshold, unit-dilation, Newton-rigidity,
  theta-hierarchy, single-scale, polynomial-composition and recurrence theorem
  packages remain pending. The detailed coverage is in Section 13.3.
- Classical material is credited, not claimed: Stanley's D-finite/P-recursive
  correspondence, Hahn–Neumann support lemmas and Higman's lemma, partial
  theta series and their functional identity, and the Conway normal-form
  identification. Ramis, Garoufalidis and Di Vizio are named antecedents;
  their conclusions are neither inferred nor strengthened here.
- `D_z` differentiates only the formal variable and kills every scalar. It is
  **not** the Berarducci–Mantova derivation, and no theorem about that
  derivation is restated as D-finite rigidity.
- Finite-order dilations are excluded from the main dilation theorem
  (Section 9). **No universal all-order rigidity theorem is claimed for
  value groups with an order unit**, and none can hold: Theorem H gives a
  nonpolynomial strongly entire series with an algebraic differential
  equation of order three for every such group. Theorem F still gives
  all-order independence for individual series with infinite
  coefficient-value rank, including the rank-one example of Theorem 21.20,
  and Theorem M (source 17) for explicit lacunary series of coefficient-value
  rank one.
  Source 10 answers the first-order case of the nonlinear question, plus the
  higher-order equations with `χ_P ≠ 0` and positive-weight Euler relations,
  for every `Γ`; sources 11 and 12 answer all orders, including a vanishing
  residue corner, when `Γ` has no order unit; source 13 answers the case with
  an order unit by the example of order three; source 14 excludes order two
  for every `Γ`, so the least order is exactly three. A classification of the
  differentially algebraic strongly entire series, and of those of minimal
  order three, stays open (Question 19.1, re-scoped four times: from what was
  Question 15.1, to groups with an order unit, to order two, and now to that
  classification). The equation
  `z²ff'' + zff' − z²f'² = 0` has polynomial solutions of every degree but is
  not a nonpolynomial counterexample (Proposition 16.4); partial theta is not
  a counterexample either (it satisfies a dilation equation), and whether
  `Θ_p` or `Σ t^(n²) z^n` is differentially algebraic (necessarily of order
  at least three) is not decided. The
  escape proof does not extend to nonlinear equations in any order. Linear
  mixed equations at unit valuation are now settled for every `Γ` (Question
  19.4, formerly 15.2, answered by source 18); several dilations are settled
  only for the existence of some linear equation with multipliers without a
  root-of-unity quotient, and stay open for prescribed operators, systems and
  root-of-unity quotients (Question 19.6, re-scoped). Order three is settled
  only in total jet degree at most three (Theorem K).
- The linear exclusion thresholds are explicit and uniform but need not be
  optimal; the nonlinear exclusion bound is explicit, solution-dependent, not
  optimal, and has no converse.
- The coefficient-field generality of the nonlinear and coefficient-field
  parts is not transferred to Theorems A–C.
- The nonlinear part keeps every limitation of source 10, listed as N1–N17 in
  Section 19.3: among them, the corner is not a differential Newton polygon;
  candidate degrees are necessary, not realized, and not a uniform algorithm
  for arbitrary coefficient names; the solution locus does not say the number
  of solutions is finite; `Σ t^(n²) z^n` and `Σ ω^(−ω^n) z^n` are prior
  material, only their two-jet consequences are new; independence concerns
  formal functions, not values; nothing is entire on all of `No[i]`; priority
  is provisional (targeted literature search of 22 September 2026, Hayman and
  Hu–Yang through metadata only, targeted repository comparison at `048b72c`).
- The coefficient-field part keeps every limitation of sources 11 and 12,
  listed with source tags as C1–C26 in Section 22.7: among them, the
  order-unit case is not settled and no counterexample is given (source 13
  has since settled it; the non-claim is kept as the sources' statement); not claimed
  new are classical coefficient recurrences (Hurwitz, Laohakosol–Kongsakorn–
  Ubolsri), finite generation, the valuation-rank inequality, the
  Skolem–Mahler–Lech theorem (imported through Bell's Theorem 1.1, Lech's
  proof not reconstructed, no effective bound), the all-scale criterion, the
  polynomial half of the descent (the entire-functions report's obstruction),
  continuum cardinality and almost-disjoint combinatorics, and `F`; entire
  means one set-sized field; independence is of formal functions; descent's
  proper-convex hypothesis is sufficient, not necessary; `𝕂(z)` is not claimed
  differentially closed; the continuum family is cardinally maximal only; the
  Painlevé statement concerns the fraction field, not local or classical
  solutions; Theorem F is sufficient only; constant extension (Proposition
  22.7) does not cover new dilation parameters; the rank-one family does not
  settle `C((t^Q))`; root-of-unity quotients are excluded; statements requiring
  a nonpolynomial strongly entire series are vacuous in uncountable cofinality,
  while Theorem F still concerns arbitrary formal series; Hu–Luan's rank-one hypotheses are not
  transferred; priority is provisional (targeted searches of 22 September
  2026, targeted repository comparison at `465a54b`). The separately
  identified Corollaries 22.8 and 22.9 are consequences assembled here from
  those sources, without a historical priority claim.
- The theta-descent part keeps every limitation of source 13, listed as
  T1–T19 in Section 25.6: among them, no Lean formalization, referee report or
  certified priority; the triple product, Chebyshev, theta–elliptic
  identities are classical, with no novelty claim for third-order theta
  relations; the no-order-unit direction (Theorem E(a)) and the bilateral
  theta domain and Hahn–Tate uniformization are prior repository material;
  `𝒯_p` is not entire on `No[i]` (it fails at `ω^ω`) and entireness is
  relative to one field; `D_z` is not the Berarducci–Mantova derivation; the
  finite checks prove no summability, transcendence, minimal order,
  classification, zero-set completeness or novelty; no classification is
  given and minimal order two is open (kept as source 13's statement; source
  14 has since excluded order two); "no omnific zero" concerns the strong
  domain only and is not a Diophantine statement; local valuation formulas
  are not uniform across roots; no numerical theta-value transcendence is
  used, and independence concerns formal functions; the minimal-order
  arguments assume an order unit and `p` is the monomial `t^μ`; Sebbar and
  Ohyama were not read in full, and broad searches are not evidence of
  absence; the repository comparison at `4cdeaec` was targeted; the answered
  question is this report's, not a named conjecture; the classification
  quantifies over the scale; without an order unit only differentially
  algebraic entire series are excluded; the poles at `z = ±2` of the rational
  system are chart artefacts; and the merge's additions (T19) carry no
  priority claim.
- The order-three-threshold part keeps every limitation of source 14, listed
  as O1–O18 in Section 27.6: among them, no Lean formalization, referee report
  or certified priority, and the Lean build does not cover it; only this
  report's question is answered, not a named conjecture; the repository
  comparison at `b895e86` was targeted and the formalization ledger was not
  read; entireness is relative to one Hahn field and nothing nonpolynomial is
  entire on `No[i]`; `D_z` is not the Berarducci–Mantova derivation; the theta
  product and elliptic identity are classical, and the theta descent, its
  equation, zeros and omnific rounding and the no-order-unit obstruction are
  prior and not claimed; eventual Newton convexity is necessary only (no
  sufficiency, no classification, `v(a_n) = n²μ` not forced); the gap test is
  a sufficient certificate, not a decision algorithm; the meromorphic
  corollary needs a polynomial denominator; the systems corollary is for
  rational right-hand sides; nothing is said about local formal solutions or
  classical Painlevé functions; positive characteristic is excluded (with a
  counterexample) and mixed-characteristic `p`-adic fields are not covered;
  there is no uniform degree bound for polynomial solutions; the proof does
  not reduce the group to rank one; the 600 finite checks (theta identities
  modulo `q^48`) certify no infinite statement; Sebbar was read through its
  abstract only and broad searches are not evidence of absence; the research
  questions are not solved; and the merge's additions (O18) carry no priority
  claim.
- The unit-dilation part keeps every limitation of source 18, listed as
  U1–U15 in Section 29.8: among them, no referee report or Lean
  formalization; the Skolem–Mahler–Lech theorem is imported, with no
  effective exceptional-zero bound; novelty of the valuation theorem is not
  certified and no rank-one case is claimed new; no nonlinear rigidity is
  claimed (its own nonlinear question is answered negatively in this text by
  `𝒯_p`); no torsion-block theorem, the no-root-of-unity hypothesis being
  essential; Theorem 29.9 concerns some equation, not prescribed operators or
  systems; no algorithm or effective zero set; exterior regions and degree
  bounds are not exact domains and depend on the exact operator; entireness is
  relative to one Hahn field, nothing is entire on `No[i]`, and `D_z` is not
  the Berarducci–Mantova derivation; omnific integers are coefficients only;
  linear independence is of formal functions; positive characteristic fails;
  the 16,579 checks prove nothing infinite and their count measures no
  coverage; the repository comparison at `bcac55a` was partial.
- The Newton-rigidity part keeps every limitation of source 19, listed as
  R1–R16 in Section 31.5: no all-order order-unit rigidity (none holds); no
  meromorphic order-unit analogue; no all-order independence from three-jet
  independence; no point-value independence; no omnific factorization (the
  omnific consequence concerns finitely many coefficients); no uniform degree
  bound; entireness relative to one Hahn field; not the Berarducci–Mantova
  derivation; external constants change the relation, not the domain; the
  first-polar and factor criteria are sufficient, not necessary; `𝖧_3`, `𝖰_4`
  and the sparse series are not counterexamples; the 259 checks certify
  nothing infinite; no Lean proof, referee report or priority, and the
  repository was not built; targeted comparisons at `3d40856`; positive and
  mixed characteristic excluded.
- The theta-hierarchy part keeps every limitation of source 16, listed as
  Th1–Th16 in Section 33.5: not every candidate works and no recognition
  algorithm; `3N` not shown sharp, `d_N` not computed, the spectrum not
  determined; order two not decided by `N = 2` (it is decided by Theorem I);
  joint independence of all `3N` jets not proved; finite checks decide no
  dependence; nothing entire on `No[i]`; no point-value independence; seed,
  equation and order three credited to source 13, theta product and Tate
  identity imported; priority provisional (a primitive-element antecedent may
  exist); no referee report or Lean; snapshot taken while the repository was
  changing; choice (Hamel basis), not CH; real-valued asymptotics, so
  `Γ = R` only; no named conjecture; external `D_z` only.
- The single-scale part keeps every limitation of source 17, listed as F1–F19
  in Section 35.7: single-series gap transcendence is classical (Grönwall via
  Ostrowski, original not inspected); normal forms, `∂_BM`, `Oz`,
  lacunarity, polarization, almost-disjoint families, cofinite spans and
  bounded-support descent not new, nor the existence of differentially
  transcendental surreals; the universal order-unit question not solved by
  source 17; the codes are algebraic, with no primality, irreducibility or
  divisibility; the mixed theorem has base `k(p, z)` only; the pure-`z`
  theorem freezes the scalars and the witnesses are not transcendental over
  `k((p))` or `No`; finite alphabets only; the continuum family is not a basis
  and not uniformly computable; finite Hermite data; strong summation, not
  the fine topology, and `∂_BM` is not `D_z`; descent needs a cofinal
  scale; rapid ratios sufficient, not necessary; the finite witness is not a
  decision procedure; no large cardinals, CH or GCH; no referee report or
  Lean, and 8,608 checks are not a theorem count; PDF bytes not reproducible;
  comparison covered three reports; floors only for real `a ≥ 0`.
- The polynomial-composition part keeps every limitation of source 15, listed
  as P1–P18 in Section 37.6: no referee report, Lean or repository build, and
  "breakthrough" disclaimed; Bell–Coons–Rowland, Nishioka, MRDP and Sun are
  credited inputs, and ten is not optimal; entireness relative to one Hahn
  field; `D_z` is not `∂_BM`; the general higher-order problem is not
  addressed by it; omnific polynomiality is elementary; the strict weight
  condition is sufficient, not necessary, and critical weights and several
  top products are open; the Newton-weight condition is not an independence
  statement; the coefficient locus is not a decision procedure; the matrix
  theorem needs a nonsingular dominant matrix; no several variables or
  meromorphic solutions; extension stability for fixed equations only; `Oz`
  not claimed a PID; the critical classification is elementary; 2,369 checks
  certify nothing infinite; the comparison read seven files and its "no
  Mahler material" statement was incorrect at the pin; the quotient and
  lattice results are not reproduced.
- The recurrence part keeps every limitation of source 20, listed as V1–V17
  in Section 39.7: no referee report, Lean formalization or certified
  priority (an unrefereed AI-assisted draft, "not an independently certified
  breakthrough"); Skolem–Mahler–Lech, the support lemma and Hilbert's basis
  theorem imported, no effective exceptional-zero bound or algorithm, and the
  classical Skolem problem not solved; Noetherian compression is existential
  only; unbounded coefficient-polynomial degrees and no common transient; no
  nonlinear mixed rigidity; no classification of full omnific membership (the
  integer constant term is not handled); the coding theorem stores a sequence
  in an infinite initial value, is not effective, and proves no definability
  of coefficient extraction in the pure ring of `Oz`; entireness relative to
  one set-sized field, statements over `No[i]` localized to a set-sized Hahn
  field; `D_z` is not `∂_BM`; torsion dilations and positive characteristic
  excluded; nothing on Lyapunov limits or periodicity of matrix coefficients;
  `deg_ω` is neither a birthday nor a sign; Fuchs–Heintze's constants not
  improved and the Krapp–Kuhlmann–Serra setup distinct; Neumann and the
  quotient report not audited; 4,605 checks certify nothing infinite (1,189 of
  them hold by construction); targeted repository comparison, stale in its
  "gap" statement.
- The finite checks validate coefficient conversions, identities, cancellation
  examples and finite ordered-group examples. They do not establish the
  infinite support arguments, the cofinality claims, the generic-line theorem,
  the nonexistence of annihilating operators, the coefficient-field theorem,
  the descent, any independence statement, the minimal order of `𝒯_p`,
  second-order rigidity, the periodic-affine valuation theorem or the
  Skolem–Mahler–Lech theorem, Theorem K, Theorem L, Theorem M, Theorem N or
  Theorem O.

## Relation to the neighbouring reports

**[entire-functions-at-arbitrary-rank](../entire-functions-at-arbitrary-rank/)**
studies the same class of entire functions over the same kind of workspace.
None of its ring-theoretic conclusions is used here. This report cites its
order-unit coarsening lemma `ent:lem:coarsening` rather than repeating it, and
takes from it the background facts about countable cofinality and the group
`⊕_{j≥0} Q ω^j`. **The two order-unit dichotomies are not the same theorem.**
There, the order unit decides Hermite interpolation and the Bézout property of
the ring. Here, it decides which annihilating operators a nonpolynomial member
can satisfy (Theorem B), whether a nonpolynomial member can be differentially
algebraic (Theorem H; without it, differential transcendence in all orders by
Theorem E; with it, least order three by Theorem I), mixed-jet
independence (Theorem G), and, through the top Archimedean scale, which finite
sets of multipliers carry a mixed linear equation with a nonpolynomial
solution (Theorem J). Neither implies the
other. Source 17's continuum family over `C((t^Q))` (Corollary 35.3) is the
order-unit counterpart of this report's Theorem 22.6. The polynomial half of the coarsening descent (Theorem 21.11) is a
coefficient-field form of that report's intersection `E_Δ ∩ K_Γ[[Z]] = K_Γ[Z]`
for noncofinal extensions.

**[differential-equations](../differential-equations/)** uses a derivation on
surreal *scalars*; this report does not. Its `diff:cor:riccati` solves
`∂u = 1 + u²` in `No[i]` with the same answer `±i` as Proposition 15.7 here,
but for a different derivation acting on different objects; neither implies
the other. **[rank-one-berkovich](../rank-one-berkovich/)**
already contains the quadratic-exponent example `Σ t^(n²) z^n`, so the partial
theta witness is not counted as a new function; the same series is
`found:ex:internal` in [foundations](../../foundations-and-computation/foundations/),
and only its two-jet independence (Corollary 17.1) is new here.

**[tail-spans-and-differential-transcendence](../../surreal/tail-spans-and-differential-transcendence/)**
proves all-order differential independence for particular Galois-supported
constructions, with scalar or fixed-disk analytic derivations over smaller
base fields, and already has continuum-sized independent families built with
binary-prefix almost-disjoint sets. The nonlinear part here proves two-jet
independence for every nonpolynomial strongly entire function over its full
Hahn field, and the coefficient-field part all-order independence for every
such function when the value group has no order unit, together with a
continuum family of strongly entire series independent over the whole Hahn
field (Theorem 22.6). Neither result weakens or rediscovers the other, and
neither is transferred to the other's derivation. That report already has an
exact cofinite-span relation theory and `∂_BM`-jets of numerical witnesses
(`tail:thm:surreal`, `tail:eq:BMtriangular`, `tail:rem:indexfamily`); the
single-scale part here (source 17) has a parallel exact relation theory whose
mechanism is support, not coefficients, over a different numerical base, and
its witnesses `𝔵_A` are different numbers from that report's `ξ_A`.

**[transcendence-over-bounded-support](../../surreal/transcendence-over-bounded-support/)**
proves algebraic independence of factorial-support witnesses `η_A` over the
bounded-support field and the descent theorem `bst:thm:descent`, and states
that it proves no differential independence. Source 17 continues it
differentially: its Lemma 35.7 is the integer-lattice case of that descent,
credited and reproved, and Corollary 35.8 gives `∂_BM`-jet independence over
the same kind of base.

**[hahn-tate-uniformization](../hahn-tate-uniformization/)** studies the
bilateral theta series `Σ (−1)^n q^(n(n−1)/2) u^n`, its strong domain and its
product at arbitrary rank. The bilateral series `Ψ_p` of the theta-descent
part is that series at the nome `p²` and the argument `−pu`; its domain and
product are specialized here, not claimed anew, and the new material is the
descent to the entire power series `𝒯_p` and its differential algebra.
**[omnific-diophantine-geometry](../../surreal/omnific-diophantine-geometry/)**
supplies the definition `Oz = Z ⊕ Π` (`odg:def:rings`) used for the omnific
rounding of the zeros of `𝒯_{ω⁻¹}` (Corollary 25.3); that corollary concerns
an infinite-series equation, not a Diophantine one. Source 17's floor profile
(Theorem 35.18) is a case of its `odg:thm:floor`.

**[single-dilation-hahn-support](../single-dilation-hahn-support/)** also speaks
of dilations, but there a dilation is an automorphism `t^g ↦ t^(qg)` of the
scalar field; here it is always the argument dilation `f(z) ↦ f(λz)` with a
fixed scalar `λ`. The two reports share the word, not a theorem. That report
already discussed Mahler difference algebra and cites Faverjon–Roques on
linear Mahler equations with Hahn-series solutions, which source 15 missed;
this report cites both (Section 37.5) and uses neither.

**[autonomous-dilation-relations](../autonomous-dilation-relations/)** treats
autonomous Mahler equations for the exponent dilation `S_d`; its
`adr:lem:monomial` (`S_d w = w^d` forces a monomial) is the twin of Example
37.7 here (`f(z^d) = f(z)^d` forces `cz^N`), and its README records Mahler's
1983 criterion through Nishioka–Nishioka. Polynomial composition in the entire
class is part of `ent:prop:operations` of entire-functions-at-arbitrary-rank.
Source 15's omnific module theorem applies `odg:thm:smith` and
`odg:thm:linear` of omnific-diophantine-geometry (with the same argument over
`Z[i]`), and its undecidability corollary refines `odg:cor:H10` by an encoding
into a rigid functional equation.

**[omnific-notations](../../foundations-and-computation/omnific-notations/)**
already contains, as `onot:eq:guardbasic`, the stream
`Σ a_n ω^(ω−n) = ω^ω Σ a_n (ω^(−1))^n` for an arbitrary real sequence, with
the remark that an algorithm for each `a_n` need not decide whether all
vanish. It is the element of Theorem 39.3; source 20 did not cite it, and only
its reading as the orbit of a first-order recurrence observed at one exponent
is new here (Remark 39.6). **[set-sized-quotients-of-omnific-integers](../../surreal/set-sized-quotients-of-omnific-integers/)**
proves that every additive and multiplicative map from `Oz` to a set-sized
ring factors through the constant term (`osq:thm:universal`); Remark 39.5
uses it only to explain why the additive coefficient map `[ω^ω]` gives no
contradiction. A batch-34 sentence there adds that the set-sized target is
needed: that report's `osq:cr:thm:residually` gives unital ring
homomorphisms `sp_a : Oz → No[i]` with `sp_a(ω^a) = −1`. Source 17's omnific codes (Theorem 35.16) encode subsets of `N`
through algebraic independence, not through a coefficient observation.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
python code/08-finite-recurrences-verify.py --output rerun-08.txt
python code/09-entire-hahn-holonomic-verification.py --output rerun-09.txt
python code/10-nonlinear-rigidity-verify.py --output rerun-10.json
pip install -r data/11-coarsening-differential-rigidity-requirements.txt
python code/11-coarsening-differential-rigidity-verify.py --output rerun-11.json
python code/12-coefficient-field-rigidity-verify.py --output rerun-12.json
pip install -r data/13-theta-descent-requirements.txt
python code/13-theta-descent-verify.py --precision 128 --output rerun-13.json
pip install -r data/14-order-three-threshold-requirements.txt
python code/14-order-three-threshold-verify.py
python code/18-unit-dilation-verify_finite.py --output rerun-18.json
pip install -r data/19-newton-rigidity-requirements.txt
python code/19-newton-rigidity-verify.py
python code/16-theta-hierarchy-verify.py --precision 128 --output rerun-16.json
pip install -r data/17-single-scale-requirements.txt
python code/17-single-scale-verify.py --output rerun-17.json
pip install -r data/15-polynomial-composition-requirements.txt
python code/15-polynomial-composition-verify.py --output rerun-15.json
python code/20-recurrences-verify.py > rerun-20.txt
```

The current build gives 245 pages with zero errors, zero warnings, zero
overfull or underfull boxes, zero undefined references, zero multiply defined
labels and zero duplicate PDF destinations; the build of the text before the
merge of source 20 gave 225 pages, that before the merge of source 15 207
pages, that before the merge of sources 16 and 17 175 pages, that before the
merge of sources 18 and 19 137 pages, that before the merge of source 14 118
pages, and that before the merge of source 13 91 pages, equally clean. The
programs of sources 08,
09, 10 and 12 use only the Python standard library with exact integer and
rational arithmetic; those of sources 11, 13 and 14 use exact SymPy and
rational arithmetic (SymPy `>=1.12,<2`, and `>=1.13,<2` for 14). Run them on a
copy of this directory.
`08-finite-recurrences-verify.py`, `10-nonlinear-rigidity-verify.py` and
`12-coefficient-field-rigidity-verify.py` require an explicit `--output` path;
the last two refuse an existing one (12 unless `--force`), so that a rerun
cannot overwrite the delivered record. `11-coarsening-differential-rigidity-verify.py`
without `--output` writes `verification.json` in the current directory, so
always pass a new path. `13-theta-descent-verify.py` requires `--output` but
overwrites an existing file, and its default precision is `q^64`, while the
record was made at `--precision 128`. `14-order-three-threshold-verify.py`
takes no arguments and always writes `data/verification.json` beside its own
`code/` directory: in this directory that is a new file next to the delivered
`data/14-order-three-threshold-verification.json`, which it leaves untouched,
but a second run overwrites the first, so run it on a copy (it needs SymPy
`>=1.13,<2`; its Python 3.9 compatibility was not tested by the source).
`19-newton-rigidity-verify.py` also takes no arguments and writes the **same**
file `data/verification.json` (with the interpreter and SymPy versions); run it
on a copy too. It needs SymPy (`data/19-newton-rigidity-requirements.txt` pins
`sympy==1.14.0`); the source states Python 3.9+. `18-unit-dilation-verify_finite.py`
uses only the standard library (Python 3.10 or later, per the source), prints
its record, and writes a file only when `--output` is given, overwriting that
path; pass a new one. `16-theta-hierarchy-verify.py` (standard library,
Python 3) writes `verification.json` in the current directory unless
`--output` is given, overwriting it; its default precision `p^128` is the
record's. `17-single-scale-verify.py` needs SymPy (`sympy==1.14.0`, Python
3.10+) and without `--output` writes `verification_results.json` **beside
itself** in `code/`, overwriting it; always pass a new path.
`15-polynomial-composition-verify.py` needs SymPy (`sympy==1.14.0`, Python
3.10+; fixed seed 20260923) and without `--output` writes `verification.json`
in the current directory, overwriting it; pass a new path.
`20-recurrences-verify.py` uses only the standard library (Python 3.10+, fixed
seed 20260923), takes no arguments, writes no file and prints its record to
standard output; redirect it to a new file.
The recorded runs passed 3,705 checks (08), 2,043
checks (09), 2,113 checks (10, seed 20260922, six groups: 450 + 240 + 480 +
500 + 360 + 83), 8,673 cases in eight groups (11; 8,136 of them binary-prefix
comparisons), 9,308 checks (12) and 1,622 checks in eleven groups (13, at
precision `q^128`: the product and the third-order equation have zero
residual in every coefficient below `q^128`) and 600 checks in nine groups
(14: 6 + 10 + 242 + 72 + 162 + 5 + 48 + 48 + 7; the theta product and the
cleared equation through `q^47`), 16,579 checks in eleven categories (18,
seed 20260923: 975 + 200 + 1,440 + 12 + 12 + 3,187 + 200 + 3,187 + 205 + 600 +
6,561 in the record's alphabetical order; 6,561 + 1,440 of them are elementary
integer identities, the first zero by construction), 259 checks in
seventeen groups (19), for 16 the listed comparisons (30 Chebyshev, 12 leading
terms, 128 + 128 `p`-coefficients of the product and the order-three identity
below `p^128`, 852 Gauss-profile cases, 65 `Q(√2)` dominance cases, the
squarefree wedge assignment for `N = 1, …, 8`, and 81 grid candidates with 50
nonzero jet determinants; the record gives no total) and 8,608 checks in 21
groups (17; 7,198 of them the band lemma in finite windows) and 2,369 checks
in twelve groups (15: 648 universal encoding, 445 indicial leading terms, 360
integer convexity, 228 Euler projectors, 208 exact resonance, 150 Smith
certificates, 90 + 70 + 35 rank-two operator, pullback and Gauss profiles, 75
boundary coefficients, 48 sharp degree family, 12 worked equations; worked
degree bounds 1, 3, 1, 2) and 4,605 checks in twelve families (20: 1,596
unit coefficient formula, 80 residual parity, 45 principal-unit
cancellation, 810 coordinate transients, 201 higher-rank comparisons, 281
omnific coding, 40 + 88 + 88 Catalan identity, powers and support, 101
partial-theta operator, 875 mixed-operator indexing, 400 positive
characteristic; 810 + 201 + 88 + 90 = 1,189 of them compare integer or
lexicographic facts that hold by construction), with no failures. For this merge the
source 11 and 12 suites were rerun on a copy (Python 3.14.4, SymPy 1.14.0) and
reproduced their records exactly apart from the recorded interpreter version
(recorded runs: Python 3.13.5, SymPy 1.14.0); an earlier rerun of the source 10
suite reproduced its record exactly. For the merge of source 13 its suite
was rerun on a copy (Python 3.14.4, SymPy 1.14.0) and reproduced its record
apart from the interpreter version and the elapsed time (recorded run: Python
3.13.5, SymPy 1.14.0). The same holds for the source 14 suite, rerun on a copy
for its merge (Python 3.14.4, SymPy 1.14.0; recorded run Python 3.13.5, SymPy
1.14.0). For the merge of sources 18 and 19 both suites were rerun on a copy
(Python 3.14.4, SymPy 1.14.0): source 18's reproduced its record exactly, and
source 19's apart from the recorded interpreter version (recorded run: Python
3.13.5, SymPy 1.14.0). Their JSON files were compared after normalizing line
endings, which a Windows run writes as CRLF. For the merge of sources 16 and
17 both suites were rerun on a copy (Python 3.14.4, SymPy 1.14.0): source 16's
reproduced its record apart from the elapsed time, and source 17's apart from
the recorded interpreter version (recorded run: Python 3.13.5). For the merge
of source 15 its suite was rerun on a copy (Python 3.14.4, SymPy 1.14.0) and
reproduced its record apart from the recorded interpreter version (recorded
run: Python 3.13.5, SymPy 1.14.0). For the merge of source 20 its suite was
rerun on a copy (Python 3.14.4) and reproduced its record exactly after
normalizing the CRLF line endings of the redirected output (the record names
no interpreter).

The build helpers were written for their sources' own manuscripts and are
kept byte-identical; do not use them here, use `latexmk` on a copy.
`code/10-nonlinear-rigidity-build.py` would typeset this report, leave
auxiliary files in the directory and write `data/build_report.json`.
`code/11-coarsening-differential-rigidity-build.py` runs `pdflatex` on an
`article.tex` in its own directory `code/`, where there is none, so it fails
and leaves log files (`rebuild-pass-1.log` among them) in `code/`. `code/12-coefficient-field-rigidity-Makefile`
names the delivery paths `article.tex` and `verify.py`: its `all` target would
rebuild `article.pdf` in place and its `verify` target calls a `verify.py`
that is not present under that name. The shipped build records describe the
source manuscripts, which are not shipped: `data/10-nonlinear-rigidity-*` the
23-page source 10 manuscript, `data/11-coarsening-differential-rigidity-build_audit.json`
the 20-page source 11 manuscript (its `pdf_sha256` and `tex_sha256` hash that
manuscript's PDF and source, which are not in this directory), and
`data/12-coefficient-field-rigidity-build_report.json` the 23-page source 12
manuscript (it records a rendering-tool path of the delivery environment).
`code/13-theta-descent-build.py` typesets an `article.tex` in its own
directory `code/`, where there is none: run here it creates `code/build/`,
writes a failed first-pass log there and exits with an error (its `--verify`
option would call a `verify.py` that is not present under that name). In the
delivery layout it wrote only into `build/`. `data/13-theta-descent-build_report.json`
describes the 21-page source 13 manuscript; its `article_tex_sha256` and
`article_pdf_sha256` hash that manuscript's source and PDF, which are not in
this directory. Likewise `data/14-order-three-threshold-build_report.json`
describes the 26-page A4 source 14 manuscript, whose source and PDF, hashed
there, are not in this directory; source 14 shipped no build script, and
neither did source 18, which also shipped no build record.
`code/19-newton-rigidity-build.py` runs `pdflatex` on an `article.tex` in its
own directory `code/`, where there is none, so it fails there (and may leave a
LaTeX log in `code/`); its `--verify` option would call `code/code/verify.py`,
which does not exist. `data/19-newton-rigidity-build_audit.json` describes the
24-page source 19 manuscript (TeX Live 2025/dev on Debian, one remaining
underfull-box warning), whose source and PDF, hashed there, are not in this
directory. `code/16-theta-hierarchy-Makefile` names the delivery paths
`article.tex` and `verify.py`: its default target would run `latexmk` on any
`article.tex` in the current directory, and its `verify` target calls a
`verify.py` that is not present under that name;
`data/16-theta-hierarchy-build_audit.json` describes the 25-page source 16
manuscript, which is not shipped. `code/17-single-scale-build.py` looks for an
`article.tex` in `code/` and stops with an error before writing anything; in
its delivery layout it wrote `.build/`, `article.pdf` and `build_audit.json`
in place. `data/17-single-scale-build_audit.json` and
`data/17-single-scale-visual_audit.json` describe the 24-page source 17
manuscript, which is not shipped. `code/15-polynomial-composition-Makefile`
runs `pdflatex` three times on an `article.tex` in the current directory,
rebuilding `article.pdf` in place; its `verify` target calls a `verify.py`
that is not present under that name, and its `clean` target deletes auxiliary
files with `rm -f`. `data/15-polynomial-composition-BUILD_REPORT.json`
describes the 24-page source 15 manuscript (TeX Live 2025/dev on Debian, no
warnings), which is not shipped. `code/20-recurrences-build.sh` was written
for source 20's delivery layout: it changes to its own directory, runs
`pdflatex` three times on an `article.tex` there, then runs
`python3 verify.py > verification.txt`, **overwriting that record by
redirection**, and prints it. Here its directory is `code/`, which has neither
file: run in this layout it stops at the first `pdflatex` call with an error
and leaves `texput.log` in `code/` (checked on a copy). Do not run it here;
source 20 shipped no build record, and its 22-page manuscript is not
shipped.


## Subsequent proof review

This review predates the merges of sources 10, 11 and 12; its page counts and
file counts refer to the 08+09 report.

The main support, recurrence, orbit, differential, generic-line, dilation,
theta-domain, torsion and mixed-operator proofs were read with the examples
and their downstream uses.

A new support lemma proves inward stability: if a nonzero `x` admits strong
evaluation, so does every `y` with `v(y) ≥ v(x)`. Membership of a fixed series'
domain therefore depends only on the argument valuation, and entireness can
be tested on monomials. This retains the full Hahn coefficient supports;
leading coefficient valuations alone need not determine a boundary domain.

The torsion equivalence now holds without divisible exponents. For an argument
of valuation `δ`, evaluate the outer series at `t^γ` with `γ = min(δ,0)`.
The inner series is then evaluable at `t^(mγ)` and inward stability reaches
the desired argument. No `m`th root in the Hahn field is needed.

The refined recurrence statements now handle absent forward slots explicitly
and place the starting index after the periodic pattern begins. The unit-orbit
application chooses period one for a nontorsion residue. The explicit
infinite-rank witness's cofinal-valuation proof works for arbitrary Hahn tails.

The optional coarsening remark now retains the original field and changes
only its valuation. It is not a coefficientwise map into a smaller Hahn field:
projecting `Σ t^(nε)` along a quotient killing `ε` would collapse infinitely
many coefficients to one exponent. The normal-form, generic-line and
cofinality proofs remain distinct from finite numerical verification.

Historical code, data and source audit files are preserved. Literature priority,
original-source reconciliation and the unformalized main theorem package remain
separate review obligations.

The classical recurrence correspondence was checked against
[Stanley's author-hosted paper](https://math.mit.edu/~rstan/pubs/pubfiles/45.pdf),
Theorem 1.5 (printed page 176). The report supplies its own coefficient
conversion over the stated Hahn field. The optional coarsening was checked
against the local `ent:lem:coarsening`; the broader literature comparisons
were not independently re-audited.

During that review, `origin/main` added the checked escape-chain and formal
exponential-domain results. At that milestone the new inward-stability proof
was not yet formalized; subsequent Lean work covers it and the other results
listed in the current coverage summary above.

The reviewed article and catalogue rebuilt in three passes at 39 and 21 pages.
The status note now fits on the title page; the baseline placed it on a
separate page. Both unchanged finite suites reproduce the historical outputs
exactly, with all six copied code/data files byte-identical to their sources.
The three delivered source audits are also preserved.

## Merge of source 10

Source 10's code, data and two audit files are byte-identical to the
delivered manuscript package; its own README, checksum list, article source
and PDF are not shipped. Every source 10 result is printed in Sections 14–17,
with its proof, except the facts listed above as printed once. Its three
further questions became Question 19.1 (the re-scoped nonlinear question),
Question 19.2 (vector fields beyond positive Euler operators) and
Question 19.3 (effective representations and minimal certificates). Source
10's references to "Question 15.1" and "Theorems A–C" of this report were
accurate at its pin `048b72c`, where the report was identical to the text it
was merged into. Its main nonlinear rigidity theorems remain unmapped in the
implementation ledger, and the delivered package includes no independent
referee report. A merge-added remark (Section 15.1) combines Theorem 15.1 with
inward stability for `k = C`, and a merge-added comparison (Section 15.5)
notes that each `t^λ/(1 − t^λ z)` also satisfies a λ-dependent linear
equation.

## Nonlinear proof review

The source-10 review covers Theorem D, Sections 14–17 and the corresponding
limitations in Section 19.3. It expands strong-family multiplication, Gauss
multiplicativity, the active initial polynomial and the finite scale
comparison. An explicit cancellation example separates the coefficient Gauss
value from the valuation after evaluation. The cofinal-scales proof now
handles equations independent of the unknown function, and denominator
clearing is explained in the formal Laurent field.

The higher-order proof identifies the precise degree whose coefficient must
vanish. Two equations with the same formal solutions now illustrate that
one can have a nonzero corner polynomial while the other has zero corner.
The Euler proof gives an explicit bounded-weight count; its comparison with
the finite mixed-derivative criterion no longer asserts their nonimplication
on the strongly entire class. The README's Euler summary retains the
nonzero-equation hypothesis. The notation guide separates residue/full
corners, rational degree cutoffs and value-group exclusion scales.

The targeted literature comparison retains Hu–Luan's characteristic-zero
hypothesis and limits the repository comparison to its named sources and
historical pin. Current primary checks do not certify priority or replace
the source's historical audit. Sources 11 and 12's all-order proofs remain
outside this main-text review, and no Lean coverage is added. The detailed
scope and validation are in the [collection review record](../../REVIEW.md#nonlinear-holonomic-main-text-review).
All 81 standard statements and seven principal theorems A–G are unchanged,
as are the 274 source labels and their numbers. Baseline and revised PDFs
passed three LaTeX passes, with no final warnings or box notices. The revised
90-page report was visually checked on 26 affected/context pages. All 28
historical audit/code/data files remain unchanged. The source-10 suite was
rerun on a copy under Python 3.13.14: all 2,113 checks pass and the full
record differs from the delivered JSON only in the Python version.


A subsequent coverage sync updates the current status for already proved
partial-theta implications, polynomial-orbit valuations, constant-point
avoidance, inward stability and torsion covariance. Section 13.3 distinguishes
those results from the remaining support, closure and classification steps.
After this prose update the three-pass PDF still has 90 pages, with no final
warnings or box notices. All 88 result statements, 274 label numbers and 28
historical files remain unchanged. All 54 pages affected by the coverage
text and its reflow (physical pages 1–2, 34–83 and 86–87) were visually checked.


## Main-text review of the coefficient-field part

The review covers sources 11 and 12's Theorems E–G and Sections 20–22. It
expands valuation-rank and coarsening arguments, separates rational from
Laurent denominator clearing, and shows that the linearization multiplier
is determined by a fixed initial segment before coefficient recovery starts.
Rationality descent now explicitly lifts a finite rational identity through
the embedded coefficient field. Corollary 22.9 combines those results to
prove mixed-jet independence for nonrational quotients of entire series
without an order unit; neither source states that added consequence.

The rank definition and boundary summaries are corrected, with an explicit
zero-rank formal series that still has independent mixed jets. The branch
family proof explains independence over the other coefficient fields.
The current notation and hypothesis audit distinguish variable derivatives,
dilations, Laurent series, coefficient-value rank and coarsened residue.
The [collection review record](../../REVIEW.md#coefficient-field-holonomic-main-text-review)
states the precise literature checks and remaining obligations. This adds
source-level proofs, not Lean declarations.

The baseline and revised PDFs each pass three LaTeX passes with clean final
logs; the revised report has 91 pages. All 33 pages with changed text or
pagination and the unchanged transition page 62 were visually inspected
(34 revised pages total), with no layout findings. All 274 previous label
numbers remain, and the new corollary is 22.9. The 88 earlier result statements
are unchanged except for making the existing characteristic-zero assumption explicit in
Corollary 21.8; there are now 82 standard statements and seven main theorems.
All 28 historical audit/code/data files are preserved. On copied scripts,
source 11's 8,673 cases and source 12's 9,308 checks pass; their full records
match the delivered records apart from Python 3.13.5 becoming 3.13.14.

## Merge of sources 11 and 12

The code, data and audit files of sources 11 and 12 are byte-identical to the
delivered packages. Not shipped: their article sources, PDFs and delivery
READMEs, and source 11's checksum list (its ten entries were verified before
it was dropped). Every result of both sources is printed in Sections 20–22 or
the introduction, with its proof, except the facts listed above as printed
once; Section 20.1 maps each numbered result of each source to its place here.
Both sources' references to this report (Questions 19.1 and 19.4, the README's
statement of the vanishing-corner boundary, the source 10 audit's
"Question 15.1") were accurate at their pin `465a54b`, at which this report was
unchanged up to the merge. The statements of this report that called the
vanishing-corner case open (the abstract, Sections 1, 5, 10, 11.4, 16.2, 17.1,
19 and the conclusion, and this README) have been re-scoped to groups with an
order unit, and Questions 19.1, 19.4 and 19.6 re-scoped, with their original
wording recorded in their status paragraphs. Source 11's Question 9.1 and
source 12's Question 10.1 are the same question and were merged into the
re-scoped Question 19.1; their other questions are 19.7–19.9. The coefficient-field
part has not been independently refereed or formalized.

## Merge of source 13

The code, data and audit files of source 13 are byte-identical to the
delivered package. Not shipped: its article source, PDF and delivery README,
and its checksum list (all ten entries verified before it was dropped). Every
result of source 13 is printed in Sections 23–25 or the introduction, with its
proof, except the facts listed above as printed once; Section 23.1 maps each
numbered result to its place here. The statements of this report that called
the order-unit case open have been updated: the abstract, Sections 1
(Theorem D remark, Theorem G and the remark after it), 5 (Remark 5.8), 11.3
(the tables and Corollary 11.3), 13.3 (Lean coverage), 16.2, 17.1, 18 (now six
suites), 19 (the attribution ledger, N1–N3, Questions 19.1, 19.4 and 19.8),
21.4, 22.5, 22.7 (C1), the conclusion, the appendices and this README.
Question 19.1 is re-scoped to order two, with its previous wording recorded
in its status paragraph; source 13's Questions 11.1 and 11.2 were merged into
it, and its Question 11.3 is Question 19.10. The reciprocal statements in
`docs/README.md` and `docs/manifest.tex` are outside this directory. The
theta-descent part has not been independently refereed or formalized, and it
is outside the scope of the two earlier main-text reviews recorded above.

## Merge of sources 18 and 19

The code, data and audit files of sources 18 and 19 are byte-identical to the
delivered packages (placement `9d28e28`). Not shipped: their article sources,
PDFs and delivery READMEs, and source 19's checksum list (verified before it
was dropped). Every result of both sources is printed in Sections 28–31 or the
introduction, with its proof, except the facts listed above as printed once;
Sections 28.1 and 30.1 map each numbered result to its place here. Both
sources' references to this report were accurate at their pins, at which the
report was the five-source text. The statements that called Question 19.4
open or the mixed unit-valuation case unclassified (Section 10, Section 19's
ledger and statuses, Section 22.5, Section 25.2, Appendix B and this README)
now record source 18's answer; Question 19.6 is re-scoped; Questions 19.1,
19.11 and 19.13–19.17 carry status notes for source 19. Source 18's Research
question 11.1 is answered in the current text and recorded in Remark 29.19;
its questions 11.2–11.12 are 19.19–19.29. Source 19's Question 12.1 is
answered by Theorem H, its Questions 12.4, 12.6 and 12.8 are 19.15–19.17, and
its Questions 12.2, 12.3, 12.5, 12.7, 12.9 and 12.10 are 19.30–19.35. Neither
part has been independently refereed or formalized.

## Merge of sources 16 and 17

The code, data and audit files of sources 16 and 17 are byte-identical to the
delivered packages (placement `9d28e28`). Not shipped: their article sources,
PDFs and delivery READMEs. Every result of both sources is printed in
Sections 32–35 or the introduction, with its proof, except the facts listed
above as printed once; Sections 32.1 and 34.1 map each numbered result to its
place here. Their references to this report were accurate at their pins, at
which the report was the five-source text. Source 16's Question 11.2 is
answered by Theorem I (Remark 32.18) and its other nine questions are
19.36–19.44; source 17's Question 12.1 is answered by Theorems H and I (Remark
35.20) and its other ten are 19.45–19.54. The remarks after Theorem 21.20 and
Corollary 25.7, the status of Question 19.1, Section 19's ledger, Section 18
and the appendices were updated. Neither part has been independently refereed
or formalized.

## Merge of source 15

The code, data and audit files of source 15 are byte-identical to the
delivered package (placement `9d28e28`). Not shipped: its article source, PDF
and delivery README. Every result of the source is printed in Sections 36–37
or the introduction, with its proof, except the facts listed above as printed
once; Section 36.1 maps each numbered result to its place here. Its
description of this report was accurate at its pin, at which the report was
the five-source text; its "no Mahler material" statement was not, and is
corrected in Sections 36.1 and 37.5. Its Questions 12.1–12.8 are 19.55–19.62.
The status of Question 19.6, Section 19's ledger, Section 18 and the
appendices were updated, and the title-page count of pending theorem packages
now names all nine later parts. The part has not been independently refereed
or formalized.

## Merge of source 20

The code, data and audit files of source 20 are byte-identical to the
delivered package (placement `aa9c891`, rechecked against a fresh extraction
of the archive in `73043eb`). Not shipped: its article source, PDF and
delivery README, and its checksum list (verified at placement and dropped).
Every result of the source is printed in Sections 38–39 or the introduction,
with its proof, except the facts listed above as printed once; Section 38.1
maps each numbered result to its place here. Its description of this report
was accurate at its pin `efc5446` (the seven-source text) and is stale
against the current one, which already contains source 18; its gap claim is
recorded, not repeated (Remark 39.11). Its Questions 12.3, 12.4, 12.6–12.10
and 12.12 are 19.63–19.70 (12.7 re-scoped), and 12.1, 12.2, 12.5 and 12.11
are recorded in the statuses of Questions 19.24, 19.21, 19.25 and 19.29. The
statuses of Questions 19.4, 19.22 and 19.28, Section 19's ledger, Section 18,
Section 13.3, the abstract, the title-page status (now "ten later parts") and
the appendices were updated. The abstract's divisibility sentence was
shortened, without change of content, so that the status note stays on the
title page. The part has not been independently refereed or formalized.
