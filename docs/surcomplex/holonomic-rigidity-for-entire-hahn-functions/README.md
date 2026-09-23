# Holonomic Rigidity for Entire Hahn Functions

**A sharp order-unit criterion for dilations, with uniform exclusion bounds,
and the exact boundary of nonlinear differential rigidity: first-order for
every value group, all orders when the value group has no order unit, and an
explicit series of minimal differential order three when it has one**
Merged research report, 22–23 September 2026, from six manuscripts: 08 and 09,
written independently on the same day; 10, which adds the nonlinear part; 11
and 12, written independently and delivered together later, which add the
coefficient-field part; and 13, delivered later still, which adds the
theta-descent part.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 118 pages
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
```

Every label in `article.tex` carries the prefix `hol:`; the nonlinear part
uses the sub-prefix `hol:nl:`, the coefficient-field part `hol:cf:` and the
theta-descent part `hol:td:`. The merge of sources 11 and 12 renamed or
removed no label: the report had 199 labels before it and had 274 after it,
all 199 original labels still present. The later coefficient-field review
adds `hol:cf:cor:meromorphicmixed`, giving 275 labels while preserving every
earlier label and number. The merge of source 13 adds 85 labels, all with the
prefix `hol:td:`, giving 360; all 275 earlier labels are present and keep
their numbers (checked against the `.aux` files of the builds before and after
the merge). The audit files and programs keep the source numbers `08` to `13`
of the batches they arrived in, and the audit files keep their sources' own
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
conclusion. The nonlinear and coefficient-field parts use no divisibility.

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
  conclusion is now Section 26. Its principal theorem is Theorem H in the
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

## What the report does not claim

- The arbitrary-rank classification is offered as a **proposed original
  contribution**. Priority is not certified, no named published conjecture is
  claimed solved, and the proofs have not been independently refereed.
  The [Lean ledger](../../FORMALIZATION.md) records support and escape
  lemmas, exponential and partial-theta domains, polynomial-orbit
  valuations, constant-point avoidance, inward stability and torsion
  covariance. In particular, the partial-theta construction proves one
  direction of the dilation classification and of the order-unit detection
  equivalence. The full classifications and the nonlinear and coefficient-field
  theorem packages remain pending. The detailed coverage is in Section 13.3.
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
  coefficient-value rank, including the rank-one example of Theorem 21.20.
  Source 10 answers the first-order case of the nonlinear question, plus the
  higher-order equations with `χ_P ≠ 0` and positive-weight Euler relations,
  for every `Γ`; sources 11 and 12 answer all orders, including a vanishing
  residue corner, when `Γ` has no order unit; source 13 answers the case with
  an order unit by the example of order three. Whether a nonpolynomial
  strongly entire series can have minimal order exactly two, and a
  classification of the differentially algebraic ones, stay open
  (Question 19.1, re-scoped three times: from what was Question 15.1, to
  groups with an order unit, and now to order two). The equation
  `z²ff'' + zff' − z²f'² = 0` has polynomial solutions of every degree but is
  not a nonpolynomial counterexample (Proposition 16.4); partial theta is not
  a counterexample either (it satisfies a dilation equation), and whether
  `Θ_p` or `Σ t^(n²) z^n` is differentially algebraic is not decided. The
  escape proof does not extend to nonlinear equations in any order. Mixed equations at unit
  valuation are open when `Γ` has an order unit (Question 19.4, formerly 15.2,
  now re-scoped); several dilations are open with an order unit and for
  parameters with a root-of-unity quotient (Question 19.6, re-scoped).
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
  given and minimal order two is open; "no omnific zero" concerns the strong
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
- The finite checks validate coefficient conversions, identities, cancellation
  examples and finite ordered-group examples. They do not establish the
  infinite support arguments, the cofinality claims, the generic-line theorem,
  the nonexistence of annihilating operators, the coefficient-field theorem,
  the descent, any independence statement, or the minimal order of `𝒯_p`.

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
Theorem E), and mixed-jet independence (Theorem G). Neither implies the
other. The polynomial half of the coarsening descent (Theorem 21.11) is a
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
neither is transferred to the other's derivation.

**[hahn-tate-uniformization](../hahn-tate-uniformization/)** studies the
bilateral theta series `Σ (−1)^n q^(n(n−1)/2) u^n`, its strong domain and its
product at arbitrary rank. The bilateral series `Ψ_p` of the theta-descent
part is that series at the nome `p²` and the argument `−pu`; its domain and
product are specialized here, not claimed anew, and the new material is the
descent to the entire power series `𝒯_p` and its differential algebra.
**[omnific-diophantine-geometry](../../surreal/omnific-diophantine-geometry/)**
supplies the definition `Oz = Z ⊕ Π` (`odg:def:rings`) used for the omnific
rounding of the zeros of `𝒯_{ω⁻¹}` (Corollary 25.3); that corollary concerns
an infinite-series equation, not a Diophantine one.

**[single-dilation-hahn-support](../single-dilation-hahn-support/)** also speaks
of dilations, but there a dilation is an automorphism `t^g ↦ t^(qg)` of the
scalar field; here it is always the argument dilation `f(z) ↦ f(λz)` with a
fixed scalar `λ`. The two reports share the word, not a theorem.

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
```

The current build gives 118 pages with zero errors, zero warnings, zero
overfull or underfull boxes, zero undefined references, zero multiply defined
labels and zero duplicate PDF destinations; the build of the text before the
merge of source 13 gave 91 pages, equally clean. The programs of sources 08,
09, 10 and 12 use only the Python standard library with exact integer and
rational arithmetic; those of sources 11 and 13 use exact SymPy and rational
arithmetic (SymPy `>=1.12,<2`). Run them on a copy of this directory.
`08-finite-recurrences-verify.py`, `10-nonlinear-rigidity-verify.py` and
`12-coefficient-field-rigidity-verify.py` require an explicit `--output` path;
the last two refuse an existing one (12 unless `--force`), so that a rerun
cannot overwrite the delivered record. `11-coarsening-differential-rigidity-verify.py`
without `--output` writes `verification.json` in the current directory, so
always pass a new path. `13-theta-descent-verify.py` requires `--output` but
overwrites an existing file, and its default precision is `q^64`, while the
record was made at `--precision 128`. The recorded runs passed 3,705 checks (08), 2,043
checks (09), 2,113 checks (10, seed 20260922, six groups: 450 + 240 + 480 +
500 + 360 + 83), 8,673 cases in eight groups (11; 8,136 of them binary-prefix
comparisons), 9,308 checks (12) and 1,622 checks in eleven groups (13, at
precision `q^128`: the product and the third-order equation have zero
residual in every coefficient below `q^128`), with no failures. For this merge the
source 11 and 12 suites were rerun on a copy (Python 3.14.4, SymPy 1.14.0) and
reproduced their records exactly apart from the recorded interpreter version
(recorded runs: Python 3.13.5, SymPy 1.14.0); an earlier rerun of the source 10
suite reproduced its record exactly. For the merge of source 13 its suite
was rerun on a copy (Python 3.14.4, SymPy 1.14.0) and reproduced its record
apart from the interpreter version and the elapsed time (recorded run: Python
3.13.5, SymPy 1.14.0).

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
this directory.


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
