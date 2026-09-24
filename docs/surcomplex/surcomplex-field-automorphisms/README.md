# Automorphisms of the Surcomplex Numbers

**Real forms, Hahn symmetries, valuation, rigidity, and finite symmetry descent**
Three-source research report. Author lines: research article prepared with
ChatGPT (source 01); research article prepared with ChatGPT for Vladimir
Reshetnikov (source 02); research manuscript prepared with ChatGPT for
Vladimir Reshetnikov (source 03).

- **Source 01** (Sections 1–15, Appendices A–C.2): manuscript 07 of batch 20
  (archive `surcomplex_automorphisms`), 22 September 2026, pinned to
  repository commit `dcf8666`, placed in commit `5fe7f8d` as a new report.
- **Source 02** (Sections 16–30, Appendix C.3): manuscript 02 of batch 32
  (archive `surreal_finite_symmetry_descent`), *Finite Symmetry Descent and
  Real Forms of Gaussian Omnific Integers*, 23 September 2026, 27 pages,
  pinned to `343dc2c`, placed in commit `7d04483` as this report's first
  addition (local number 02; source 01 counts as 01).
- **Source 03** (Sections 31–40, Appendix C.4): manuscript 03 of batch 34
  (archive `gaussian_omnific_real_forms`), *Gaussian-Omnific Real Forms and
  Geometric Symmetrization*, 23 September 2026, 24 pages, pinned to
  `110efe9`, placed in commit `a7a435f` as this report's second addition
  (local number 03). It is an independent re-derivation of source 02's main
  results, with an explicit inverse, a characteristic-free descent and the
  arithmetic of the fixed rings as new material.

Every result, proof, example, question and limitation of the three manuscripts
is printed. A result the collection already proves is printed once, with
credit; text added when source 02 or source 03 was merged is marked `[merge]`
in the article.

```
article.tex                                        the report, standalone LaTeX with an internal bibliography
article.pdf                                        the compiled report, 89 pages (title, contents i–iii, pages 1–85)
README.md                                          this guide
02-finite-symmetry-descent-SOURCE_AND_PROOF_AUDIT.md   source 02: source and proof audit, as delivered
03-gaussian-real-forms-SOURCES.md                  source 03: source and claim audit, as delivered
code/
  02-finite-symmetry-descent-build.sh              source 02: delivered build helper (do not run in place; see below)
  02-finite-symmetry-descent-verify_finite.py      source 02: exact finite checks (Python 3.10+, standard library)
  03-gaussian-real-forms-build.sh                  source 03: delivered build helper (not usable as shipped; see below)
  03-gaussian-real-forms-verify.py                 source 03: exact finite checks (Python 3.9+, standard library)
data/
  02-finite-symmetry-descent-build_validation.json     source 02: the delivery's build and PDF-inspection record
  02-finite-symmetry-descent-verification.json         source 02: recorded run at order 12, 3,751 assertions
  02-finite-symmetry-descent-verification_console.txt  source 02: console copy of that run (same bytes)
  03-gaussian-real-forms-verification.json             source 03: recorded run at order 8, 457 assertions
```

Every label in `article.tex` carries the prefix `saut:`; source 02's material
uses the sub-prefix `saut:fs:`, source 03's `saut:gr:`. Source 01's 86
labels (its 79 plus the 7 added at placement: `saut:sec:conventions`,
`saut:sec:position`, `saut:eq:Lchain`,
`saut:sec:nonclaims`, `saut:app:conjugacy`, `saut:app:provenance`,
`saut:app:pinned`) are all kept, and every one of their numbers is unchanged
(checked against a build of the previous text). The merge of source 02 added
83 labels, 169 in all: 82 `saut:fs:` labels (62 of the source's 66, unchanged
after the prefix, and 20 new) and `saut:app:source02`. Not carried:
`eq:surreal-hahn` (it is `saut:eq:hahn`, printed once) and the closing labels
`sec:conclusion`, `app:audit`, `app:formalization` (now inside
`saut:fs:sec:closing`). The merge of source 03 (sub-prefix `saut:gr:`, unused
before) kept all 169 labels with unchanged numbers (checked against a build of
the committed text) and added 59, 228 in all: 58 `saut:gr:` labels and
`saut:app:source03`. Source 03's own bare labels (`thm:overview`,
`thm:orbit`, …) are not carried: each of its results is either mapped to an
existing label (Section 31.2) or printed under a new one. The source
manuscripts, their PDFs and delivery READMEs, and source 03's checksum
manifest `SHA256SUMS.txt` (7 entries, verified), are not shipped;
`article.pdf` is a build of this text. The `02-` and `03-` files are
byte-identical to the delivery.

## Which automorphisms

Let `K = No(i)`, `c` its conjugation, `O` the finite ring and `v` the natural
valuation (`t^g = ω^{-g}`, `v = min supp`). The report never says
"automorphism" without the structure preserved (Section 1.4):

- **plain field automorphism** — any ring automorphism: `Aut(K)`, `Aut(No)`;
- **valued automorphism** — `α(O) = O` (the group `G_v`), so
  `v(αz) = τ_α(v z)` for an ordered automorphism `τ_α` of the value group; it
  need not fix any value. Every field automorphism of `No` is valued; one of
  `K` need not be;
- **value-fixing** — valued with `τ_α = id`;
- **1-automorphism** — `v(αz − z) > v(z)` for all `z ≠ 0` (the group `U`),
  i.e. every leading term fixed; the leading-term notion of Kaplan–Krapp–Serra;
- **exponential automorphism** — an automorphism of `No` commuting with the
  surreal `exp` (`Aut_exp(No)`); there is no surcomplex exponential here;
- **L-automorphism** — an automorphism of `K` commuting with the logarithmic
  modulus `L(z) = log|z|` (`Aut_L(K)`, the rigidity report's notation);
- **(source 02)** `𝒢 = {α ∈ G_v : α(Oz[i]) = Oz[i]}`, the valued automorphisms
  preserving the Gaussian omnific integers. Source 02 required them to be
  strong as well; that is automatic (below).

`U ⊆ value-fixing ⊆ G_v ⊆ Aut(K)` and
`{id, c} = Aut(K/No) ⊆ Aut_L(K) ⊆ G_No ⊆ G_v`, where `G_No` is the setwise
stabilizer of `No`.

## What the report claims

Section and theorem numbers are those of the build.

### Source 01 (Sections 1–15, Appendices A–C.2)

- **Real axis (Theorem 2.2).** For real closed `F`, `Aut(F(i)/F) = {id, c}`,
  and the setwise stabilizer of `F` is the centralizer of `c` and is
  `≅ Aut(F) × C₂`. Exact norm or modulus preservation forces `id` or `c`
  (Theorem 2.3); preserving the unit circle setwise is equivalent to
  preserving `F` (Theorem 2.4).
- **Explicit Hahn automorphisms (Theorem 4.1).** `M_{ρ,τ,χ}` (coefficient
  automorphism `ρ`, ordered exponent automorphism `τ`, arbitrary character
  `χ: No → C^×`) is a strong field automorphism with a stated composition law;
  it preserves `No` exactly when `ρ ∈ {id, c}` and `χ > 0`. Special cases: the
  dilations `S_a` (`ω ↦ ω^a`), witnessing `Aut(K/No) ⊊ G_No`; positive
  characters `D_λ`; and the **phase twists** `P_θ` (Theorem 4.2), a faithful
  action of `(R,+)` by strongly `C`-linear, value-fixing automorphisms that
  move `No` (`P_{π/2}(t) = it`), witnessing `G_No ⊊ Aut(K)` with no choice.
  The conjugates `P_{2θ}c` have pairwise distinct fixed fields, all `≅ No`.
- **Leading-term kernel (Theorems 5.1, 5.2).** Taylor motions `Φ_d` are
  1-automorphisms. Suitable derivations preserving `R` give motions that
  preserve `No` and move a real transcendental constant `b ↦ b + t^δ`;
  fixed-shift flows `T_s` (e.g. `t ↦ t/(1−st)`) are strongly
  `C`-linear 1-automorphisms.
- **Four layers (Theorem 6.1).** Every valued automorphism factors uniquely as
  `u · D_χ · M_{ρ,τ}`: `G_v ≅ (U ⋊ Hom(Γ,C^×)) ⋊ (Aut(C) × Aut_ord(Γ))`; for
  `No`, `(U_R ⋊ Hom(Γ,R_{>0})) ⋊ Aut_ord(Γ)` (6.5), and a further
  kernel–skeleton layer for `Aut_ord(Γ)` (Section 6.2).
- **Topology (Propositions 7.1, 7.2; Section 7.2).** Valued automorphisms are
  fine homeomorphisms; set-sized subsets are closed and discrete; an explicit
  fine-continuous real-axis-preserving automorphism fails to preserve a Hahn
  sum. The finite observations also show non-density of strong maps in the
  pointwise-equality topology on both `Aut(No)` and `Aut(K)`.
- **Derivatives (Theorems 8.1, 8.2; Corollary 8.3).** A field automorphism
  with a fine derivative somewhere has the same derivative everywhere, and a
  nonzero one forces the identity; `S_a` (`a > 1`) has derivative 0
  everywhere, while `0 < a < 1` gives no `K`-valued derivative; only the
  identity is bidifferentiable.
- **Pure field (Theorems 9.1, 9.2; Propositions 9.3, 9.4).** Class
  back-and-forth (global choice): `Aut(K/C)` is transitive on `K \ C`; for any
  set of parameters some automorphism fixing them moves `No`, and some moves
  `O`, so neither is definable in the pure field; `G_No ⊊ G_v ⊊ Aut(K)`;
  fixed fields `Q`, `C`, `Q^rc`, `Q^rc`, `Q̄`.
- **Real forms (Theorems 10.1, 10.2; Proposition B.1).** Nontrivial finite
  subgroups of `Aut(K)` have order 2, each involution fixes a real form; a real
  form with a countable cofinal subset exists, so not every involution is
  conjugate to `c`; an involution is conjugate to `c` iff its fixed field has
  the set-cut interpolation property.
- **Exponential structure (Section 11).** Simplicity plus order forces the
  identity; commuting with the omega-map and fixing values forces the
  identity. Lemma 11.1, Theorem 11.2 (faithful value-group action), the
  equation `ker(Aut_exp(No) → Aut_ord(Γ)) = {id}` (11.2), Proposition 11.3
  (no exponential automorphism induces `g ↦ qg`, `q ∈ Q_{>0} \ {1}`) and
  Theorem 11.4 (`Aut_L(K) ≅ Aut_exp(No) × C₂`, value-action kernel `{id, c}`)
  are the rigidity report's results, reprinted with attribution.
- **Observation of the edit (1.2).** `Aut_L(K) = {α ∈ G_No : α|No ∈
  Aut_exp(No)} ⊊ G_No`, strict by `S_q` (`q` rational, `≠ 1`). Whether
  `{id, c} ⊊ Aut_L(K)`, i.e. whether `Aut_exp(No)` is nontrivial, is not
  decided.
- **Questions (Section 14):** the image of exponential automorphisms in the
  value group (the rigidity report's Question 13.1); omega-map compatibility
  (KKS Questions 5.6, 5.7); effective descriptions inside `U`; real-form and
  continuity classifications. The real-form classification is now **partly
  answered** by source 02 (status note in Section 14): the valued,
  `Oz[i]`-preserving case is classified. The rest is open.

### Source 02 (Sections 16–30)

Notation: `K = k((t^Γ))` a full Hahn field over a set-sized field `k` of
characteristic 0, `Γ` a set-sized divisible ordered group or `No` (set
supports), `𝓘` the strictly negative-support part, `ct` the constant
coefficient, `M_ρ` the coefficientwise lift of `ρ ∈ Aut(k)`.

- **Finite symmetry descent (Theorem 16.1, proved in Section 20).** If a
  finite group `G` of order `n` acts on `K` by valued automorphisms
  stabilizing `k` and `𝓘`, then `𝓗(Σ a_γ t^γ) = Σ a_γ m_γ`, with the norm
  section `m_γ = ∏_{g∈G} g(t^{γ/n})`, is a strong `k`-linear value-fixing
  automorphism with `𝓗(𝓘) = 𝓘`, `ct ∘ 𝓗 = ct` and `𝓗⁻¹ g 𝓗 = M_{g|_k}`;
  restriction to `k` is faithful. Proof ingredients: invariant section
  (Lemma 20.1), diagonal summability (20.2), value-preserving embedding (20.3),
  surjectivity by spherical completeness (Lemmas 19.1, 19.2) and, for
  `Γ = No`, by an invariant set-sized exponent closure (Lemma 19.3, no class
  maximality principle), then `𝓗(𝓘) = 𝓘` and inverse strongness by the
  pairing test. Fixed fields and support rings (Corollary 20.4).
- **Pairing test (Lemma 18.1, Theorem 18.2, Corollary 18.3).** A family is
  Hahn summable iff every `y` has `ct(x_i y) ≠ 0` for finitely many `i`
  (Baire-category proof); a `k`-linear `ct`-preserving automorphism is strong
  both ways. These are `opa:as:thm:detect` and `opa:as:thm:ctiso` of the
  omnific-preserving report, which prove more; printed once, credited.
- **[merge] Automatic strongness (Proposition 18.5, Remark 22.3).** A valued
  automorphism stabilizing `k` and `𝓘` satisfies `ct ∘ g = g|_k ∘ ct` and is
  strong both ways (via `M_ρ` and Corollary 18.3; this is `opa:as:thm:ctiso`).
  So source 02's strongness hypotheses are redundant, and `𝒢` equals the
  source's class (`opa:as:thm:gaussian`).
- **Lifts and torsion (Corollaries 21.1, 21.2).** All finite valued lifts of a
  coefficient action are conjugate by the kernel `𝓝` (strong `k`-linear
  value-fixing automorphisms preserving `𝓘`); finite-order elements fixing
  `k` are trivial; the nonabelian `H¹(Θ, 𝓝)` of a finite group is trivial. No
  statement about infinite groups.
- **Reconstruction (Proposition 22.1, Corollary 22.4).** For `𝔬 = Z` or
  `Z[i]`: `Frac(𝔬 + 𝓘) = K`, `𝓘 = ∩ n(𝔬 + 𝓘)`, `(𝓘 : 𝓘) = k + 𝓘`,
  `k = (k + 𝓘)^× ∪ {0}`; `R_F ≅ R_{F'}` iff `F ≅ F'`. Prior material
  (`opa:lem:divisible`, `odg:def:thm:multiplier`, `odg:thm:fractions`),
  reproved.
- **Involutions of `No[i]` (Theorem 16.2; Propositions 23.1, 23.2).** Every
  nonidentity involution `j ∈ 𝒢` restricts to a nonidentity involution `ρ` of
  `C` and equals `𝓗_j M_ρ 𝓗_j⁻¹` with `𝓗_j(t^γ) = t^{γ/2} j(t^{γ/2})`.
  Conjugacy in `𝒢` ⇔ conjugacy of `ρ` in `Aut(C)` ⇔ `C^{ρ₁} ≅ C^{ρ₂}` ⇔
  isomorphic fixed rings. With `F = C^ρ` the fixed pair is
  `(No_F, R_F) = (F((t^No)), Z + F((t^{No<0})))`; the possible `F` are exactly
  the real closed fields of transcendence degree `𝔠`. Nontrivial finite
  subgroups of `𝒢` have order 2 (Corollary 23.3, contained in Theorem 10.1).
- **Integer parts and the standard form (Theorem 16.3; Lemma 24.2,
  Theorems 24.3, 24.4, Corollary 24.5, Proposition 24.6).** `R_F` is
  discretely ordered with least positive element 1; it is an integer part of
  `No_F` iff `F` is Archimedean, with an explicit floor formula (24.1);
  `No_F ≅ No` (as plain fields) iff `F ≅ R`, by explicit omitted set cuts; so
  `j ∈ 𝒢` is conjugate to `c` under some plain field automorphism iff
  `F ≅ R`, and then already within `𝒢`.
- **Exactly `2^𝔠` types (Theorem 16.4; Lemma 25.1, Theorem 25.2).** Subfields
  `F_Y` of `R` algebraic over `Q(B₀ ∪ Y)` give `2^𝔠` coefficientwise
  involutions with pairwise nonisomorphic fixed fields and integer-part fixed
  rings, pairwise nonconjugate under all plain field automorphisms;
  `|Aut(C)| ≤ 2^𝔠` gives the upper bound; `2^𝔠` types are nonstandard.
- **Examples and boundaries (Sections 26, 27).** Phase characters
  (`𝓗_j(t^γ) = χ(γ/2) t^γ`; [merge] for `j_θ = P_{2θ}c` the norm conjugator
  is exactly `P_θ`); a nonlinear two-scale involution on
  `C((u^Q))((z^Q))` whose norm conjugator differs from the conjugator used to
  build it; `t ↦ −t` on `k((t))` (divisibility needed); `t ↦ t + t²` on
  `k(t)` (fullness needed); discreteness does not give floors; wild
  coefficient actions.
- **Questions (Section 29).** Question 29.1 (strongness of finite Gaussian
  symmetries) is **answered** yes by `opa:as:thm:gaussian` (status note). The
  source's second question (does every automorphism of `Oz[i]` preserve the
  valuation?) is `opa:as:q:gaussian` of the omnific-preserving report and is
  printed as a paragraph, not as a new question; open. Questions 29.2–29.9
  (non-full and bounded-support fields, partial divisibility, infinite
  groups, added exponential/derivation/simplicity structure, non-Archimedean
  plain fixed fields, definability of the standard real form, effective
  inversion, formal verification) are open; Question 29.8 (effective
  inversion) is **partly addressed** by source 03 (status note).

### Source 03 (Sections 31–40)

Source 03 re-derives Theorems 16.1–16.4 independently (its pin has source
02's placement but not its text). Those results are printed once, in source
02's sections; the statement map (Section 31.2) credits each of source 03's
numbered statements. Notation: `k` is an **arbitrary** field in Sections 32–33.

- **Formal inversion (Theorem 32.4, imported; Corollary 32.5).** A strongly
  `k`-linear `𝒯` with `supp 𝒯(t^γ) > γ` has `(id + 𝒯)⁻¹ = Σ (−𝒯)^r`, strongly
  linear (Bagayoko–Krapp–Kuhlmann–Panazzolo–Serra, Theorem 3.11 and
  Proposition 1.45, imported, with a set-sized localization for `Γ = No`); so
  `D_χ(id + 𝒯)` is bijective with strong inverse and preserves `𝓘` both ways
  if `𝒯` does. Remark 32.6 [merge]: this supplies the inverse half of the
  obstacle noted in Section 5.3.
- **Orbit-product descent in any characteristic (Theorem 33.1, Corollaries
  33.3, 33.5).** For a finite group of order `n` acting on `k((t^Γ))`, `Γ`
  `n`-divisible, by valued, **strong** automorphisms stabilizing `k` (not
  necessarily `𝓘`), the norm conjugator `𝓗` is a strong value-fixing
  automorphism with the explicit strong inverse
  `𝓗⁻¹ = (Σ_r (−𝒯)^r) D_{χ_𝓗}⁻¹`, `𝒯 = D_{χ_𝓗}⁻¹𝓗 − id` (33.2), and
  `g𝓗 = 𝓗M_{g|_k}`; it preserves `𝓘` and every `A_𝔬` if `G` does.
  Consequently a finite-order valued strongly `k`-linear automorphism is the
  identity when `Γ` is divisible by its order. Remark 33.2 [merge] compares
  the two routes (maximality and the pairing test versus formal inversion)
  and records that source 02's proof uses no characteristic zero either.
- **Gaussian involutions (Proposition 34.1; (34.2)–(34.4)).** The leading
  character `χ_j(γ) = lc j(t^γ)` satisfies `χ_j ρ(χ_j) = 1`, and the
  normalizer's is `χ_{𝓗_j}(γ) = χ_j(γ/2)`, a coherent Hilbert-90 solution;
  explicit inverse `𝓗_j⁻¹ = (Σ (−𝒯_j)^r) D_{χ_{𝓗_j}}⁻¹`, all iterates
  preserving `𝓘`; `H¹(C₂, 𝓝)` trivial as a cocycle identity.
- **Classification route (Section 35).** Conjugacy under `C`-fixing elements
  of `𝒢` iff equal restriction to `C` (Corollary 35.2); a direct proof that
  `Fix(j)` is real closed and the Gaussian splitting
  `Oz[i] = Oz[i]^j ⊕ i·Oz[i]^j` (Proposition 35.3); the integer-part
  criterion in three forms, with the floor transported to `Oz[i]^j`
  (Corollary 35.4).
- **Counting and the standard form (Section 36).** Realized rational cuts
  `Cut_Q(No_F) = F` for Archimedean `F ⊆ R` (Remark 36.1); Corollary 36.2:
  for `j ∈ 𝒢`, conjugacy to `c` in `𝒢` ⇔ `F ≅ R` ⇔ `Oz[i]^j ≅ Oz` ⇔ the pair
  is `(No, Oz)` ⇔ `Fix(j) ≅ No` (the last [merge], from Theorem 24.4; the
  source needs the integer-part hypothesis), and under the integer-part
  hypothesis ⇔ every real rational cut is realized (the hypothesis cannot be
  dropped there: [merge] example with `F` the real closure of `R(X)`).
- **Finite arithmetic (Propositions 37.1, 37.2).** For every real closed `F`:
  `nR_F = nZ ⊕ 𝓘_F`, `R_F/nR_F ≅ Z/nZ`, every unital map to a finite ring
  factors through `ct`, and a system of equations over `Z` is solvable in
  `R_F` iff in `Z`. So the `2^𝔠` pairwise nonisomorphic integer-part fixed
  rings share finite quotients and integer equation solvability (not
  elementary equivalence; disequations not covered). For `F = R` these are
  `odg:thm:finitequotients`, `odg:thm:transfer`; the factorization is a case
  of `osq:thm:universal`(ii).
- **Example (Proposition 38.1).** On `C((t^{Q⊕_lex Q}))`, `j = T_i c` with the
  flows `T_s(z^a u^b) = z^a u^b exp(sau)` (those of Theorem 5.2) is a valued
  `Z[i] + 𝓘`-preserving involution moving the real-coefficient field, with
  normalizer `T_{i/2}`; [merge] it belongs to the same family as source 02's
  example (26.2).
- **Questions (Section 39).** Merged into existing questions: its Questions
  1–2 (`opa:as:q:gaussian` with the involution clause), 4
  (Question 29.3), 5 (`opa:as:q:otherrings`), 10 (Question 29.5), 12
  (Question 29.9); open. Question 39.4 (which `F((t^No))` are `≅ No`,
  non-Archimedean `F`) is **answered** (never), by Theorem 24.4. New and open:
  39.1 (nonvalued `Oz[i]`-preserving real forms; more than `2^𝔠`?), 39.2
  (positive characteristic), 39.3 (elementary equivalence of the `R_F`), 39.5
  (effective normalizers with certified support bounds), 39.6 (Hermitian and
  norm descent).

## Source 02: the merge record

| Manuscript | Pin | Contributes |
|---|---|---|
| batch 32, no. 02, `surreal_finite_symmetry_descent`, 27 pp. | `343dc2c` | Sections 16–30, Appendix C.3; the finite verifier and its record |

**Placement.** The source's Sections 1–14 are Sections 16–29; its Section 15
and Appendices A–B are Section 30. They follow Section 15 (source 01's audit
and conclusions) and precede the appendices, so no number of source 01
changes. An unnumbered heading "Addition: finite symmetry descent
(source 02)" opens them. Numbering map: Theorems 1.1–1.4 → 16.1–16.4;
Definition 2.1 → 17.1; Lemma 3.1, Theorem 3.2, Corollary 3.3, Remark 3.4 →
18.1–18.4; Lemmas 4.1–4.3 → 19.1–19.3; Lemmas 5.1–5.3, Corollary 5.4 →
20.1–20.4; Corollaries 6.1, 6.2 → 21.1, 21.2; Proposition 7.1, Remark 7.2,
Corollary 7.3 → 22.1, 22.2, 22.4; Propositions 8.1, 8.2, Corollary 8.3 →
23.1–23.3; Definition 9.1, Lemma 9.2, Theorems 9.3, 9.4, Corollary 9.5,
Proposition 9.6 → 24.1–24.6; Lemma 10.1, Theorem 10.2, Remark 10.3 →
25.1–25.3; Example 12.1 → 27.1; Question 14.1 → 29.1; Question 14.2 → the
paragraph after it; Questions 14.3–14.10 → 29.2–29.9. Proposition 18.5 and
Remark 22.3 are merge additions.

**Renamed symbols** (table in Section 16.1; no normalization changed). `τ`,
`τ_g = g|_k` → `ρ`, `ρ_g`; `τ̂` → `M_ρ`; the induced map `u` on `Γ` → `τ`;
the involution `σ` → `j`; `H`, `H_σ`, `H_a` → `𝓗`, `𝓗_j`, `𝓗_α`; `𝒢` now
defined without "strong"; `A = Oz[i]` written out; `B = k + 𝓘` → `A_k`; the
subring `D`, `A_D` → `𝔬`, `A_𝔬`; the closed ball `B(a,r)` → `𝔹(a,r)`;
`L_F` → `No_F`; cut sets `L, U` → `𝓛, 𝓡`; `E` → `F'`; `E/F` and `E_N` →
`K₁/K₀`, `Z_N`; `T, T₀, T₁` → `B, B₀, B₁`; `U, F_U, ψ_U, c_U, τ_U, σ_U` →
`Y, F_Y, ψ_Y, c_Y, ρ_Y, j_Y`; the conjugator `U` written out; the finite group
`P` and its actions `a, b` → `Θ`, `α, α'`; the cocycle `u_p` → `ξ_p`; the
conjugator `ρ` in `Aut(C)` → `κ`; the linear forms `ℓ_j` → `f_j`; the set `P`
of positive elements above `N` → `F_∞`; the character `a_γ` → `χ(γ)`; the
example automorphism `P` and field `K₂` → `Ψ`, `K_lex`; the element `c` in
the immediacy proof → `w`. Reasons: `τ` is always a value-group automorphism
here, `σ` an automorphism of `No`, `L` the logarithmic modulus, `D` the
displacement, `E` an exponential, `U` the leading-term kernel, `P_θ` and `𝒫`
the phase twists and Puiseux field, `ℓ` the exponent coefficient, `c` the
conjugation, and `B(a,r)` the open fine ball. Tempting false readings are
printed beside the true ones in Section 16.1 (`No_F` is not `No` unless
`F ≅ R`; `R_F` is discretely ordered but an integer part only for
Archimedean `F`; `F((t^{No<0}))` is not a Hahn field; `F = C^ρ` need not be
`R`; `F_j` of Section 10 is the class fixed field, `F` the set coefficient
field; `ct` is not multiplicative on `K`; value-fixing is not
leading-term-fixing).

**Printed once, with credit.** The pairing criterion and its corollary
(`opa:as:thm:detect`, `opa:as:thm:ctiso`; the source's Baire proof kept as a
fourth route, for the weaker all-`y` form); the reconstruction
(`opa:lem:divisible`, `odg:def:thm:multiplier`, `odg:thm:fractions`, as the
source says); Corollary 23.3 (contained in Theorem 10.1, `saut:thm:torsion`;
the source's route kept); the identification `No[i] = C((t^No))`
(`saut:eq:hahn`); the definition of strong maps (Section 3, restated for
general `k`, `Γ`).

**Stale in the source, corrected in place.** The source's pin predates the
omnific-preserving report's automatic-strongness part (added in parallel, in
`20c4c9f`, not an ancestor of the pin). Its strongness hypotheses (Theorem
16.1, Corollaries 21.1–21.2, the class `𝒢`) are redundant; its first question
is answered; its second is `opa:as:q:gaussian`; the second half of Remark 22.2
("nor strongness") is stale. Each correction is marked `[merge]`, with the
source's statement kept beside it.

**Merge additions** (all marked `[merge]`): Proposition 18.5, Remark 22.3, the
consequences after Proposition 23.1 (`j_θ ∈ 𝒢`; the countable-cofinality real
form of Theorem 10.2 is not conjugate to any member of `𝒢`; the
forcing-sensitive involutions of surreal-fields-across-universes that agree
with `c` on `C` are not both valued and `Oz[i]`-preserving, nor are those of
first-kappa-coefficients), the consistency of Corollary 24.5 with Proposition
B.1, `𝓗_{j_θ} = P_θ`, the assertion count of Section 26.3, Section 28.4, the
status notes, and non-claims 23–27 of Section 30.4. In source 01's text:
pointers or status notes in the front matter, Sections 1.5, 10.1, 14, 15.3
and Appendix C.1; no mathematical statement of source 01 changed.

**Verification.** The source's proofs were read against its statements for this
merge (no gap found; this is not a refereeing). The suite was rerun (below).

## Source 03: the merge record

| Manuscript | Pin | Contributes |
|---|---|---|
| batch 34, no. 03, `gaussian_omnific_real_forms`, 24 pp. | `110efe9` | Sections 31–40, Appendix C.4; the verification program and its record |

**Placement.** Sections 31–40 follow Section 30 (source 02's closing) and
precede the appendices, under an unnumbered heading "Addition: Gaussian-omnific
real forms (source 03)"; no number of sources 01 and 02 changes. Source 03's
Section 1 → Section 31; Sections 2–4 → 32; 5 → 33; 6 → 34; 7–8 → 35; 9–10 →
36; 11 → 37; 12 → 38; 13 → 39; 14 and Appendices A–B → 40. Numbering map of
what is printed here: Lemma 3.1 → Remark 32.1 (route); Lemma 3.2 → second
route in Section 32.2; Proposition 3.3 → 32.2; Remark 3.5 → 32.3; Theorem 4.1,
Corollary 4.2 → 32.4, 32.5; Theorem 5.1, Corollary 5.2, Remark 5.3,
Corollary 5.4 → 33.1, 33.3, 33.4, 33.5; (6.1)–(6.4) → Proposition 34.1,
(34.1)–(34.3); the cocycle → (34.4); Remark 7.2 → 35.1; Corollary 7.4 → 35.2;
Theorem 8.1 → Proposition 35.3 (with (16.2)); Theorem 8.4 → Corollary 35.4;
Remark 8.5 → 35.5; Proposition 9.4 → Remark 36.1; Theorem 10.1, Remark 10.2 →
Corollary 36.2, Remark 36.3; Propositions 11.1, 11.2 → 37.1, 37.2; Proposition
12.1 → 38.1; Questions 3, 6, 7, 8, 9, 11 → 39.1–39.6. Everything else is
mapped to source 02's labels in the table of Section 31.2 (Theorems 1.1, 1.2,
3.4, 6.1, 7.3, 9.3, Lemmas 7.1, 8.3, 9.1, 9.2, Definition 8.2, Corollaries 6.2,
8.7, 9.5, Propositions 8.6, 9.6). Remarks 32.6, 33.2 are merge additions.

**Renamed symbols** (table in Section 31.1; no normalization changed).
`No(i)`, `K` → `𝕂`; `Og`, `J` → `Oz[i]`; `P`, `P_k` → `𝓘`, `𝓘_k`; `o`,
`R_o` → `𝔬`, `A_𝔬`; `⟨x,y⟩₀` → `ct(xy)`; the isomorphism `F`, `α`, `l` of
Proposition 3.3 → `φ`, `ρ`, `k'`; `α = j|_C`, `α_g` → `ρ`, `ρ_g`; `α̂` → `M_ρ`;
the conjugator `β ∈ Aut(C)` → `κ`; `H_G`, `H_j` → `𝓗`, `𝓗_j`; `h_G(γ)` →
`m_γ`; `m = |G|` → `n`; the leading characters `b`, `b_j` and `M_b` →
`χ_𝓗`, `χ_{𝓗_j}`, `D_{χ_𝓗}`; the remainder `T`, `T_j` → `𝒯`, `𝒯_j`; the
exponent sets `S_n`, `Ω` → `Ω_r`, `Ω`; `N` → `𝓝`; the cocycle `u` → `ξ`;
`E`, `F_E`, `P_E`, `I_E` → `F`, `No_F`, `𝓘_F`, `R_F`; `E₁, E₂`, `φ` → `F, F'`,
`ψ`; `A ⊆ B₁`, `E_A`, `φ_A`, `α_A`, `j_A` → `Y`, `F_Y`, `ψ_Y`, `ρ_Y`, `j_Y`;
the bound `β` → `δ`; the cut set `𝒟(F_E)` → `Cut_Q(No_F)`; the rationals
`q, s` → `q, q'`; `e₀, e₁`, `x`, `s` → `(1,0)`, `(0,1)`, `z`, `u`; the
derivation `D` → `𝒟`; the flows `U_λ` and parameters `λ, μ` → `T_s` and
`s, r`. Reasons: this report's `P_θ`/`𝒫` (phase twists, Puiseux field), `T`
(a transcendental) and `T_s` (flows), `S_a` (dilations), `U` (leading-term
kernel), `D` (displacement), `E` (exponential), `ℓ` (exponent coefficient),
`J` (an index set), and source 02's names. Tempting false readings are printed
in Section 31.1 (characteristic-free descent is not a characteristic-free
Gaussian application; `𝒯` is neither `T` nor `T_s`; `χ_j ≠ χ_{𝓗_j}`;
Archimedean is not `≅ R`; equal finite quotients are not elementary
equivalence; `Cut_Q` is external; `H¹` is shorthand).

**Printed once, with credit.** The whole classification package (the map of
Section 31.2): normalization formula, conjugacy classification, fixed pair,
integer-part criterion and floor, reconstruction, `2^𝔠` count, absolute
nonconjugacy, no set-sized cofinal subset — all source 02's. Its Section 3
(reconstruction, detection, covariance, automatic strongness) is
`opa:lem:divisible`, `odg:def:thm:multiplier`, `opa:as:thm:detect`,
`opa:as:thm:ctiso`, `opa:as:thm:gaussian`, as the source says. Second routes
kept: the binary-witness proof of the pairing test, the multiplier step for
every `Γ ≠ 0`, the direct real-closedness proof, and formal inversion in
place of maximality.

**Stale in the source.** Its Appendix B says the inspected snapshot does "not
supply the orbit-product normalizer … with its arithmetic inverse, the
resulting classification … or the integer-part and cardinality package". At
the pin this report's `article.tex` and README were source 01 only (as the
source says; its `SOURCES.md` lists only those two files of this directory),
but source 02's staged audit, placed in `7d04483` (an ancestor of the pin),
already named the norm section `m_gamma = product_g g(t^(gamma/n))` (its line
78) and the classification and count; source 02's text was written in
`b8bbfee`, after the pin. The claim is printed as the source's with this
correction (Section 40.1), not as current. Its question on abstractly surreal
fixed fields was already answered (Theorem 24.4), and its plain-field clause is
weaker than Theorem 24.4 (Corollary 36.2, Remark 36.3).

**Merge additions** (marked `[merge]`): the statement map and conventions
table, Remarks 32.6 and 33.2, the notes after Corollary 33.3, Proposition 34.1,
Proposition 35.3 and Proposition 37.2, clause (v) and the example in the proof
of Corollary 36.2, the status notes of Section 39, the assertion count of
Section 38.1, Section 40.2 and non-claims 26–31. In the earlier text: the title
page and abstract, Sections 1.5 and 5.3, the note after Theorem 16.1,
Questions 29.3, 29.5, 29.8 (status: partly addressed) and 29.9, the pointer in
Section 15.3, and Appendix C.1; no mathematical statement of sources 01 and 02
changed. Bibliography: the two Stacks Project entries are new; the
Bagayoko–Krapp–Kuhlmann–Panazzolo–Serra entry (`BKKS`) gained a note.

**Verification.** The source's proofs were read against its statements for this
merge; the proof of Theorem 24.4 (the omitted cut `N < F_∞`) was rechecked
because it answers source 03's Question 8. No gap found; this is not a
refereeing. The imported formal-inversion theorem was not rechecked. The suite
was rerun (below).

## What the report does not claim

Section 15.3 keeps source 01's non-claims in place and collects them in a
ledger of 33 items: 28 from the source and 5 added when the report joined the
collection. Section 30.4 collects source 02's 27: 22 from the source and 5
added in the merge. Section 40.5 collects source 03's 31: 25 from the source
and 6 added in the merge. In brief:

- Not refereed; no new Lean code and no `saut:` or `saut:fs:` implementation
  mappings. Existing generic proofs cover ordered displacement, exponential
  rigidity, logarithmic-modulus classification and the valuation kernel, as
  detailed below. Neither source built the repository. No complete
  classification of `Aut(K)`; priority not certified for either source; no
  exhaustive nonduplication claim; searches focused, not exhaustive.
- The exponential results of Section 11 and the answer to KKS Question 5.4
  are prior work of the rigidity report, not results of this one.
  Faithfulness is not triviality.
- The four-layer decomposition covers `G_v` only, not `Aut(K)`. Continuity is
  an inclusion, not a classification. The non-strong witness is not claimed
  value- or leading-term-fixing, and non-density is only for the
  pointwise-equality topology.
- `S_2` is not a locally convergent power series; zero derivative does not
  imply local constancy; the Berarducci–Mantova derivation, formal
  differentiation and the fine derivative are three notions.
- Back-and-forth results and `Φ_d` are not algorithms; the transcendence-basis
  slogan is not a classification; real forms and the conjugacy criterion are
  not classified or decided effectively (source 02 classifies only the
  valued, `Oz[i]`-preserving ones).
- The finite symbolic checks mentioned in source 01's delivered README were not
  delivered; nothing here rests on them, and they would prove no infinite
  statement.
- Added for source 01: the Q5.4 reading rests on the rigidity report's check
  of the pinned KKS v3; the source's readings of KKS Examples 4.3–4.4 and
  Questions 5.6–5.7 were not rechecked; nontriviality of `Aut_exp(No)` and
  exponentiality of `S_a|No` for non-rational `a` are not decided; relations
  in Section 1.5 transfer no theorem between topologies or derivative notions.
- Source 02: no proof that an arbitrary automorphism of `Oz[i]` preserves the
  valuation (open, `opa:as:q:gaussian`) — the summation half is settled for
  valued ones by the collection, not by source 02; no classification of all
  real forms of plain `No[i]`, and the `2^𝔠` upper bound is for `𝒢` only;
  nothing on exponentials, derivations or simplicity; no infinite or
  profinite groups and no `H¹` for infinite groups; the outer valuation equals
  the natural one only for Archimedean `F`; Artin–Schreier is used only in
  `C`; the reconstruction and the pairing criterion carry no novelty claim;
  divisibility is sufficient, not shown necessary per action; the norm
  conjugator is not unique; the repository comparison was selective (a
  connector, some truncated responses, no local clone); the questions are
  proposed, not published problems.
- Source 02's verifier checks exact identities in `Q(i)[u]/(u^12)` for the
  worked example only; it does not verify Hahn summability, the Baire lemma,
  maximality, class arguments or cardinalities. Of its 3,751 assertions,
  3,047 are order comparisons of exponent pairs (family
  `negative_support_finite_window`); the identity checks number 704.
- Added in the merge: the automatic-strongness results and the answer to
  Question 29.1 are the collection's, not source 02's; the consequences for
  `odg:def:q:realform`, `univ:q:compatible`, `opa:as:q:otherrings` and
  first-kappa-coefficients are negative or partial information, answering
  none of them; source 02's citations of Kuhlmann–Serra Definition 4.0.5,
  Poonen and Conrad were not rechecked.
- Source 03: unrefereed; novelty and priority not certified (targeted
  searches); classical facts (real closed coefficient fields, Galois descent,
  Hilbert 90 for characters, constant-term retractions) not claimed new, and
  the finite-quotient and equation results are not a new retraction theorem;
  the collection's reconstruction and automatic strongness are reproduced
  with attribution. Valuation preservation is **assumed**; automatic valuation
  preservation for automorphisms (or involutions) of `Oz[i]` is unresolved;
  the classification is complete only in the valued Gaussian sector. The
  normalizer is canonical only relative to the monomial section; no finite
  list of parameters classifies the coefficient fields; "geometric" means no
  analytic limit and no surcomplex exponential. The formal-inversion theorem
  (BKKPS Theorem 3.11 / Proposition 1.45) is **imported**; strongness is not
  inferred from continuity. Archimedean does not mean `≅ R`;
  `Frac(R_F) = No_F` uses the class bound on `No` and is not claimed for
  set-sized support rings; the `2^𝔠` upper bound holds only in the valued
  Gaussian sector (none for pure-field involutions); equal finite quotients
  and `Z`-equation solvability do not imply elementary equivalence, and
  disequations, order constraints and nonordinary coefficients are not
  covered; the rational-cut invariant is not claimed first-order definable;
  `H¹` is a reading, not a claim to originate nonabelian descent; phase shears
  are not new; the finite checks do not test summability, class
  constructions, transcendence bases, cardinalities or all automorphisms; no
  Lean, repository not built or modified; questions are proposed, and no
  published problem (none of Kaplan–Krapp–Serra's) is claimed solved.
- Added in the merge for source 03: its "not supplied" statement is stale
  (source 02 already had the results); the BKKPS, Conrad and Stacks citations,
  including the characteristic-free reading and the class localization, were
  not rechecked; the route comparison, the kernel remark, clause (v) of
  Corollary 36.2, the rational-cut counterexample and the credits to
  `osq`/`odg`/`dsn` are the merge's; 166 of the 457 assertions hold by
  lexicographic order, the orbit-product formula is compared on nine
  monomials only, and the inverse only where the remainder is nilpotent; no
  `saut:gr:` label has a Lean mapping.

## Relation to the neighbouring reports

**[exponential-automorphism-rigidity](../../surreal/exponential-automorphism-rigidity/)**
studies *exponential* automorphisms of an ordered exponential field and, in its
Section 9, `L`-automorphisms of `F(i)`; this report studies *plain* field
automorphisms of `No(i)`. Section 11 here reprints: Lemma 11.1 = its
`lem:amplify` (3.1); Theorem 11.2 = its faithfulness `thm:cofinal`/`cor:faithful`
(4.1/4.2) via `lem:bridge`, `lem:bounded`, `prop:finite-log`; (11.2) and the
sentence after it = its `eq:main-no`, `thm:no`, `cor:question54` (5.1/5.2, the
answer to KKS Question 5.4, arXiv v3); Proposition 11.3 = its `thm:dilation`
(8.4), second proof, any positive infinite `X` for `ω`; Theorem 11.4 = its
`thm:L-classification` with `lem:range`, `thm:complex-kernel`, `cor:surcomplex`
(9.1, 9.2, 9.4, 9.5) for `F = No`. Theorem 2.2 is the field-level, exponential-free
counterpart of its classification. `S_q|No` is its canonical lift `T̂_q`
(`prop:hahn-lift`), and `ℓ(g) = [g]_0` its layer coefficient. The report's
image question is its Question 13.1.

**[omnific-preserving-automorphisms](../../surreal/omnific-preserving-automorphisms/)**
(source 02). Its summation detection and automatic strongness
(`opa:as:thm:detect`, `opa:as:thm:ctiso`, `opa:as:thm:gaussian`) postdate
source 02's pin: they are the pairing criterion printed in Section 18, make
source 02's strongness hypotheses redundant, and answer its first question.
Source 02's second question is its `opa:as:q:gaussian`. The reconstruction
uses its `opa:lem:divisible`. For `k` of characteristic 0 and `𝔬 = Z, Z[i]`,
Remark 22.3 is partial information on its `opa:as:q:otherrings` (valued maps
only). Its statement that no nonconjugacy is claimed for `Oz[i]`-preserving
maps that do not preserve conjugation concerns its copies of `No`
(`opa:as:cor:complexcopies`); for involutions, Theorem 25.2 gives `2^𝔠`
members of `𝒢` pairwise nonconjugate under all field automorphisms. That
report is not edited here. Source 03 (batch 34) reproves `opa:as:thm:detect`
(binary-witness route), `opa:as:thm:ctiso` and `opa:as:thm:gaussian` with
credit, asks `opa:as:q:gaussian` again with an involution-only clause and a
nonvalued counting variant (Question 39.1), and asks `opa:as:q:otherrings`
again (the intersection `∩ n𝔬` must vanish); both stay open.

**[omnific-diophantine-geometry](../../surreal/omnific-diophantine-geometry/)**
— the reconstruction uses `odg:def:thm:multiplier` and `odg:thm:fractions`;
its phase twist `odg:def:lem:twist` is a case of Section 26.1. Source 02 gives
negative information, not an answer, for `odg:def:q:realform`: requiring an
involution to preserve the valuation, summation and `Oz[i]` leaves `2^𝔠`
pairwise nonisomorphic fixed rings. Source 03 adds that these rings share all
finite quotients and integer-equation solvability (Propositions 37.1, 37.2),
extending its `odg:thm:finitequotients` and `odg:thm:transfer` from `Oz` to
every `R_F`.

**[set-sized-quotients-of-omnific-integers](../../surreal/set-sized-quotients-of-omnific-integers/)**,
**[definable-surreals-and-omnific-integers](../../foundations-and-computation/definable-surreals-and-omnific-integers/)**
— the factorization clause of Proposition 37.1 is the finite-target case of
`osq:thm:universal`(ii) with the set field `F` and the subring `Z`;
`dsn:thm:finite-quotients` is the same statement for the definable rings
`I_A`. Neither report is edited.

**[foundations](../../foundations-and-computation/foundations/)** —
`found:prop:complex` (the pair field, algebraic closedness); Proposition 7.2 is
`found:thm:discrete` (Lean-proved for the surcomplex carrier, with
lower-universe smallness, per `FORMALIZATION.md`); the derivative is
`found:eq:derivative`. The collection's earlier zero-derivative witnesses
(`found:rem:fourtypes`, **[analysis](../analysis/)** `b:L`) are locally
constant; `S_2` is injective, hence constant on no nontrivial open set.

**Character twists.** `D_χ = M_{id,id,χ}` generalizes the diagonal twists of
[spectral-theory](../spectral-theory/) (`spec:lem:finiteindex`),
[hidden-negative-hermitian-directions](../hidden-negative-hermitian-directions/)
(`hnd:lem:supportdegree`) and
[transcendence-over-bounded-support](../../surreal/transcendence-over-bounded-support/)
(`bst:lem:characters`) from set-sized groups to `Γ = No`.

**[trigonometry](../trigonometry/)** — the Cayley map of Theorem 2.4 is a
reparametrization of `trigonometry:thm:cayley`. Rotations there and in
[euclidean-three-space](../../surreal/euclidean-three-space/) (same batch) are
`No`-linear isometries, not field automorphisms; by Theorem 2.3 the only field
automorphisms preserving every modulus are `id` and `c`.

**Lean.** `Surreal/Surcomplex/Basic.lean` (`conj` as a ring automorphism) and
`Surreal/HahnSeries/ComplexNumbers.lean` (`coefficientEquiv`, the case
`M_{ρ,id,1}` in a workspace) are interfaces; `Surreal/Algebra/SigmaDerivation.lean`
proves valued-field forms of the rigidity report's displacement results, while
the ordered displacement lemma is now proved by `displacement_cofinal` in
`Surreal/Algebra/ExponentialProfile.lean`. That module's `eq_id_of_commute`
also proves the generic value-fixing exponential rigidity implication.
`Surreal/Algebra/LogModulusClassification.lean` now proves the generic
logarithmic-modulus classification, including the direct-product group
isomorphism `autLEquiv`. `Surreal/Algebra/ComplexValuationKernel.lean`
proves the generic valuation-kernel theorem. Both use an ordered field
with nonnegative square roots and an injective `OrderedExp`; injectivity
is an explicit hypothesis, omitted from the structure itself. The kernel
theorem additionally uses a nontrivial convex valuation. That module
defines its own `log`, `L` and `IsLAut`, without a formal bridge to the
classification module, and represents the coarsened action relationally.
These existing mappings use the rigidity report's labels; this review adds
no dedicated `saut:` mapping. The actual surreal exponential instantiation,
rational non-lifting and the actual surcomplex logarithmic-modulus
classification remain pending. Source 02's formalization interface
(Section 30.3) is a plan; nothing of it is implemented. Source 03 supplies
no Lean either, and no `saut:gr:` label has an implementation mapping.

"Rigidity" here (Theorems 2.3, 11.2; Section 11.1) is not `f:thm-rigidity` of
analysis nor the scalar rigidity of gamma-functions; "phase" is a coefficient
multiplier, not an argument or the trigonometry/differential-equations phase;
"real form" is a real closed `F` with `K = F(i)`, not the real-coefficient
versions in entire-functions or analytic-geometry. A strong automorphism
is determined by its action on both coefficients and monomials; monomial
images alone suffice for strongly `C`-linear maps. The strong Taylor motions
fix every monomial while moving coefficients, so strongness alone cannot
remove the coefficient data.

Two later reports use conjugation on `No[i]`.
[surreal-fields-across-universes](../../foundations-and-computation/surreal-fields-across-universes/)
continues, but does not settle, the real-form question of Section 14: under
global choice it transports an inner model's conjugation to real forms of
`No[i]` that have no set-sized cofinal subset and are not conjugate to `c`
(by the easy direction of `saut:prop:conjugacycriterion`), separates several
such forms by an external gap invariant, and lets them agree with `c` on `C`.
By Proposition 23.1, those that agree with `c` on `C` are not both valued and
`Oz[i]`-preserving; its `univ:q:compatible` is related to source 02 and not
answered.
[birthday-cutoffs-and-hereditary-sets](../../foundations-and-computation/birthday-cutoffs-and-hereditary-sets/)
enriches bounded surcomplex fields by conjugation and a coordinate birthday;
its bounded `Aut = {id, c}` statements are credited to `saut:thm:axis` and the
simplicity rigidity of `saut:sec:exponential`, and only its two-lift
classification of elementary embeddings and, under GBC, its elementary
self-embeddings of the full structure are new there. Neither addresses
`Aut_L`.

[first-kappa-coefficients](../first-kappa-coefficients/) receives in batch 32
a proper-class family of pure-field involutions agreeing with `c` on `C`, none
conjugate to `c` (`fkc:sb:thm:involutions`); by Proposition 23.1 none lies in
`𝒢`. The two are complementary. A note after Proposition B.1
(`saut:prop:conjugacycriterion`) records that the non-conjugacy to `c` also
follows from that criterion (`fkc:sb:rem:univ`). Source 03's Question 39.3
(elementary equivalence of the rings `R_F`) is a companion of that report's
`fkc:sb:q:omnific` (elementary equivalence of the short omnific rings). The large-cardinal report
([large-cardinal-embeddings-and-normal-forms](../../foundations-and-computation/large-cardinal-embeddings-and-normal-forms/))
is a different direction: source 02's class argument uses no large cardinal.

[single-dilation-hahn-support](../single-dilation-hahn-support/) computes the
centralizer of a rational dilation `S_q` (`q ≠ 1`) among all field automorphisms
(`dsup:thm:centralizer`): it consists of untwisted coefficient–exponent lifts,
consistent with `saut:thm:decomp`, and naming `S_q` makes the coefficient field
and every coefficient definable, complementing `saut:prop:nondefinability`. It
answers none of the questions of Section 14. The trigonometry report's shifts
`Sh_c` (`trigonometry:per:thm:shifts`) are the flows of `saut:thm:shiftflow`,
and act freely on all global phases (`trigonometry:per:thm:free`).

## Stale statements corrected

The source compared itself with the repository at `dcf8666` (Section 13, kept
as provenance); Appendix C.2 records the check. Its descriptions of
`Complexify.lean`, `FineDerivative.lean`, `NORMAL_FORM_BRIDGE.md` and the
rigidity report with its audit correction are accurate, and none of those
files changed between the pin and the placement. The source did not relate its
results to `found:thm:discrete` and its Lean proof, the zero-derivative
witnesses, `spec:lem:finiteindex`, `trigonometry:thm:cayley`, or the Lean
modules above; the hidden-negative-directions and bounded-support reports and
`SigmaDerivation.lean` postdate the pin. Section 1.5 supplies these relations.
The rigidity report's README sentence that no other report proves its theorems
about `Aut(No)` predates this report.

Six symbols were renamed so that each has one meaning: `E_{ρ,τ} → M_{ρ,τ}`,
`E_d → Φ_d` (so `E` never denotes a lift; otherwise it is an exponential,
except as a local name for a set-sized subfield in `Aut(K/E)` and in the
proofs of Proposition 9.3 and Theorem 10.1 — Section 1.4 said "only an
exponential" before batch 32 and was corrected), the derivation `D → 𝒟`, the
Puiseux field `P → 𝒫`, the automorphism `τ → ψ` in Section 7.2, and cut sides
`(L,R) → (𝓛,𝓡)`; `Aut(K,L)` is written `Aut_L(K)`. `Γ = (No,+,<)` is a proper
class here, departing from `NOTATION.md`'s set-sized `Γ`. No mathematical
statement was changed at placement.

Batch 32 (source 02): the "single-source" statements of the title page and
Appendix C.1 were updated; Section 14's real-form paragraph and non-claim 20
received status notes (partly answered, valued `Oz[i]`-preserving case);
Section 10.1 received a pointer. Source 02's own stale statements (its
strongness hypotheses and first question) are corrected in place, as above.
Its comparison with the collection at `343dc2c` (its Section 13.2, printed as
Section 28.2) is accurate for that tree; Section 28.4 adds the relations
checked against the current one.

Batch 34 (source 03): the "two-source" title page, the abstract, Section 1.5
and Appendix C.1 were updated; Question 29.8 (effective inversion) received a
status note (partly addressed: an explicit formula, no complexity bound), and
Questions 29.3, 29.5, 29.9, Section 5.3 (the inverse half of the obstacle
there) and the note after Theorem 16.1 received pointers. Source 03's own
stale statement (that the collection lacked the normalizer and the
classification) and its already-answered question are corrected in place, as
above.

The subsequent main-text review covers Sections 1–15 and the conjugacy
criterion. It makes class-map conventions and set-stage choices explicit,
reduces finite-group assertions to ordinary invariant algebraically closed
subfields, and constructs the real closure through compatible ordered
embeddings. It corrects the rational-cut and monomial-determination
explanations, expands the additive value-group decomposition, and supplies
the finite-observation obstruction for the full `Aut(K)`. The derivative
statement now excludes every `K`-valued derivative, including infinite
values, using explicit neighborhood thresholds. The generic exponential
proof uses the actual valuation image, and current Lean status is separated
from the pinned inspection. See the
[collection review record](../../REVIEW.md#field-automorphism-main-text-review).
Remaining imported-result, source reconciliation and priority checks are
separate from this main-text review. That review predates source 02.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Standard packages (`newtx`, `amsmath`, `mathtools`, `geometry`, `microtype`,
`booktabs`, `longtable`, `enumitem`, `ragged2e`, `tocloft`, `fancyhdr`,
`hyperref`, `cleveref`); no shell escape, no external `.bib`. The build with
the merge of source 03 (MiKTeX 26.2, pdfTeX 1.40.29) has 89 pages (title, contents
i–iii, pages 1–85; 68 before) and no errors, no undefined or multiply-defined
references or citations, no duplicate PDF destinations, no LaTeX warnings and
no overfull or underfull boxes, like the build of the previous text. Its log
contains two informational lines "ignored: Infinite glue shrinkage found in
box being split" at page breaks inside the two new long tables of Section 31;
they are not warnings, and the same longtable message appears with source 02's
table of Section 16.1 when it starts at other page positions (tested). With
source 02 the build had 68 pages; the text before source 02 gives 38 pages
with this MiKTeX (the PDF committed then, 37 pages, was built with pdfTeX
1.40.22). A clean compile proves nothing about the proofs. Source 01
delivered no code or data.

## Rerun source 02's checks

`code/02-finite-symmetry-descent-verify_finite.py` needs Python 3.10 or later
and nothing else. It prints its JSON record to standard output and writes a
file only when given `--output`. The delivered helper
`code/02-finite-symmetry-descent-build.sh` is **not usable as shipped** and
should not be run in place: it changes into its own directory, expects the
delivery layout (`code/verify_finite.py`, `finite_symmetry_descent.tex`, which
is not shipped) and overwrites `data/verification.json`,
`data/verification_console.txt` and the PDF. The audit and the build record
also name the delivery paths (`code/verify_finite.py`,
`data/verification.json`); `data/…-build_validation.json` describes the
delivery's own 27-page PDF (495,744 bytes), which is not shipped. Run the
verifier on a copy, from this directory:

```sh
T=$(mktemp -d)
mkdir -p "$T/code" "$T/data"
cp code/02-finite-symmetry-descent-verify_finite.py "$T/code/verify_finite.py"
(cd "$T" && python3 code/verify_finite.py --order 12 --output data/verification.json \
    > data/verification_console.txt)
diff "$T/data/verification.json" data/02-finite-symmetry-descent-verification.json
diff "$T/data/verification_console.txt" data/02-finite-symmetry-descent-verification_console.txt
```

Rerun for this merge with Python 3.14.4 on Windows: exit code 0, status
`passed`, 3,751 assertions, and both written files identical to the shipped
records after converting line endings (Python's text mode writes CRLF on
Windows; the records are LF). The families are 23 each of the per-exponent
identities (involution, norm-section invariance and square, conjugacy
factors, inverse, constant coefficient), 529 multiplicativity checks, 1 + 1
phase-unit checks, 3 + 9 sparse involution and multiplicativity checks, and
3,047 lexicographic order comparisons. They check finite instances in
`Q(i)[u]/(u^12)` only.

## Rerun source 03's checks

`code/03-gaussian-real-forms-verify.py` needs Python 3.9 or later and nothing
else. It writes its JSON record to the path given by `--output` (default
`verification.json` in the **current directory**) and prints the same JSON to
standard output; options `--order` (default 8) and `--samples` (default 24).
The record includes the Python version, so it differs between interpreters.
The delivered helper `code/03-gaussian-real-forms-build.sh` is **not usable as
shipped**: it changes into `code/`, runs `pdflatex` on an `article.tex` that
is not there (it stops at once under `set -e`), and would then call
`verify.py` under its delivery name and write `verification.json` into
`code/`. The audit `03-gaussian-real-forms-SOURCES.md` and the delivery
README (not shipped) use the delivery names `verify.py`, `verification.json`,
`build.sh`, `article.tex`. Run the program on a copy:

```sh
T=$(mktemp -d)
cp code/03-gaussian-real-forms-verify.py "$T/verify.py"
(cd "$T" && python3 verify.py --output verification.json > console.txt)
diff "$T/verification.json" data/03-gaussian-real-forms-verification.json
```

Rerun for this merge with Python 3.14.4 on Windows: exit code 0, status
`passed`, 457 assertions in the same families and counts as the record; the
written file differs from the shipped record only in the `"python"` field
(`3.14.4` against the delivery's `3.13.5`) and in line endings (Python's
text mode writes CRLF on Windows; the record is LF). The families: 9 each for
the orbit-product formula, the monomial involution and the monomial
intertwining; 24 each for flow composition, flow multiplicativity, involution,
intertwining, normalizer multiplicativity, geometric inverse, nilpotent
remainder, left and right inverse, conjugacy identity and leading value; and
166 `negative_support_preservation` checks, which are lexicographic
comparisons `(a, b + r) < (0, 0)` that hold by the order itself. They check
finite instances in `Q(i)[z^Q][u]/(u^9)` only (the program's own names are
`x` and `s` for `z` and `u`).
