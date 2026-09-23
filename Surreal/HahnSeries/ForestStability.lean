import Surreal.HahnSeries.MarkovResidueShadow

/-!
# Entrywise relative stability of Hahn rate-matrix resolvents

This file proves `markov:thm:stability` of
`docs/surreal/markov-generators-at-every-scale/article.tex` in full, together with the sharpness
example `markov:ex:sharp`, and the shadow-level content of `markov:cor:leading-equivalence`.

**Setting.** `F = Lex R⟦Γ⟧` for any linearly ordered field `R` and any linearly ordered abelian
group `Γ`; the source's `ℝ((t^Γ))`, with `Γ` nonzero and divisible, is the case `R = ℝ`, and
neither divisibility nor nontriviality of `Γ` is used. The valuation is
`v(x) = (ofLex x).orderTop ∈ WithTop Γ`. The rates are a matrix `q : n → n → F` on a finite type
with nonnegative off-diagonal entries, `L = rowLaplacian q` is the row Laplacian
`markov:eq:laplacian` and `R_L(s) = s(sI + L)⁻¹` is `Surreal.Markov.resolvent`. The bound `δ` is
taken in `WithTop Γ`: the source's `δ ∈ Γ` is its coercion, and `δ = ⊤` means exact equality.

**Relative closeness.** `RelClose δ x x'` is `v(x' - x) ≥ δ + v(x)`, the source's
`x' = x(1 + O(δ))`. For `x ≠ 0` it is `v(x'/x - 1) ≥ δ` (`relClose_iff`); for `x = 0` it forces
`x' = 0`. It is preserved by products, finite products and powers when `δ ≥ 0`
(`RelClose.mul`, `RelClose.prod`, `RelClose.pow`), and by quotients with a nonzero denominator
when `δ > 0` (`RelClose.div`). It is preserved by sums of *nonnegative* terms (`RelClose.sum`):
this is the no-cancellation step of the source. For `0 ≤ x ≤ y` one has `v(y) ≤ v(x)`
(`orderTop_le_of_nonneg_of_le`), so each summand's error is `O(δ)` relative to the whole sum.
For `δ > 0` the valuation and the leading coefficient are preserved (`RelClose.orderTop_eq`,
`RelClose.leadingCoeff_eq`).

**`markov:thm:stability`.** By `markov:prop:forest` (`Surreal/Algebra/MarkovForest.lean`),
`R_L(s) = N(s)/D(s)`, where `D(s)` and every `N(s)_ij` are sums of the nonnegative forest terms
`q(f)s^{d-|f|}`. Each forest weight, hence each forest term, is perturbed relatively by `O(δ)`
(`relClose_weight`, `relClose_forestCoeff`, `relClose_forestMatrix`), and so are `D` and every
`N_ij` (`relClose_forestDenom`, `relClose_forestNumer`).
* `relClose_resolvent`: if `q'_ij = q_ij(1 + O(δ))` for `i ≠ j`, `s > 0`, `s' = s(1 + O(δ))`
  and `δ > 0`, then `R_{L'}(s')_ij = R_L(s)_ij(1 + O(δ))` for every entry. Neither strong
  connectivity, nor positivity of `q'`, nor a spectral gap is assumed; zero entries stay zero.
* `stability_core`: if the graph of positive rates of `q` is strongly connected, every entry is
  nonzero and `v(R_{L'}(s')_ij / R_L(s)_ij - 1) ≥ δ`.
* `stability`: the first display `markov:eq:relative-stability`, for `q'_ij = q_ij(1 + η_ij)`
  with `v(η_ij) ≥ δ > 0`; `stability_of_param`: the second clause, with `s' = s(1 + η_s)` and
  `v(η_s) ≥ δ`; `stability_of_graph`: the same with the source's literal hypotheses, a strongly
  connected allowed graph `E`, positive rates on `E`, both rate systems zero off `E`, and
  `q'_e = q_e(1 + η_e)` on `E`.

The bound does not depend on `s`, on a spectral gap or on the valuation of the entry. The proof
is the source's. Forest terms through missing edges are zero, which the no-cancellation step
allows because only nonnegativity is used. `D(s') ≠ 0` and `s' ≠ 0` follow from relative
closeness, so the perturbed resolvent is `N'/D'` by `MarkovForest.resolvent_eq_forest` without
assuming `q' ≥ 0`.

**`markov:ex:sharp`.** `sharpRates η` has two states with `q₁₂ = 1 + η` and `q₂₁ = 1`, so
`sharpRates η` is `sharpRates 0` with only `q₁₂` multiplied by `1 + η` (`sharpRates_eq`).
`resolvent_sharpRates`: `R_L(1)₁₂ = (1 + η)/(3 + η)` whenever `3 + η ≠ 0`. `sharp`: for
`v(η) > 0` the relative error `2η/(3 + η)` of that entry has valuation exactly `v(η)`, so the
exponent in `markov:eq:relative-stability` cannot be increased.

**`markov:cor:leading-equivalence`.** `exists_relClose_of_leading` and
`exists_relClose_of_leading_rates`: finitely many rates with the same valuations and leading
coefficients (hence the same graph) are relatively close with one common `δ > 0` (possibly `⊤`).
`shadowAt_eq`: relatively close data have the same residue shadow `res R_L(s)`. Over `ℝ`,
`leading_equivalence` proves, for nonnegative off-diagonal rates `q` and rates `q'` with the same
edge valuations and edge leading coefficients:
* `res R_{L'}(s) = res R_L(s)` for every positive `s` (all resolvent parameters at once);
* `K_α(c) = res R_L(ct^α)` (`MarkovShadow.shadow`) agrees for every `α` and every real `c > 0`;
* every entry of `R_{L'}(s)` has the valuation and the leading coefficient of the corresponding
  entry of `R_L(s)`, for every `s > 0`, in particular at every scale `s = ct^α`: the leading
  terms of all marked entries.

**Pending.** Nothing of `markov:thm:stability` or `markov:ex:sharp`. For
`markov:cor:leading-equivalence`, only the residue, shadow and marked-entry clauses above are
proved. The plateau projections, crossover kernels and effective generators are determined by the
shadow family `c ↦ K_α(c)` on `c > 0` (limits as `c → ∞` and `c → 0⁺`, and values at positive
`c`; `Surreal/Algebra/PseudoResolventLimits.lean`, `Surreal/Algebra/MarkovEffective.lean`), so
their agreement follows from the equality of the shadows for every `c > 0` in
`leading_equivalence`. That equality is stated only for `c > 0`, so this is a congruence argument
on positive `c`, not a literal rewrite; these derived statements are not stated separately here.
The leading-forest formula of `markov:thm:leading` and the remainder
certificate `markov:prop:remainder` are not addressed, although `orderTop_le_of_nonneg_of_le`
is their common no-cancellation core.
-/

namespace Surreal.ForestStability

open Finset Matrix
open _root_.HahnSeries
open Surreal.MarkovForest (rowLaplacian forestDenom forestNumer forestCoeff forestMatrix weight
  IsInForest)

noncomputable section

section Arith

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]
  {δ : WithTop Γ} {x x' y y' : Lex R⟦Γ⟧}

/-- `RelClose δ x x'` says `x' = x(1 + O(δ))`, in additive form: `v(x' - x) ≥ δ + v(x)`. -/
def RelClose (δ : WithTop Γ) (x x' : Lex R⟦Γ⟧) : Prop :=
  δ + (ofLex x).orderTop ≤ (ofLex (x' - x)).orderTop

/-- The valuation is additive on products. -/
theorem orderTop_ofLex_mul (x y : Lex R⟦Γ⟧) :
    (ofLex (x * y)).orderTop = (ofLex x).orderTop + (ofLex y).orderTop :=
  orderTop_mul (ofLex x) (ofLex y)

omit [IsOrderedAddMonoid Γ] in
/-- Every element is relatively close to itself. -/
theorem RelClose.refl (δ : WithTop Γ) (x : Lex R⟦Γ⟧) : RelClose δ x x := by
  simp [RelClose]

omit [IsOrderedAddMonoid Γ] in
/-- Only `0` is relatively close to `0`. -/
theorem relClose_zero_left_iff : RelClose δ 0 x' ↔ x' = 0 := by
  simp [RelClose]

/-- For `δ ≥ 0`, a relative perturbation does not lower the valuation. -/
theorem RelClose.orderTop_le (hδ : 0 ≤ δ) (h : RelClose δ x x') :
    (ofLex x).orderTop ≤ (ofLex x').orderTop := by
  calc (ofLex x).orderTop ≤ min (ofLex x).orderTop (ofLex (x' - x)).orderTop :=
        le_min le_rfl ((le_add_of_nonneg_left hδ).trans h)
    _ ≤ (ofLex x + ofLex (x' - x)).orderTop := min_orderTop_le_orderTop_add
    _ = (ofLex x').orderTop := by rw [← ofLex_add, add_sub_cancel]

/-- For `δ > 0` and `x ≠ 0`, the error `x' - x` has strictly larger valuation than `x`. -/
theorem RelClose.orderTop_lt (hδ : 0 < δ) (h : RelClose δ x x') (hx : x ≠ 0) :
    (ofLex x).orderTop < (ofLex (x' - x)).orderTop := by
  refine lt_of_lt_of_le ?_ h
  have := WithTop.add_lt_add_right (orderTop_ne_top.mpr hx) hδ
  rwa [zero_add] at this

/-- For `δ > 0`, a relative perturbation keeps the valuation. -/
theorem RelClose.orderTop_eq (hδ : 0 < δ) (h : RelClose δ x x') :
    (ofLex x').orderTop = (ofLex x).orderTop := by
  by_cases hx : x = 0
  · subst hx
    rw [relClose_zero_left_iff.mp h]
  · have := orderTop_add_eq_left (h.orderTop_lt hδ hx)
    rwa [← ofLex_add, add_sub_cancel] at this

/-- For `δ > 0`, a relative perturbation of a nonzero element is nonzero. -/
theorem RelClose.ne_zero (hδ : 0 < δ) (h : RelClose δ x x') (hx : x ≠ 0) : x' ≠ 0 := by
  intro hx'
  have := h.orderTop_eq hδ
  rw [hx', ofLex_zero, orderTop_zero, eq_comm, orderTop_eq_top] at this
  exact hx this

/-- For `δ > 0`, a relative perturbation keeps the leading coefficient. -/
theorem RelClose.leadingCoeff_eq (hδ : 0 < δ) (h : RelClose δ x x') :
    (ofLex x').leadingCoeff = (ofLex x).leadingCoeff := by
  by_cases hx : x = 0
  · subst hx
    rw [relClose_zero_left_iff.mp h]
  · have := leadingCoeff_add_eq_left (h.orderTop_lt hδ hx)
    rwa [← ofLex_add, add_sub_cancel] at this

/-- Relative closeness at `δ` implies it at every smaller `δ'`. -/
theorem RelClose.mono {δ' : WithTop Γ} (hδ : δ' ≤ δ) (h : RelClose δ x x') : RelClose δ' x x' :=
  le_trans (by gcongr) h

/-- `x(1 + ε)` with `v(ε) ≥ δ` is relatively close to `x`. -/
theorem relClose_mul_one_add {ε : Lex R⟦Γ⟧} (hε : δ ≤ (ofLex ε).orderTop) (x : Lex R⟦Γ⟧) :
    RelClose δ x (x * (1 + ε)) := by
  unfold RelClose
  rw [show x * (1 + ε) - x = x * ε by ring, orderTop_ofLex_mul, add_comm]
  gcongr

/-- Products of relative perturbations are relative perturbations (`δ ≥ 0`). -/
theorem RelClose.mul (hδ : 0 ≤ δ) (hx : RelClose δ x x') (hy : RelClose δ y y') :
    RelClose δ (x * y) (x' * y') := by
  have hx' := hx.orderTop_le hδ
  unfold RelClose at *
  rw [show x' * y' - x * y = x' * (y' - y) + (x' - x) * y by ring, ofLex_add,
    orderTop_ofLex_mul x y]
  refine le_trans (le_min ?_ ?_) min_orderTop_le_orderTop_add
  · rw [orderTop_ofLex_mul, add_left_comm]
    gcongr
  · rw [orderTop_ofLex_mul, ← add_assoc]
    gcongr

/-- Finite products of relative perturbations are relative perturbations (`δ ≥ 0`). -/
theorem RelClose.prod {ι : Type*} (S : Finset ι) {f f' : ι → Lex R⟦Γ⟧} (hδ : 0 ≤ δ)
    (h : ∀ i ∈ S, RelClose δ (f i) (f' i)) : RelClose δ (∏ i ∈ S, f i) (∏ i ∈ S, f' i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using RelClose.refl δ (1 : Lex R⟦Γ⟧)
  | @insert i S hi ih =>
    rw [prod_insert hi, prod_insert hi]
    exact (h i (mem_insert_self i S)).mul hδ (ih fun j hj => h j (mem_insert_of_mem hj))

/-- Powers of relative perturbations are relative perturbations (`δ ≥ 0`). -/
theorem RelClose.pow (hδ : 0 ≤ δ) (h : RelClose δ x x') (m : ℕ) : RelClose δ (x ^ m) (x' ^ m) := by
  induction m with
  | zero => simpa using RelClose.refl δ (1 : Lex R⟦Γ⟧)
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul hδ h

/-- Quotients of relative perturbations by a nonzero denominator are relative perturbations
(`δ > 0`): the source's "the inverse of `1 + O(δ)` is again `1 + O(δ)`". -/
theorem RelClose.div (hδ : 0 < δ) {N N' D D' : Lex R⟦Γ⟧} (hN : RelClose δ N N')
    (hD : RelClose δ D D') (hD0 : D ≠ 0) : RelClose δ (N / D) (N' / D') := by
  have hD0' : D' ≠ 0 := hD.ne_zero hδ hD0
  have hvD := hD.orderTop_eq hδ
  have hc : (ofLex D).orderTop + (ofLex D').orderTop ≠ ⊤ := by
    rw [← orderTop_ofLex_mul]
    exact orderTop_ne_top.mpr (mul_ne_zero hD0 hD0')
  have key : (N' / D' - N / D) * (D * D') = (N' - N) * D - (D' - D) * N := by
    field_simp
    ring
  have h1 : (ofLex (N' / D' - N / D)).orderTop + ((ofLex D).orderTop + (ofLex D').orderTop) =
      (ofLex ((N' - N) * D - (D' - D) * N)).orderTop := by
    rw [← orderTop_ofLex_mul D D', ← orderTop_ofLex_mul, key]
  have h2 : (ofLex (N / D)).orderTop + (ofLex D).orderTop = (ofLex N).orderTop := by
    rw [← orderTop_ofLex_mul, div_mul_cancel₀ N hD0]
  unfold RelClose at *
  have h3 : δ + (ofLex N).orderTop + (ofLex D).orderTop ≤
      (ofLex ((N' - N) * D - (D' - D) * N)).orderTop := by
    rw [ofLex_sub]
    refine le_trans (le_min ?_ ?_) min_orderTop_le_orderTop_sub
    · rw [orderTop_ofLex_mul]
      gcongr
    · rw [orderTop_ofLex_mul, add_right_comm]
      gcongr
  refine WithTop.le_of_add_le_add_right hc ?_
  calc δ + (ofLex (N / D)).orderTop + ((ofLex D).orderTop + (ofLex D').orderTop)
        = δ + ((ofLex (N / D)).orderTop + (ofLex D).orderTop) + (ofLex D).orderTop := by
          rw [hvD, add_assoc, add_assoc, add_assoc]
      _ ≤ _ := by rw [h2]; exact h3
      _ = _ := h1.symm

/-- For `x ≠ 0`, `RelClose δ x x'` is the valuation bound `v(x'/x - 1) ≥ δ`. -/
theorem relClose_iff (hx : x ≠ 0) :
    RelClose δ x x' ↔ δ ≤ (ofLex (x' / x - 1)).orderTop := by
  have e : (ofLex (x' / x - 1)).orderTop + (ofLex x).orderTop = (ofLex (x' - x)).orderTop := by
    rw [← orderTop_ofLex_mul, sub_mul, div_mul_cancel₀ x' hx, one_mul]
  unfold RelClose
  rw [← e]
  exact WithTop.add_le_add_iff_right (orderTop_ne_top.mpr hx)

/-- Equal valuations and equal leading coefficients make `x'` relatively close to `x` for some
positive `δ` (`δ = ⊤` when `x' = x`). -/
theorem exists_relClose_of_leading (hv : (ofLex x').orderTop = (ofLex x).orderTop)
    (hlc : (ofLex x').leadingCoeff = (ofLex x).leadingCoeff) :
    ∃ δ : WithTop Γ, 0 < δ ∧ RelClose δ x x' := by
  by_cases hx : x = 0
  · subst hx
    rw [ofLex_zero, orderTop_zero, orderTop_eq_top] at hv
    refine ⟨⊤, WithTop.coe_lt_top 0, ?_⟩
    rw [show x' = 0 from hv]
    exact RelClose.refl ⊤ 0
  · obtain ⟨g, hg⟩ : ∃ g : Γ, (ofLex x).orderTop = g :=
      ⟨_, (WithTop.coe_untop _ (orderTop_ne_top.mpr hx)).symm⟩
    have hne : (ofLex (x' - x)).orderTop ≠ g := by
      rw [ofLex_sub]
      exact orderTop_sub_ne (hv.trans hg) hg hlc
    have hge : (g : WithTop Γ) ≤ (ofLex (x' - x)).orderTop := by
      rw [ofLex_sub, ← hg]
      exact (le_min hv.ge le_rfl).trans min_orderTop_le_orderTop_sub
    have hlt : (g : WithTop Γ) < (ofLex (x' - x)).orderTop := lt_of_le_of_ne hge (Ne.symm hne)
    refine ⟨(ofLex (x' - x)).orderTop + ((-g : Γ) : WithTop Γ), ?_, ?_⟩
    · have := WithTop.add_lt_add_right (WithTop.coe_ne_top (a := -g)) hlt
      rwa [← WithTop.coe_add, add_neg_cancel, WithTop.coe_zero] at this
    · unfold RelClose
      rw [hg, add_assoc, ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero, add_zero]

end Arith

section Order

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]
  [LinearOrder R] [IsStrictOrderedRing R] {δ : WithTop Γ} {x y : Lex R⟦Γ⟧}

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- No cancellation: for `0 ≤ x ≤ y`, `v(y) ≤ v(x)`. A positive element dominates, in
valuation, every nonnegative element below it. -/
theorem orderTop_le_of_nonneg_of_le (hx : 0 ≤ x) (hxy : x ≤ y) :
    (ofLex y).orderTop ≤ (ofLex x).orderTop := by
  refine not_lt.mp fun h => ?_
  have h' := abs_lt_abs_of_orderTop_ofLex h
  rw [abs_of_nonneg hx, abs_of_nonneg (hx.trans hxy)] at h'
  exact h'.not_ge hxy

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- A sum of nonnegative elements has valuation at most that of each summand. -/
theorem orderTop_sum_le {ι : Type*} {S : Finset ι} {f : ι → Lex R⟦Γ⟧} (hf : ∀ i ∈ S, 0 ≤ f i)
    {i : ι} (hi : i ∈ S) : (ofLex (∑ j ∈ S, f j)).orderTop ≤ (ofLex (f i)).orderTop :=
  orderTop_le_of_nonneg_of_le (hf i hi) (single_le_sum hf hi)

/-- A sum of nonnegative terms, each perturbed relatively by `O(δ)`, is perturbed relatively by
`O(δ)`: the no-cancellation step of the proof of `markov:thm:stability`. Only the unperturbed
terms need to be nonnegative. -/
theorem RelClose.sum {ι : Type*} {S : Finset ι} {f f' : ι → Lex R⟦Γ⟧} (hf : ∀ i ∈ S, 0 ≤ f i)
    (h : ∀ i ∈ S, RelClose δ (f i) (f' i)) : RelClose δ (∑ i ∈ S, f i) (∑ i ∈ S, f' i) := by
  unfold RelClose
  rw [← sum_sub_distrib]
  exact Finset.sum_induction _
    (fun z : Lex R⟦Γ⟧ => δ + (ofLex (∑ i ∈ S, f i)).orderTop ≤ (ofLex z).orderTop)
    (fun a b ha hb => (le_min ha hb).trans min_orderTop_le_orderTop_add) (by simp)
    fun i hi => le_trans (by gcongr; exact orderTop_sum_le hf hi) (h i hi)

end Order

section Forest

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]
  [LinearOrder R] [IsStrictOrderedRing R] {δ : WithTop Γ}
  {n : Type*} [Fintype n] [DecidableEq n] {q q' : n → n → Lex R⟦Γ⟧}

omit [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq n] in
/-- The forest weight `q'(f) = ∏_{e ∈ f} q'_e` of an in-forest is `q(f)(1 + O(δ))`. -/
theorem relClose_weight (hδ : 0 ≤ δ) (h : ∀ i j, i ≠ j → RelClose δ (q i j) (q' i j))
    {φ : n → Option n} (hφ : IsInForest φ) : RelClose δ (weight q φ) (weight q' φ) := by
  unfold MarkovForest.weight
  refine RelClose.prod _ hδ fun k _ => ?_
  cases hk : φ k with
  | none => exact RelClose.refl δ 1
  | some p => exact h k p (MarkovForest.ne_of_isInForest hφ hk)

/-- `σ'_k = σ_k(1 + O(δ))` for the scalar forest coefficients. -/
theorem relClose_forestCoeff (hq : ∀ i j, i ≠ j → 0 ≤ q i j) (hδ : 0 ≤ δ)
    (h : ∀ i j, i ≠ j → RelClose δ (q i j) (q' i j)) (k : ℕ) :
    RelClose δ (forestCoeff q k) (forestCoeff q' k) := by
  unfold MarkovForest.forestCoeff
  exact RelClose.sum
    (fun φ hφ => MarkovForest.weight_nonneg hq
      (MarkovForest.mem_allForests.mp (mem_filter.mp hφ).1))
    fun φ hφ => relClose_weight hδ h (MarkovForest.mem_allForests.mp (mem_filter.mp hφ).1)

/-- `F'_k(i, j) = F_k(i, j)(1 + O(δ))` for the matrix forest coefficients. -/
theorem relClose_forestMatrix (hq : ∀ i j, i ≠ j → 0 ≤ q i j) (hδ : 0 ≤ δ)
    (h : ∀ i j, i ≠ j → RelClose δ (q i j) (q' i j)) (k : ℕ) (i j : n) :
    RelClose δ (forestMatrix q k i j) (forestMatrix q' k i j) := by
  classical
  simp only [MarkovForest.forestMatrix, of_apply]
  exact RelClose.sum
    (fun φ hφ => MarkovForest.weight_nonneg hq
      (MarkovForest.mem_allForests.mp (mem_filter.mp (mem_filter.mp hφ).1).1))
    fun φ hφ => relClose_weight hδ h
      (MarkovForest.mem_allForests.mp (mem_filter.mp (mem_filter.mp hφ).1).1)

/-- `D'(s') = D(s)(1 + O(δ))` for the forest denominator. -/
theorem relClose_forestDenom (hq : ∀ i j, i ≠ j → 0 ≤ q i j) (hδ : 0 ≤ δ)
    (h : ∀ i j, i ≠ j → RelClose δ (q i j) (q' i j)) {s s' : Lex R⟦Γ⟧} (hs : 0 ≤ s)
    (hs' : RelClose δ s s') : RelClose δ (forestDenom q s) (forestDenom q' s') := by
  unfold MarkovForest.forestDenom
  exact RelClose.sum
    (fun k _ => mul_nonneg (MarkovForest.forestCoeff_nonneg hq k) (pow_nonneg hs _))
    fun k _ => (relClose_forestCoeff hq hδ h k).mul hδ (hs'.pow hδ _)

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The entries of the forest numerator `N(s) = ∑_k s^{d-k} F_k`. -/
theorem forestNumer_apply (q : n → n → Lex R⟦Γ⟧) (s : Lex R⟦Γ⟧) (i j : n) :
    forestNumer q s i j = ∑ k ∈ range (Fintype.card n - 1 + 1),
      s ^ (Fintype.card n - 1 - k) * forestMatrix q k i j := by
  simp [MarkovForest.forestNumer, Matrix.sum_apply]

/-- `N'(s')_ij = N(s)_ij(1 + O(δ))` for every entry of the forest numerator. -/
theorem relClose_forestNumer (hq : ∀ i j, i ≠ j → 0 ≤ q i j) (hδ : 0 ≤ δ)
    (h : ∀ i j, i ≠ j → RelClose δ (q i j) (q' i j)) {s s' : Lex R⟦Γ⟧} (hs : 0 ≤ s)
    (hs' : RelClose δ s s') (i j : n) :
    RelClose δ (forestNumer q s i j) (forestNumer q' s' i j) := by
  rw [forestNumer_apply, forestNumer_apply]
  exact RelClose.sum
    (fun k _ => mul_nonneg (pow_nonneg hs _) (MarkovForest.forestMatrix_nonneg hq k i j))
    fun k _ => (hs'.pow hδ _).mul hδ (relClose_forestMatrix hq hδ h k i j)

/-- `markov:thm:stability`, general additive form: if `q'_ij = q_ij(1 + O(δ))` off the
diagonal, `s > 0` and `s' = s(1 + O(δ))` with `δ > 0`, then every entry satisfies
`R_{L'}(s')_ij = R_L(s)_ij(1 + O(δ))`. No connectivity, no positivity of `q'` and no spectral
gap is assumed. -/
theorem relClose_resolvent (hq : ∀ i j, i ≠ j → 0 ≤ q i j) (hδ : 0 < δ)
    (h : ∀ i j, i ≠ j → RelClose δ (q i j) (q' i j)) {s s' : Lex R⟦Γ⟧} (hs : 0 < s)
    (hs' : RelClose δ s s') (i j : n) :
    RelClose δ (Markov.resolvent (rowLaplacian q) s i j)
      (Markov.resolvent (rowLaplacian q') s' i j) := by
  haveI : Nonempty n := ⟨i⟩
  have hD := relClose_forestDenom hq hδ.le h hs.le hs'
  have hD0 : forestDenom q s ≠ 0 := (MarkovForest.forestDenom_pos hq hs).ne'
  rw [MarkovForest.resolvent_eq_div hq hs,
    MarkovForest.resolvent_eq_forest q' (hs'.ne_zero hδ hs.ne') (hD.ne_zero hδ hD0)]
  simp only [Matrix.smul_apply, smul_eq_mul, inv_mul_eq_div]
  exact (relClose_forestNumer hq hδ.le h hs.le hs' i j).div hδ hD hD0

/-- `markov:thm:stability` in the ratio form of `markov:eq:relative-stability`, for relatively
close rates and parameters (`δ > 0`, `s > 0`): if the off-diagonal rates `q` are nonnegative and
their graph of positive rates is strongly connected, then
`v(R_{L'}(s')_ij / R_L(s)_ij - 1) ≥ δ` for all `i, j`. -/
theorem stability_core (hq : ∀ i j, i ≠ j → 0 ≤ q i j)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => 0 < q a b) i j) (hδ : 0 < δ)
    (h : ∀ i j, i ≠ j → RelClose δ (q i j) (q' i j)) {s s' : Lex R⟦Γ⟧} (hs : 0 < s)
    (hs' : RelClose δ s s') (i j : n) :
    δ ≤ (ofLex (Markov.resolvent (rowLaplacian q') s' i j /
      Markov.resolvent (rowLaplacian q) s i j - 1)).orderTop := by
  haveI : Nonempty n := ⟨i⟩
  exact (relClose_iff (MarkovForest.resolvent_pos hq hconn hs i j).ne').mp
    (relClose_resolvent hq hδ h hs hs' i j)

/-- `markov:thm:stability`, second clause: for nonnegative off-diagonal rates `q` whose graph of
positive rates is strongly connected, `q'_ij = q_ij(1 + η_ij)` with `v(η_ij) ≥ δ > 0` (`i ≠ j`)
and `s' = s(1 + η_s)` with `v(η_s) ≥ δ`, `v(R_{L'}(s')_ij / R_L(s)_ij - 1) ≥ δ` for every
positive `s` and all `i, j`. -/
theorem stability_of_param {η : n → n → Lex R⟦Γ⟧} {ηs s : Lex R⟦Γ⟧}
    (hq : ∀ i j, i ≠ j → 0 ≤ q i j)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => 0 < q a b) i j) (hδ : 0 < δ)
    (hη : ∀ i j, i ≠ j → δ ≤ (ofLex (η i j)).orderTop)
    (hq' : ∀ i j, i ≠ j → q' i j = q i j * (1 + η i j)) (hηs : δ ≤ (ofLex ηs).orderTop)
    (hs : 0 < s) (i j : n) :
    δ ≤ (ofLex (Markov.resolvent (rowLaplacian q') (s * (1 + ηs)) i j /
      Markov.resolvent (rowLaplacian q) s i j - 1)).orderTop :=
  stability_core hq hconn hδ
    (fun a b hab => by rw [hq' a b hab]; exact relClose_mul_one_add (hη a b hab) _) hs
    (relClose_mul_one_add hηs s) i j

/-- `markov:thm:stability`, `markov:eq:relative-stability`: for nonnegative off-diagonal rates `q`
whose graph of positive rates is strongly connected and `q'_ij = q_ij(1 + η_ij)` with
`v(η_ij) ≥ δ > 0` (`i ≠ j`), `v(R_{L'}(s)_ij / R_L(s)_ij - 1) ≥ δ` for every positive `s` and all
`i, j`. -/
theorem stability {η : n → n → Lex R⟦Γ⟧} {s : Lex R⟦Γ⟧}
    (hq : ∀ i j, i ≠ j → 0 ≤ q i j)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => 0 < q a b) i j) (hδ : 0 < δ)
    (hη : ∀ i j, i ≠ j → δ ≤ (ofLex (η i j)).orderTop)
    (hq' : ∀ i j, i ≠ j → q' i j = q i j * (1 + η i j)) (hs : 0 < s) (i j : n) :
    δ ≤ (ofLex (Markov.resolvent (rowLaplacian q') s i j /
      Markov.resolvent (rowLaplacian q) s i j - 1)).orderTop := by
  simpa using stability_of_param (ηs := 0) hq hconn hδ hη hq' (by simp) hs i j

/-- `markov:thm:stability` with the source's literal hypotheses: both rate systems have the same
strongly connected allowed graph `E`, `q` is positive on `E`, both vanish off `E` (off the
diagonal), and `q'_e = q_e(1 + η_e)` with `v(η_e) ≥ δ > 0` on `E`; the parameter is
`s' = s(1 + η_s)` with `v(η_s) ≥ δ`. -/
theorem stability_of_graph {E : n → n → Prop} (hE : ∀ i j, Relation.ReflTransGen E i j)
    (hpos : ∀ i j, i ≠ j → E i j → 0 < q i j) (hzero : ∀ i j, i ≠ j → ¬E i j → q i j = 0)
    (hzero' : ∀ i j, i ≠ j → ¬E i j → q' i j = 0) {η : n → n → Lex R⟦Γ⟧} {ηs s : Lex R⟦Γ⟧}
    (hδ : 0 < δ) (hη : ∀ i j, i ≠ j → E i j → δ ≤ (ofLex (η i j)).orderTop)
    (hq' : ∀ i j, i ≠ j → E i j → q' i j = q i j * (1 + η i j))
    (hηs : δ ≤ (ofLex ηs).orderTop) (hs : 0 < s) (i j : n) :
    δ ≤ (ofLex (Markov.resolvent (rowLaplacian q') (s * (1 + ηs)) i j /
      Markov.resolvent (rowLaplacian q) s i j - 1)).orderTop := by
  have hq : ∀ i j, i ≠ j → 0 ≤ q i j := fun a b hab => by
    by_cases hE' : E a b
    · exact (hpos a b hab hE').le
    · exact (hzero a b hab hE').ge
  have hconn : ∀ i j, Relation.ReflTransGen (fun a b => 0 < q a b) i j := by
    intro a b
    induction hE a b with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih =>
      by_cases h : c = d
      · exact h ▸ ih
      · exact ih.tail (hpos c d h hcd)
  refine stability_core hq hconn hδ (fun a b hab => ?_) hs (relClose_mul_one_add hηs s) i j
  by_cases hE' : E a b
  · rw [hq' a b hab hE']
    exact relClose_mul_one_add (hη a b hab hE') _
  · rw [hzero a b hab hE', hzero' a b hab hE']
    exact RelClose.refl δ 0

omit [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq n] in
/-- Finitely many rates with the same valuations and leading coefficients are relatively close
with one common positive `δ`. -/
theorem exists_relClose_of_leading_rates
    (hlead : ∀ i j, i ≠ j → (ofLex (q' i j)).orderTop = (ofLex (q i j)).orderTop ∧
      (ofLex (q' i j)).leadingCoeff = (ofLex (q i j)).leadingCoeff) :
    ∃ δ : WithTop Γ, 0 < δ ∧ ∀ i j, i ≠ j → RelClose δ (q i j) (q' i j) := by
  classical
  have hp : ∀ p : n × n, ∃ δ : WithTop Γ, 0 < δ ∧
      (p.1 ≠ p.2 → RelClose δ (q p.1 p.2) (q' p.1 p.2)) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨⊤, WithTop.coe_lt_top 0, fun h => absurd hp h⟩
    · obtain ⟨δ, hδ, h⟩ := exists_relClose_of_leading (hlead _ _ hp).1 (hlead _ _ hp).2
      exact ⟨δ, hδ, fun _ => h⟩
  choose d hd using hp
  exact ⟨univ.inf d, (Finset.lt_inf_iff (WithTop.coe_lt_top 0)).mpr fun p _ => (hd p).1,
    fun i j hij => ((hd (i, j)).2 hij).mono (Finset.inf_le (mem_univ _))⟩

end Forest

section Shadow

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] {δ : WithTop Γ}
  {n : Type*} [Fintype n] [DecidableEq n] {q q' : n → n → Lex ℝ⟦Γ⟧}

/-- Relatively close rates and parameters (`δ > 0`) have the same residue shadow:
`res R_{L'}(s') = res R_L(s)`, because every entry of `R_L(s)` lies in `𝒪` and the entrywise
error has valuation at least `δ > 0`. -/
theorem shadowAt_eq (hq : ∀ i j, i ≠ j → 0 ≤ q i j) (hδ : 0 < δ)
    (h : ∀ i j, i ≠ j → RelClose δ (q i j) (q' i j)) {s s' : Lex ℝ⟦Γ⟧} (hs : 0 < s)
    (hs' : RelClose δ s s') :
    MarkovShadow.shadowAt (rowLaplacian q') s' = MarkovShadow.shadowAt (rowLaplacian q) s := by
  ext i j
  have hR := relClose_resolvent hq hδ h hs hs' i j
  have h0 := MarkovShadow.orderTop_resolvent_nonneg hq hs i j
  have hpos : ((0 : Γ) : WithTop Γ) < (ofLex (Markov.resolvent (rowLaplacian q') s' i j -
      Markov.resolvent (rowLaplacian q) s i j)).orderTop :=
    lt_of_lt_of_le (lt_of_lt_of_le hδ (le_add_of_nonneg_right h0)) hR
  have h1 := coeff_eq_zero_of_lt_orderTop hpos
  rw [ofLex_sub, coeff_sub, sub_eq_zero] at h1
  simp only [MarkovShadow.shadowAt, MarkovShadow.resMap_apply, MarkovShadow.res_apply]
  exact h1

/-- `markov:cor:leading-equivalence`, at the level of shadows and marked entries: nonnegative
off-diagonal rates `q` and rates `q'` with the same edge valuations and edge leading coefficients
(hence the same graph) have the same residue `res R_L(s)` at every positive `s`, the same shadows
`K_α(c)` for every `α` and every real `c > 0`, and the same valuation and leading coefficient of
every entry `R_L(s)_ij` at every positive `s`. The plateau projections, crossover kernels and
effective generators of the corollary are not stated here. -/
theorem leading_equivalence (hq : ∀ i j, i ≠ j → 0 ≤ q i j)
    (hlead : ∀ i j, i ≠ j → (ofLex (q' i j)).orderTop = (ofLex (q i j)).orderTop ∧
      (ofLex (q' i j)).leadingCoeff = (ofLex (q i j)).leadingCoeff) :
    (∀ s : Lex ℝ⟦Γ⟧, 0 < s →
      MarkovShadow.shadowAt (rowLaplacian q') s = MarkovShadow.shadowAt (rowLaplacian q) s) ∧
    (∀ (α : Γ) (c : ℝ), 0 < c →
      MarkovShadow.shadow (rowLaplacian q') α c = MarkovShadow.shadow (rowLaplacian q) α c) ∧
    ∀ s : Lex ℝ⟦Γ⟧, 0 < s → ∀ i j,
      (ofLex (Markov.resolvent (rowLaplacian q') s i j)).orderTop =
        (ofLex (Markov.resolvent (rowLaplacian q) s i j)).orderTop ∧
      (ofLex (Markov.resolvent (rowLaplacian q') s i j)).leadingCoeff =
        (ofLex (Markov.resolvent (rowLaplacian q) s i j)).leadingCoeff := by
  obtain ⟨δ, hδ, h⟩ := exists_relClose_of_leading_rates hlead
  refine ⟨fun s hs => shadowAt_eq hq hδ h hs (RelClose.refl δ s),
    fun α c hc => shadowAt_eq hq hδ h (MarkovShadow.mono_pos hc) (RelClose.refl δ _),
    fun s hs i j => ?_⟩
  have hR := relClose_resolvent hq hδ h hs (RelClose.refl δ s) i j
  exact ⟨hR.orderTop_eq hδ, hR.leadingCoeff_eq hδ⟩

end Shadow

section Sharp

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]
  [LinearOrder R] [IsStrictOrderedRing R]

/-- The two-state rates of `markov:ex:sharp`: `q₁₂ = 1 + η` and `q₂₁ = 1` (states `0, 1`). The
diagonal entries are ignored by `rowLaplacian`. -/
def sharpRates (η : Lex R⟦Γ⟧) : Fin 2 → Fin 2 → Lex R⟦Γ⟧ :=
  fun i j => if i = 0 ∧ j = 1 then 1 + η else 1

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- In `sharpRates η` only `q₁₂` differs from the unperturbed rates, by the factor `1 + η`. -/
theorem sharpRates_eq (η : Lex R⟦Γ⟧) (i j : Fin 2) :
    sharpRates η i j = sharpRates 0 i j * (1 + if i = 0 ∧ j = 1 then η else 0) := by
  unfold sharpRates
  split_ifs <;> simp

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- For the rates of `markov:ex:sharp`, `R_L(1)₁₂ = (1 + η)/(3 + η)`. -/
theorem resolvent_sharpRates {η : Lex R⟦Γ⟧} (h3 : (3 : Lex R⟦Γ⟧) + η ≠ 0) :
    Markov.resolvent (rowLaplacian (sharpRates η)) 1 0 1 = (1 + η) / (3 + η) := by
  have hX : Markov.resolvent (rowLaplacian (sharpRates η)) 1 =
      !![2 / (3 + η), (1 + η) / (3 + η); 1 / (3 + η), (2 + η) / (3 + η)] := by
    apply Markov.resolvent_eq_of_mul_eq one_ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [MarkovForest.rowLaplacian, sharpRates, Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;> ring
  rw [hX]
  simp

/-- `markov:ex:sharp`: changing only `q₁₂ = 1` to `1 + η`, with `v(η) > 0`, changes
`R_L(1)₁₂ = 1/3` into `(1 + η)/(3 + η)`, whose relative error `2η/(3 + η)` has valuation exactly
`v(η)`. -/
theorem sharp {η : Lex R⟦Γ⟧} (hη : 0 < (ofLex η).orderTop) :
    (ofLex (Markov.resolvent (rowLaplacian (sharpRates η)) 1 0 1 /
      Markov.resolvent (rowLaplacian (sharpRates 0)) 1 0 1 - 1)).orderTop =
      (ofLex η).orderTop := by
  have hv3 : (ofLex (3 : Lex R⟦Γ⟧)).orderTop = 0 := by
    rw [show ofLex (3 : Lex R⟦Γ⟧) = single 0 (3 : R) from rfl, orderTop_single three_ne_zero,
      WithTop.coe_zero]
  have hv2 : (ofLex (2 : Lex R⟦Γ⟧)).orderTop = 0 := by
    rw [show ofLex (2 : Lex R⟦Γ⟧) = single 0 (2 : R) from rfl, orderTop_single two_ne_zero,
      WithTop.coe_zero]
  have hv3η : (ofLex (3 + η)).orderTop = 0 := by
    rw [ofLex_add, orderTop_add_eq_left (by rwa [hv3]), hv3]
  have h3η : (3 : Lex R⟦Γ⟧) + η ≠ 0 := fun h => by
    rw [h, ofLex_zero, orderTop_zero] at hv3η
    exact WithTop.top_ne_zero hv3η
  have h3 : (3 : Lex R⟦Γ⟧) + 0 ≠ 0 := by
    rw [add_zero]
    exact three_ne_zero
  rw [resolvent_sharpRates h3η, resolvent_sharpRates h3]
  have e : (1 + η) / (3 + η) / ((1 + 0) / (3 + 0)) - 1 = 2 * η / (3 + η) := by
    field_simp
    ring
  rw [e]
  have := congrArg (fun z => (ofLex z).orderTop) (div_mul_cancel₀ (2 * η) h3η)
  simp only [orderTop_ofLex_mul, hv3η, hv2, add_zero, zero_add] at this
  exact this

end Sharp

end

end Surreal.ForestStability
