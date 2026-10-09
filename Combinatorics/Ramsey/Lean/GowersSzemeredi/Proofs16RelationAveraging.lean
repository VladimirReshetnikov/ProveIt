import GowersSzemeredi.Definitions

/-! The two counting steps of the algebraic regularity iteration ([49],
proof of Theorem 33, p. 28), independent of the domain structure.

When a piece is not quasirandom, at least `θ|S|²` pairs `(y, y′)` carry a
bad bounded relation `Σ ν_γ γ + λ·L(y) + λ′·L(y′) = 0`.

* `exists_popular_witness`: some single relation is carried by at least a
  `1/#relations` fraction of them (pigeonhole).
* `collision_pairs_ge`: if `f(y) = h(y′)` holds for at least `θ|Y|²` pairs,
  then `f(y₁) = f(y₂)` holds for at least `θ²|Y|²` pairs (Cauchy–Schwarz
  over the fibres). In [49] this turns one relation between `y` and `y′`
  into `λ·L(y₁) = λ·L(y₂)` for many pairs. Freiman-linearity then makes
  `λ·L` vanish on many differences `y₁ − y₂`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Finset

/-- **One witness carries a large share of the bad pairs.** -/
theorem exists_popular_witness {α β : Type*} [DecidableEq α] [DecidableEq β] (P : Finset α) (R : Finset β)
    (Wit : α → β → Prop) [∀ p r, Decidable (Wit p r)] (hR : R.Nonempty)
    (hW : ∀ p ∈ P, ∃ r ∈ R, Wit p r) :
    ∃ r ∈ R, (P.card : ℝ) ≤ R.card * (P.filter fun p => Wit p r).card := by
  by_contra hno
  push Not at hno
  have hcover : P ⊆ R.biUnion fun r => P.filter fun p => Wit p r := by
    intro p hp
    obtain ⟨r, hr, hw⟩ := hW p hp
    exact Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_filter.mpr ⟨hp, hw⟩⟩
  have h1 : (P.card : ℝ) ≤ ∑ r ∈ R, ((P.filter fun p => Wit p r).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have h2 : ∑ r ∈ R, ((P.filter fun p => Wit p r).card : ℝ) < ∑ _r ∈ R, (P.card : ℝ) / R.card := by
    apply Finset.sum_lt_sum_of_nonempty hR
    intro r hr
    have hRpos : (0 : ℝ) < R.card := by exact_mod_cast hR.card_pos
    rw [lt_div_iff₀ hRpos, mul_comm]
    exact hno r hr
  have h3 : ∑ _r ∈ R, (P.card : ℝ) / R.card = P.card := by
    have hRpos : (0 : ℝ) < R.card := by exact_mod_cast hR.card_pos
    rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  linarith

/-- **Collisions from a matching relation** (Cauchy–Schwarz over fibres). -/
theorem collision_pairs_ge {Y Z : Type*} [Fintype Y] [DecidableEq Z] (f h : Y → Z)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hpairs : θ * (Fintype.card Y : ℝ) ^ 2 ≤
      ((Finset.univ.filter fun p : Y × Y => f p.1 = h p.2).card : ℝ)) :
    θ ^ 2 * (Fintype.card Y : ℝ) ^ 2 ≤
      ((Finset.univ.filter fun p : Y × Y => f p.1 = f p.2).card : ℝ) := by
  -- fibre sizes, as indicator sums
  let a : Z → ℝ := fun z => ∑ y : Y, if f y = z then (1 : ℝ) else 0
  have hcard : ∀ (g g' : Y → Z),
      ((Finset.univ.filter fun p : Y × Y => g p.1 = g' p.2).card : ℝ) =
        ∑ y : Y, ∑ y' : Y, if g y = g' y' then (1 : ℝ) else 0 := by
    intro g g'
    rw [Finset.card_filter, Fintype.sum_prod_type]
    push_cast; rfl
  have h1 : ((Finset.univ.filter fun p : Y × Y => f p.1 = h p.2).card : ℝ) =
      ∑ y' : Y, a (h y') := by
    rw [hcard, Finset.sum_comm]
  have h2 : ((Finset.univ.filter fun p : Y × Y => f p.1 = f p.2).card : ℝ) =
      ∑ y : Y, a (f y) := by
    rw [hcard]
    apply Finset.sum_congr rfl; intro y _
    apply Finset.sum_congr rfl; intro y' _
    by_cases hy : f y = f y' <;> simp [hy, eq_comm]
  have hsq : ∑ y' : Y, a (h y') ^ 2 ≤ Fintype.card Y * ∑ y : Y, a (f y) := by
    have hregroup : ∑ y' : Y, a (h y') ^ 2 =
        ∑ y : Y, a (f y) * ∑ y' : Y, if f y = h y' then (1 : ℝ) else 0 := by
      calc ∑ y' : Y, a (h y') ^ 2 = ∑ y' : Y, ∑ y : Y,
            (if f y = h y' then (1 : ℝ) else 0) * a (h y') := by
            apply Finset.sum_congr rfl; intro y' _
            rw [sq, ← Finset.sum_mul]
        _ = ∑ y' : Y, ∑ y : Y, (if f y = h y' then (1 : ℝ) else 0) * a (f y) := by
            apply Finset.sum_congr rfl; intro y' _
            apply Finset.sum_congr rfl; intro y _
            by_cases hy : f y = h y' <;> simp [hy]
        _ = _ := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro y _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro y' _
            ring
    rw [hregroup, Finset.mul_sum]
    apply Finset.sum_le_sum; intro y _
    have ha0 : 0 ≤ a (f y) := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    have hb : ∑ y' : Y, (if f y = h y' then (1 : ℝ) else 0) ≤ Fintype.card Y := by
      calc _ ≤ ∑ _y' : Y, (1 : ℝ) := Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num
        _ = _ := by simp
    nlinarith
  have hcs : (∑ y' : Y, a (h y')) ^ 2 ≤ Fintype.card Y * ∑ y' : Y, a (h y') ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun y' => a (h y')) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    linarith
  rw [h1] at hpairs
  rw [h2]
  have hY0 : (0 : ℝ) ≤ Fintype.card Y := by positivity
  rcases hY0.eq_or_lt with hY | hY
  · rw [← hY]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  · have hA0 : 0 ≤ θ * (Fintype.card Y : ℝ) ^ 2 := by positivity
    have hstep : (θ * (Fintype.card Y : ℝ) ^ 2) ^ 2 ≤
        (Fintype.card Y : ℝ) ^ 2 * ∑ y : Y, a (f y) := by
      calc (θ * (Fintype.card Y : ℝ) ^ 2) ^ 2 ≤ (∑ y' : Y, a (h y')) ^ 2 :=
            pow_le_pow_left₀ hA0 hpairs 2
        _ ≤ Fintype.card Y * ∑ y' : Y, a (h y') ^ 2 := hcs
        _ ≤ Fintype.card Y * (Fintype.card Y * ∑ y : Y, a (f y)) :=
            mul_le_mul_of_nonneg_left hsq hY.le
        _ = _ := by ring
    have hY2 : (0 : ℝ) < (Fintype.card Y : ℝ) ^ 2 := by positivity
    have : θ ^ 2 * (Fintype.card Y : ℝ) ^ 2 * (Fintype.card Y : ℝ) ^ 2 ≤
        (∑ y : Y, a (f y)) * (Fintype.card Y : ℝ) ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right this hY2

end LeanProofs.GowersSzemeredi
