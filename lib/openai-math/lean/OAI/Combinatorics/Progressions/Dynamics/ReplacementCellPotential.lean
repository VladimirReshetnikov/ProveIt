import OAI.Combinatorics.Progressions.Estimates.AmplificationFinalCostGrowth
import OAI.Combinatorics.Progressions.Estimates.LocalMomentScale

namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem rpow_sub_rpow_ge_tangent {u v θ : ℝ} (hu : 0 < u) (hv : 0 ≤ v)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ * u ^ (θ - 1) * (u - v) ≤ u ^ θ - v ^ θ := by
  have hratio : (v / u) ^ θ ≤ 1 + θ * (v / u - 1) := by
    have h := rpow_one_add_le_one_add_mul_self
      (s := v / u - 1) (by have := div_nonneg hv hu.le; linarith) hθ0 hθ1
    simpa only [add_sub_cancel] using h
  have hscaled := mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hu.le θ)
  have heq : u ^ θ * (v / u) ^ θ = v ^ θ := by
    rw [Real.div_rpow hv hu.le]
    field_simp
  rw [heq] at hscaled
  rw [Real.rpow_sub_one hu.ne']
  calc
    θ * (u ^ θ / u) * (u - v) =
        u ^ θ - u ^ θ * (1 + θ * (v / u - 1)) := by field_simp; ring
    _ ≤ _ := sub_le_sub_left hscaled _

theorem peeling_rpow {u v u₁ b K θ : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hK : 0 < K) (hbu : 0 ≤ b * u₁ ∧ b * u₁ ≤ u) (hKu : K * u ≤ u₁)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ * K ^ (1 - θ) * b * (u₁ * v) ^ θ ≤
      (u * v) ^ θ - ((u - b * u₁) * v) ^ θ := by
  have hu₁ : 0 < u₁ := (mul_pos hK hu).trans_le hKu
  have hb : 0 ≤ b := by nlinarith [hbu.1]
  have hremaining : 0 ≤ u - b * u₁ := sub_nonneg.mpr hbu.2
  have hratio : K ≤ u₁ / u := (le_div_iff₀ hu).mpr hKu
  have hratioPow := Real.rpow_le_rpow hK.le hratio (sub_nonneg.mpr hθ1)
  have hinv : u ^ (θ - 1) = (u ^ (1 - θ))⁻¹ := by
    rw [show θ - 1 = -(1 - θ) by ring, Real.rpow_neg hu.le]
  have hidentity : (u₁ / u) ^ (1 - θ) * u₁ ^ θ = u ^ (θ - 1) * u₁ := by
    calc
      _ = (u₁ ^ (1 - θ) * u₁ ^ θ) / u ^ (1 - θ) := by
        rw [Real.div_rpow hu₁.le hu.le]
        ring
      _ = u₁ / u ^ (1 - θ) := by
        rw [← Real.rpow_add hu₁, sub_add_cancel, Real.rpow_one]
      _ = _ := by rw [hinv]; ring
  have hpower : K ^ (1 - θ) * u₁ ^ θ ≤ u ^ (θ - 1) * u₁ := by
    rw [← hidentity]
    exact mul_le_mul_of_nonneg_right hratioPow (Real.rpow_nonneg hu₁.le θ)
  have htangent := rpow_sub_rpow_ge_tangent hu hremaining hθ0 hθ1
  calc
    θ * K ^ (1 - θ) * b * (u₁ * v) ^ θ =
        v ^ θ * (θ * b * (K ^ (1 - θ) * u₁ ^ θ)) := by
      rw [Real.mul_rpow hu₁.le hv.le]
      ring
    _ ≤ v ^ θ * (θ * b * (u ^ (θ - 1) * u₁)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpower (mul_nonneg hθ0 hb)) (Real.rpow_nonneg hv.le θ)
    _ = v ^ θ * (θ * u ^ (θ - 1) * (u - (u - b * u₁))) := by ring
    _ ≤ v ^ θ * (u ^ θ - (u - b * u₁) ^ θ) :=
      mul_le_mul_of_nonneg_left htangent (Real.rpow_nonneg hv.le θ)
    _ = _ := by
      rw [Real.mul_rpow hu.le hv.le, Real.mul_rpow hremaining hv.le]
      ring

theorem peeling_quarter {u v u₁ b K : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hK : 0 < K) (hbu : 0 ≤ b * u₁ ∧ b * u₁ ≤ u) (hKu : K * u ≤ u₁) :
    (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) * b * (u₁ * v) ^ (1 / 4 : ℝ) ≤
      (u * v) ^ (1 / 4 : ℝ) - ((u - b * u₁) * v) ^ (1 / 4 : ℝ) := by
  convert peeling_rpow hu hv hK hbu hKu (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 1) using 1
  norm_num

theorem sq_deviation_le_sqrt_gap {x M : ℝ} (hx : 0 ≤ x) (hxM : x ≤ M) :
    (x - 1) ^ 2 ≤ 2 * (1 + Real.sqrt M) ^ 2 * ((1 + x) / 2 - Real.sqrt x) := by
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hsq : Real.sqrt x ≤ Real.sqrt M := Real.sqrt_le_sqrt hxM
  have hgap : 0 ≤ (1 + x) / 2 - Real.sqrt x := by
    nlinarith [sq_nonneg (Real.sqrt x - 1)]
  have hfac : 2 * (1 + Real.sqrt x) ^ 2 ≤ 2 * (1 + Real.sqrt M) ^ 2 := by
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg M]
  calc
    (x - 1) ^ 2 = 2 * (1 + Real.sqrt x) ^ 2 * ((1 + x) / 2 - Real.sqrt x) := by
      have hid : ((Real.sqrt x) ^ 2 - 1) ^ 2 =
          2 * (1 + Real.sqrt x) ^ 2 * ((1 + (Real.sqrt x) ^ 2) / 2 - Real.sqrt x) := by
        ring
      simpa only [hsx] using hid
    _ ≤ _ := mul_le_mul_of_nonneg_right hfac hgap

theorem sqrt_average_le_of_second_moment {ι : Type*} [Fintype ι]
    (w X : ι → ℝ) {M c : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hwSum : ∑ i, w i = 1)
    (hX : ∀ i, 0 ≤ X i) (hXM : ∀ i, X i ≤ M)
    (hmean : ∑ i, w i * X i ≤ 1)
    (hsecond : 1 + c ≤ ∑ i, w i * (X i) ^ 2) :
    (∑ i, w i * Real.sqrt (X i)) ≤
      1 - c / (2 * (1 + Real.sqrt M) ^ 2) := by
  have hden : 0 < 2 * (1 + Real.sqrt M) ^ 2 := by
    positivity
  have hvariance : c ≤ ∑ i, w i * (X i - 1) ^ 2 := by
    have heq : (∑ i, w i * (X i - 1) ^ 2) =
        (∑ i, w i * (X i) ^ 2) - 2 * (∑ i, w i * X i) + 1 := by
      calc
        _ = ∑ i, (w i * (X i) ^ 2 - 2 * (w i * X i) + w i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, hwSum]
    rw [heq]
    linarith
  have hbound : (∑ i, w i * (X i - 1) ^ 2) ≤
      2 * (1 + Real.sqrt M) ^ 2 *
        ((1 + ∑ i, w i * X i) / 2 - ∑ i, w i * Real.sqrt (X i)) := by
    calc
      _ ≤ ∑ i, w i * (2 * (1 + Real.sqrt M) ^ 2 *
          ((1 + X i) / 2 - Real.sqrt (X i))) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (sq_deviation_le_sqrt_gap (hX i) (hXM i)) (hw i)
      _ = _ := by
        have hid : ∀ i, w i * (2 * (1 + Real.sqrt M) ^ 2 *
            ((1 + X i) / 2 - Real.sqrt (X i))) =
            2 * (1 + Real.sqrt M) ^ 2 *
              ((w i + w i * X i) / 2 - w i * Real.sqrt (X i)) := by
          intro i
          ring
        simp_rw [hid]
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div,
          Finset.sum_add_distrib, hwSum]
  have hfinal : c ≤ 2 * (1 + Real.sqrt M) ^ 2 *
      (1 - ∑ i, w i * Real.sqrt (X i)) := by
    have hm : (1 + ∑ i, w i * X i) / 2 - ∑ i, w i * Real.sqrt (X i) ≤
        1 - ∑ i, w i * Real.sqrt (X i) := by linarith
    exact hvariance.trans (hbound.trans (mul_le_mul_of_nonneg_left hm hden.le))
  have hdiv : c / (2 * (1 + Real.sqrt M) ^ 2) ≤
      1 - ∑ i, w i * Real.sqrt (X i) := (div_le_iff₀ hden).mpr (by nlinarith)
  linarith

theorem sqrt_average_sq_le {ι : Type*} [Fintype ι] (w X : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwSum : ∑ i, w i = 1) (hX : ∀ i, 0 ≤ X i) :
    (∑ i, w i * Real.sqrt (X i)) ^ 2 ≤ ∑ i, w i * X i := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i ↦ w i * Real.sqrt (X i)) (f := w) (g := fun i ↦ w i * X i)
    (fun i _ ↦ hw i) (fun i _ ↦ mul_nonneg (hw i) (hX i))
    (fun i _ ↦ by rw [mul_pow, Real.sq_sqrt (hX i)]; nlinarith)
  simpa only [hwSum, one_mul] using h

theorem fourth_root_product_average_le {ι : Type*} [Fintype ι]
    (w X Y : ι → ℝ) {M c : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hwSum : ∑ i, w i = 1)
    (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i) (hXM : ∀ i, X i ≤ M)
    (hmeanX : ∑ i, w i * X i ≤ 1) (hmeanY : ∑ i, w i * Y i ≤ 1)
    (hsecond : 1 + c ≤ ∑ i, w i * (X i) ^ 2) :
    (∑ i, w i * (X i * Y i) ^ (1 / 4 : ℝ)) ≤
      1 - c / (4 * (1 + Real.sqrt M) ^ 2) := by
  have hroot (i : ι) : (X i * Y i) ^ (1 / 4 : ℝ) =
      Real.sqrt (Real.sqrt (X i * Y i)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (mul_nonneg (hX i) (hY i))]
    norm_num
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i ↦ w i * (X i * Y i) ^ (1 / 4 : ℝ))
    (f := fun i ↦ w i * Real.sqrt (X i)) (g := fun i ↦ w i * Real.sqrt (Y i))
    (fun i _ ↦ mul_nonneg (hw i) (Real.sqrt_nonneg _))
    (fun i _ ↦ mul_nonneg (hw i) (Real.sqrt_nonneg _)) (fun i _ ↦ by
      rw [hroot, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sqrt_mul (hX i)]
      exact le_of_eq (by ring))
  have hYsq := sqrt_average_sq_le w Y hw hwSum hY
  have hYmean : (∑ i, w i * Real.sqrt (Y i)) ≤ 1 := by nlinarith
  have hXnonneg : 0 ≤ ∑ i, w i * Real.sqrt (X i) :=
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hw i) (Real.sqrt_nonneg _))
  have hprod := mul_le_mul_of_nonneg_left hYmean hXnonneg
  simp only [mul_one] at hprod
  have hXmean := sqrt_average_le_of_second_moment w X hw hwSum hX hXM hmeanX hsecond
  have hsq : (∑ i, w i * (X i * Y i) ^ (1 / 4 : ℝ)) ^ 2 ≤
      1 - c / (2 * (1 + Real.sqrt M) ^ 2) := by
    exact hcs.trans (hprod.trans hXmean)
  have hhalf : c / (4 * (1 + Real.sqrt M) ^ 2) =
      (c / (2 * (1 + Real.sqrt M) ^ 2)) / 2 := by
    rw [div_div]
    congr 1
    ring
  rw [hhalf]
  nlinarith [sq_nonneg ((∑ i, w i * (X i * Y i) ^ (1 / 4 : ℝ)) - 1)]

end Erdos3

end

section

namespace Erdos3

theorem concave_power_drop {p p' β ν c : ℝ} (hp : 0 < p) (hp' : 0 ≤ p')
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hdrop : p' ≤ p - c * p ^ ν) :
    β * c * p ^ (β + ν - 1) ≤ p ^ β - p' ^ β := by
  have htangent := rpow_sub_rpow_ge_tangent hp hp' hβ0 hβ1
  calc
    β * c * p ^ (β + ν - 1) = β * p ^ (β - 1) * (c * p ^ ν) := by
      rw [show β + ν - 1 = (β - 1) + ν by ring, Real.rpow_add hp]
      ring
    _ ≤ β * p ^ (β - 1) * (p - p') :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hβ0 (Real.rpow_nonneg hp.le _))
    _ ≤ _ := htangent

theorem density_invariant_preserved {p p' L L' A C₀ C β ν c : ℝ}
    (hp : 0 < p) (hp' : 0 ≤ p') (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hA : 0 ≤ A)
    (hinvariant : A * p ^ β + C₀ ≤ L)
    (hdrop : p' ≤ p - c * p ^ ν)
    (hlength : L - C * Real.log (2 + p) ≤ L')
    (hpayment : C * Real.log (2 + p) ≤ A * (β * c * p ^ (β + ν - 1))) :
    A * p' ^ β + C₀ ≤ L' := by
  have hpotential := mul_le_mul_of_nonneg_left
    (concave_power_drop hp hp' hβ0 hβ1 hdrop) hA
  nlinarith

theorem no_invariant_of_descent {S : Type*} (P : S → Prop) (potential : S → ℝ)
    (T : ℝ)
    (h_nonneg : ∀ x, P x → 0 ≤ potential x)
    (h_terminal : ∀ x, P x → potential x ≤ T → False)
    (h_step : ∀ x, P x → T < potential x →
      ∃ y, P y ∧ potential y + 1 ≤ potential x) :
    ∀ x, ¬ P x := by
  have h : ∀ n : ℕ, ∀ x, ⌊potential x⌋₊ = n → ¬ P x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx hPx
      have hlarge : T < potential x := lt_of_not_ge (h_terminal x hPx)
      obtain ⟨y, hPy, hdec⟩ := h_step x hPx hlarge
      have hfloor := Nat.floor_mono hdec
      rw [Nat.floor_add_one (h_nonneg y hPy), hx] at hfloor
      exact ih ⌊potential y⌋₊ (by omega) y rfl hPy
  intro x
  exact h _ x rfl

end Erdos3

end

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem step_mass_bounds (B C : Finset G) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ B → f x = 0) :
    0 ≤ (C.card : ℝ) / B.card * (𝔼 x ∈ C, f x) ∧
      (C.card : ℝ) / B.card * (𝔼 x ∈ C, f x) ≤ 𝔼 x ∈ B, f x := by
  constructor
  · exact mul_nonneg (by positivity) (Finset.expect_nonneg (fun x _ => hf x))
  · have h := Finset.expect_nonneg (s := B) (fun x _ => remainder_nonneg C f hf x)
    rw [expect_remainder B C f hsupport] at h
    linarith

theorem step_potential_le (B C : Finset G) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ B → f x = 0)
    {v K : ℝ} (hu : 0 < 𝔼 x ∈ B, f x) (hv : 0 < v) (hK : 0 < K)
    (hconc : K * (𝔼 x ∈ B, f x) ≤ 𝔼 x ∈ C, f x) :
    (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) * ((C.card : ℝ) / B.card) *
        ((𝔼 x ∈ C, f x) * v) ^ (1 / 4 : ℝ) ≤
      ((𝔼 x ∈ B, f x) * v) ^ (1 / 4 : ℝ) -
        ((𝔼 x ∈ B, remainder C f x) * v) ^ (1 / 4 : ℝ) := by
  rw [expect_remainder B C f hsupport]
  exact peeling_quarter hu hv hK (step_mass_bounds B C f hf hsupport) hconc

theorem step_coefficient_le_mass_drop (B C : Finset G) (f : G → ℝ)
    (hsupport : ∀ x, x ∉ B → f x = 0) {K kappa : ℝ}
    (hK : 0 ≤ K) (hactive : kappa ≤ 𝔼 x ∈ B, f x)
    (hconc : K * (𝔼 x ∈ B, f x) ≤ 𝔼 x ∈ C, f x) :
    (K * kappa) * ((C.card : ℝ) / B.card) ≤
      (𝔼 x ∈ B, f x) - 𝔼 x ∈ B, remainder C f x := by
  have hlower := (mul_le_mul_of_nonneg_left hactive hK).trans hconc
  have h := mul_le_mul_of_nonneg_right hlower (show 0 ≤ (C.card : ℝ) / B.card by positivity)
  rw [expect_remainder B C f hsupport]
  nlinarith

end Erdos3.Peeling

end

section

namespace Erdos3

open scoped BigOperators

theorem fourth_root_product_average_le_means {ι : Type*} [Fintype ι]
    (w X Y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwSum : ∑ i, w i = 1)
    (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i) :
    (∑ i, w i * (X i * Y i) ^ (1 / 4 : ℝ)) ≤
      ((∑ i, w i * X i) * ∑ i, w i * Y i) ^ (1 / 4 : ℝ) := by
  have hroot (i : ι) : (X i * Y i) ^ (1 / 4 : ℝ) =
      Real.sqrt (Real.sqrt (X i * Y i)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (mul_nonneg (hX i) (hY i))]
    norm_num
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i => w i * (X i * Y i) ^ (1 / 4 : ℝ))
    (f := fun i => w i * Real.sqrt (X i)) (g := fun i => w i * Real.sqrt (Y i))
    (fun i _ => mul_nonneg (hw i) (Real.sqrt_nonneg _))
    (fun i _ => mul_nonneg (hw i) (Real.sqrt_nonneg _)) (fun i _ => by
      rw [hroot, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sqrt_mul (hX i)]
      exact le_of_eq (by ring))
  have hXs := sqrt_average_sq_le w X hw hwSum hX
  have hYs := sqrt_average_sq_le w Y hw hwSum hY
  have hXm : 0 ≤ ∑ i, w i * X i := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hX i))
  have hYm : 0 ≤ ∑ i, w i * Y i := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hY i))
  have hprod := mul_le_mul hXs hYs (sq_nonneg _) hXm
  have hfour := pow_le_pow_left₀ (sq_nonneg _) hcs 2
  have hfour' : (∑ i, w i * (X i * Y i) ^ (1 / 4 : ℝ)) ^ 4 ≤
      (∑ i, w i * X i) * ∑ i, w i * Y i := by
    nlinarith
  have hrootPow : (((∑ i, w i * X i) * ∑ i, w i * Y i) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) =
      (∑ i, w i * X i) * ∑ i, w i * Y i := by
    simpa only [Nat.cast_ofNat, one_div] using
      Real.rpow_inv_natCast_pow (mul_nonneg hXm hYm) (by norm_num : (4 : ℕ) ≠ 0)
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
    (Real.rpow_nonneg (mul_nonneg hXm hYm) (1 / 4 : ℝ))
  rwa [hrootPow]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem expect_quarter_product_le (S : Finset ι) (hS : S.Nonempty) (X Y : ι → ℝ)
    (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i) {u v : ℝ}
    (hu : (𝔼 i ∈ S, X i) ≤ u) (hv : (𝔼 i ∈ S, Y i) ≤ v) :
    (𝔼 i ∈ S, (X i * Y i) ^ (1 / 4 : ℝ)) ≤ (u * v) ^ (1 / 4 : ℝ) := by
  have h := fourth_root_product_average_le_means (realUniformMass S) X Y
    (realUniformMass_nonneg S) (sum_realUniformMass hS) hX hY
  simp only [sum_uniformMass_mul_eq_expect] at h
  apply h.trans
  apply Real.rpow_le_rpow
  · exact mul_nonneg (Finset.expect_nonneg (fun i _ => hX i)) (Finset.expect_nonneg (fun i _ => hY i))
  · exact mul_le_mul hu hv (Finset.expect_nonneg (fun i _ => hY i))
      ((Finset.expect_nonneg (fun i _ => hX i)).trans hu)
  · norm_num

theorem expect_quarter_product_contraction (S : Finset ι) (hS : S.Nonempty) (X Y : ι → ℝ)
    {M c : ℝ} (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i) (hXM : ∀ i, X i ≤ M)
    (hmeanX : (𝔼 i ∈ S, X i) ≤ 1) (hmeanY : (𝔼 i ∈ S, Y i) ≤ 1)
    (hsecond : 1 + c ≤ 𝔼 i ∈ S, X i ^ 2) :
    (𝔼 i ∈ S, (X i * Y i) ^ (1 / 4 : ℝ)) ≤ 1 - c / (4 * (1 + Real.sqrt M) ^ 2) := by
  have h := fourth_root_product_average_le (realUniformMass S) X Y
    (realUniformMass_nonneg S) (sum_realUniformMass hS) hX hY hXM
    (by simpa only [sum_uniformMass_mul_eq_expect] using hmeanX)
    (by simpa only [sum_uniformMass_mul_eq_expect] using hmeanY)
    (by simpa only [sum_uniformMass_mul_eq_expect] using hsecond)
  simpa only [sum_uniformMass_mul_eq_expect] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem normalized_quarter_potential_contraction
    (S : Finset ι) (hS : S.Nonempty) (U V : ι → ℝ) {u v M c : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hU : ∀ i, 0 ≤ U i) (hV : ∀ i, 0 ≤ V i)
    (hmeanU : (𝔼 i ∈ S, U i) ≤ u) (hmeanV : (𝔼 i ∈ S, V i) ≤ v)
    (hcap : ∀ i, U i / u ≤ M)
    (hsecond : 1 + c ≤ 𝔼 i ∈ S, (U i / u) ^ 2) :
    (𝔼 i ∈ S, (U i * V i) ^ (1 / 4 : ℝ)) ≤
      (1 - c / (4 * (1 + Real.sqrt M) ^ 2)) * (u * v) ^ (1 / 4 : ℝ) := by
  have hX : ∀ i, 0 ≤ U i / u := fun i => div_nonneg (hU i) hu.le
  have hY : ∀ i, 0 ≤ V i / v := fun i => div_nonneg (hV i) hv.le
  have hxmean : (𝔼 i ∈ S, U i / u) ≤ 1 := by
    rw [← Finset.expect_div]
    exact (div_le_one hu).mpr hmeanU
  have hymean : (𝔼 i ∈ S, V i / v) ≤ 1 := by
    rw [← Finset.expect_div]
    exact (div_le_one hv).mpr hmeanV
  have h := expect_quarter_product_contraction S hS (fun i => U i / u) (fun i => V i / v)
    hX hY hcap hxmean hymean hsecond
  have hpoint (i : ι) : (U i * V i) ^ (1 / 4 : ℝ) =
      (u * v) ^ (1 / 4 : ℝ) * ((U i / u) * (V i / v)) ^ (1 / 4 : ℝ) := by
    rw [← Real.mul_rpow (mul_nonneg hu.le hv.le) (mul_nonneg (hX i) (hY i))]
    congr 1
    field_simp
  calc
    _ = (u * v) ^ (1 / 4 : ℝ) *
        (𝔼 i ∈ S, ((U i / u) * (V i / v)) ^ (1 / 4 : ℝ)) := by
      simp_rw [hpoint]
      rw [← Finset.mul_expect]
    _ ≤ (u * v) ^ (1 / 4 : ℝ) * (1 - c / (4 * (1 + Real.sqrt M) ^ 2)) :=
      mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (mul_nonneg hu.le hv.le) _)
    _ = _ := mul_comm _ _

theorem normalized_quarter_potential_contraction_either
    (S : Finset ι) (hS : S.Nonempty) (U V : ι → ℝ) {u v M c : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hU : ∀ i, 0 ≤ U i) (hV : ∀ i, 0 ≤ V i)
    (hmeanU : (𝔼 i ∈ S, U i) ≤ u) (hmeanV : (𝔼 i ∈ S, V i) ≤ v)
    (hcapU : ∀ i, U i / u ≤ M) (hcapV : ∀ i, V i / v ≤ M)
    (hsecond : (1 + c ≤ 𝔼 i ∈ S, (U i / u) ^ 2) ∨
      (1 + c ≤ 𝔼 i ∈ S, (V i / v) ^ 2)) :
    (𝔼 i ∈ S, (U i * V i) ^ (1 / 4 : ℝ)) ≤
      (1 - c / (4 * (1 + Real.sqrt M) ^ 2)) * (u * v) ^ (1 / 4 : ℝ) := by
  rcases hsecond with hsecond | hsecond
  · exact normalized_quarter_potential_contraction S hS U V hu hv hU hV hmeanU hmeanV hcapU hsecond
  · simpa only [mul_comm] using
      normalized_quarter_potential_contraction S hS V U hv hu hV hU hmeanV hmeanU hcapV hsecond

theorem quarter_contraction_factor_bounds {M c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    3 / 4 ≤ 1 - c / (4 * (1 + Real.sqrt M) ^ 2) ∧
      1 - c / (4 * (1 + Real.sqrt M) ^ 2) < 1 := by
  have hden : 0 < 4 * (1 + Real.sqrt M) ^ 2 := by positivity
  have hratio : c / (4 * (1 + Real.sqrt M) ^ 2) ≤ 1 / 4 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [Real.sqrt_nonneg M, sq_nonneg (Real.sqrt M)]
  have hpos := div_pos hc hden
  constructor <;> linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem parent_cell_potential_le {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (B L : Finset G) (hB : B.Nonempty) (hL : L.Nonempty)
    (f g : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0) :
    (𝔼 x ∈ B, 𝔼 y ∈ B, (cellAverage L f x * cellAverage L g y) ^ (1 / 4 : ℝ)) ≤
      ((𝔼 x ∈ B, f x) * (𝔼 y ∈ B, g y)) ^ (1 / 4 : ℝ) := by
  have hfmean := expect_cellAverage_comp_le B L hL f hf hfsupport id Function.injective_id
  have hgmean := expect_cellAverage_comp_le B L hL g hg hgsupport id Function.injective_id
  have h := expect_quarter_product_le (B ×ˢ B) (hB.product hB)
    (fun z => cellAverage L f z.1) (fun z => cellAverage L g z.2)
    (fun z => cellAverage_nonneg L f hf z.1) (fun z => cellAverage_nonneg L g hg z.2)
    (u := 𝔼 x ∈ B, f x) (v := 𝔼 y ∈ B, g y)
    (by simpa only [id_eq, Finset.expect_product, Finset.expect_const hB] using hfmean)
    (by simpa only [id_eq, Finset.expect_product, Finset.expect_const hB] using hgmean)
  simpa only [Finset.expect_product] using h

theorem normalized_cell_cap {a u u₀ c₀ K : ℝ}
    (hu : 0 < u) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hlower : c₀ * u ≤ u₀) (hcell : a ≤ K * u) : a / u₀ ≤ K / c₀ := by
  have hu₀ : 0 < u₀ := (mul_pos hc₀ hu).trans_le hlower
  apply (div_le_div_iff₀ hu₀ hc₀).mpr
  nlinarith [mul_le_mul_of_nonneg_left hlower hK,
    mul_le_mul_of_nonneg_right hcell hc₀.le]

theorem small_ratio_quarter_potential_le {a b u v c₀ K : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hc₀ : 0 ≤ c₀) (hK : 0 ≤ K) (hau : a ≤ c₀ * u) (hbv : b ≤ K * v)
    (hsmall : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2) :
    (a * b) ^ (1 / 4 : ℝ) ≤ (u * v) ^ (1 / 4 : ℝ) / 2 := by
  have hab : a * b ≤ (c₀ * K) * (u * v) := by
    nlinarith [mul_le_mul hau hbv hb (mul_nonneg hc₀ hu)]
  calc
    _ ≤ ((c₀ * K) * (u * v)) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (mul_nonneg ha hb) hab (by norm_num)
    _ = (c₀ * K) ^ (1 / 4 : ℝ) * (u * v) ^ (1 / 4 : ℝ) :=
      Real.mul_rpow (mul_nonneg hc₀ hK) (mul_nonneg hu hv)
    _ ≤ (1 / 2) * (u * v) ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg (mul_nonneg hu hv) _)
    _ = _ := by ring

theorem combine_matched_potential_contractions {A B Phi rho : ℝ}
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (hsmall : A ≤ Phi / 2) (htotal : A + B ≤ Phi) :
    A + rho * B ≤ ((1 + rho) / 2) * Phi := by
  nlinarith [mul_le_mul_of_nonneg_left htotal hrho,
    mul_le_mul_of_nonneg_left hsmall (sub_nonneg.mpr hrho1)]

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def replacementPotential (D Q C : Finset G) (f g : G → ℝ) : ℝ :=
  𝔼 z ∈ Q, ((𝔼 x ∈ D, f x) * cellAverage C g z) ^ (1 / 4 : ℝ)

theorem replacementPotential_nonneg (D Q C : Finset G) (f g : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    0 ≤ replacementPotential D Q C f g := by
  apply Finset.expect_nonneg
  intro z _
  exact Real.rpow_nonneg
    (mul_nonneg (Finset.expect_nonneg (fun x _ => hf x)) (cellAverage_nonneg C g hg z)) _

variable [Fintype G] [DecidableEq G]

theorem replacementPotential_le (D Q C : Finset G) (hQ : Q.Nonempty) (hC : C.Nonempty)
    (f g : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hgsupport : ∀ x, x ∉ Q → g x = 0) :
    replacementPotential D Q C f g ≤
      ((𝔼 x ∈ D, f x) * (𝔼 y ∈ Q, g y)) ^ (1 / 4 : ℝ) := by
  apply expect_quarter_product_le Q hQ (fun _ => 𝔼 x ∈ D, f x) (cellAverage C g)
  · intro _
    exact Finset.expect_nonneg (fun x _ => hf x)
  · exact cellAverage_nonneg C g hg
  · exact (Finset.expect_const hQ _).le
  · exact expect_cellAverage_comp_le Q C hC g hg hgsupport id Function.injective_id

omit [Fintype G] in
theorem replacementPotential_eq_cell_means (D Q C : Finset G) (f g : G → ℝ) :
    replacementPotential D Q C f g =
      𝔼 z ∈ Q, ((𝔼 x ∈ D, f x) *
        (𝔼 y ∈ C.image (fun t => z + t), g y)) ^ (1 / 4 : ℝ) := by
  apply Finset.expect_congr rfl
  intro z _
  rw [Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)]
  rfl

end Erdos3.CellRefinement

end

end OAI
