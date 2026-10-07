/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.NativeLocalPivotVerticalBudget
import OAI.Combinatorics.Progressions.Fourier.WeightedTranslationTwistedCentralFrequency

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exp_scaled_norm_le_one {b : ℝ} {z : ℂ} (hz : ‖z‖ ≤ Real.exp b) :
    ‖(Real.exp (-b) : ℂ) * z‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-b) * Real.exp b := mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

theorem finite_double_normalization {X : Type*} (S : Finset X) (f g : X → ℂ) (b : ℝ)
    (hcorr : Real.exp (-b) ≤ ‖𝔼 x ∈ S, f x * g x‖) :
    Real.exp (-(3 * b)) ≤ ‖𝔼 x ∈ S,
      ((Real.exp (-b) : ℂ) * f x) * ((Real.exp (-b) : ℂ) * g x)‖ := by
  have hmean : (𝔼 x ∈ S, ((Real.exp (-b) : ℂ) * f x) * ((Real.exp (-b) : ℂ) * g x)) =
      ((Real.exp (-b) : ℂ) * (Real.exp (-b) : ℂ)) * (𝔼 x ∈ S, f x * g x) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [hmean, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-(3 * b)) = (Real.exp (-b) * Real.exp (-b)) * Real.exp (-b) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcorr (by positivity)

theorem finite_remove_normalization {X : Type*} (S : Finset X) (f g : X → ℂ)
    {b rho : ℝ} (hb : 0 ≤ b)
    (hcorr : rho ≤ ‖𝔼 x ∈ S, ((Real.exp (-b) : ℂ) * f x) * g x‖) :
    rho ≤ ‖𝔼 x ∈ S, f x * g x‖ := by
  have hmean : (𝔼 x ∈ S, ((Real.exp (-b) : ℂ) * f x) * g x) =
      (Real.exp (-b) : ℂ) * (𝔼 x ∈ S, f x * g x) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [hmean, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at hcorr
  exact hcorr.trans (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hb)))

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

private theorem weighted_fixed_choices {Ω K : Type*} {I : K → Type*}
    [Fintype Ω] [Fintype K] [∀ k, Fintype (I k)]
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (rel : ∀ (_ : Ω) (k : K), I k → Prop)
    (hex : ∀ a ∈ H, ∀ k, ∃ i, rel a k i) {b : ℝ}
    (hcard : ∀ k, (Fintype.card (I k) : ℝ) ≤ Real.exp b) :
    ∃ (choice : ∀ k, I k) (S : Finset Ω), S ⊆ H ∧ 0 < outer.mass S ∧
      Real.exp (-b * Fintype.card K) * outer.mass H ≤ outer.mass S ∧
      ∀ a ∈ S, ∀ k, rel a k (choice k) := by
  classical
  have hHne : H.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he] at hH
    simp only [FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hH
  obtain ⟨a0, ha0⟩ := hHne
  let : ∀ k, Nonempty (I k) := fun k => ⟨(hex a0 ha0 k).choose⟩
  let code : Ω → ∀ k, I k := fun a k =>
    if ha : a ∈ H then (hex a ha k).choose else (hex a0 ha0 k).choose
  have hcode (a : Ω) (ha : a ∈ H) (k : K) : rel a k (code a k) := by
    simpa only [code, dite_eq_left ha] using (hex a ha k).choose_spec
  have hc : (Fintype.card (∀ k, I k) : ℝ) ≤ Real.exp (b * Fintype.card K) := by
    rw [Fintype.card_pi, Nat.cast_prod]
    calc
      _ ≤ ∏ _k : K, Real.exp b :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun k _ => hcard k)
      _ = (Real.exp b) ^ Fintype.card K := by simp
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  obtain ⟨choice, hchoice⟩ := outer.exists_code_fiber_mass H code
  let S := H.filter (fun a => code a = choice)
  have hmass : Real.exp (-b * Fintype.card K) * outer.mass H ≤ outer.mass S := by
    calc
      _ = outer.mass H / Real.exp (b * Fintype.card K) := by
        rw [show -b * (Fintype.card K : ℝ) = -(b * Fintype.card K) by ring,
          Real.exp_neg, div_eq_mul_inv, mul_comm]
      _ ≤ outer.mass H / Fintype.card (∀ k, I k) :=
        div_le_div_of_nonneg_left hH.le (by positivity) hc
      _ ≤ _ := hchoice
      _ = outer.mass S := by
        congr 1
        ext a
        simp only [S, Finset.mem_filter]
  refine ⟨choice, S, Finset.filter_subset _ _, (mul_pos (Real.exp_pos _) hH).trans_le hmass,
    hmass, ?_⟩
  intro a ha k
  obtain ⟨haH, he⟩ := Finset.mem_filter.mp ha
  rw [← he]
  exact hcode a haH k

theorem exists_weighted_native_vertical_partners
    {Ω K T σ : Type*} [Fintype Ω] [Fintype K] {L : K → Type*}
    [∀ k, LieRing (L k)] [∀ k, LieAlgebra ℚ (L k)] {s : ℕ} {d : K → ℕ}
    [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L k)] [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L k)]
    [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L k)] [∀ k, T2Space (ℝ ⊗[ℚ] L k)]
    (D : ∀ k, RationalFilteredNilmanifold (L k) s (d k)) {w : σ → ℕ}
    (Q : ∀ k, (D k).Niltest w)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (S : Ω → K → Finset T) (point : Ω → T → σ → ℤ)
    (weight : Ω → K → T → ℂ) {p q delta : ℝ}
    (hq : 0 ≤ q) (hpq : p ≤ q) (hdelta : 0 < delta)
    (hprecision : (delta / 2)⁻¹ ≤ Real.exp q)
    (hQ : ∀ k, (Q k).ComplexityLE p) (hcap : ∀ k, ((Q k).normBound : ℝ) ≤ 1)
    (hS : ∀ a ∈ H, ∀ k, (S a k).Nonempty)
    (hweight : ∀ a ∈ H, ∀ k t, t ∈ S a k → ‖weight a k t‖ ≤ 1)
    (hcorr : ∀ a ∈ H, ∀ k, delta ≤
      ‖𝔼 t ∈ S a k, weight a k t * (Q k).eval (point a t)‖) :
    ∃ (freq : ∀ k, L k →ₗ[ℚ] ℚ) (V : ∀ k, (D k).Niltest w) (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      Real.exp (-verticalDecompositionBudget q * Fintype.card K) * outer.mass H ≤
        outer.mass retained ∧
      (∀ k, (V k).ComplexityLE p ∧ (V k).orbit = (Q k).orbit ∧
        (V k).normBound = (Q k).normBound ∧ (V k).lipBound = (Q k).lipBound ∧
        ((V k).normBound : ℝ) ≤ 1) ∧
      (∀ k i, rationalLogHeight (freq k ((D k).basis i)) ≤ verticalDecompositionBudget q) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s → ∀ x,
        (V k).observable (z • x) =
          character ((realifyFunctional (freq k) z.coord : ℝ) : CircleFourier.Circle) *
            (V k).observable x) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s →
        z ∈ (D k).realLattice → ∃ n : ℤ, realifyFunctional (freq k) z.coord = n) ∧
      (∀ k (z : (D k).RealGroup) (c : ℂ),
        (∀ x, (Q k).observable (z • x) = c * (Q k).observable x) →
        ∀ x, (V k).observable (z • x) = c * (V k).observable x) ∧
      ∀ a ∈ retained, ∀ k, delta / (2 * Real.exp (verticalDecompositionBudget q)) ≤
        ‖𝔼 t ∈ S a k, weight a k t * (V k).eval (point a t)‖ := by
  classical
  choose I instI freq V hcard hheight hcert hvert hint hpres hobs happrox using
    fun k => (Q k).exists_vertical_decomposition_preserving_bounds_and_characters
      hq ((hQ k).mono hpq) (by positivity : 0 < delta / 2) hprecision
  let : ∀ k, Fintype (I k) := instI
  let rel : ∀ (_ : Ω) (k : K), I k → Prop := fun a k i =>
    delta / (2 * Real.exp (verticalDecompositionBudget q)) ≤
      ‖𝔼 t ∈ S a k, weight a k t * (V k i).eval (point a t)‖
  have hex (a : Ω) (ha : a ∈ H) (k : K) : ∃ i, rel a k i := by
    have hh := exists_correlating_summand (hS a ha k) (weight a k)
      (fun t => star ((Q k).eval (point a t)))
      (fun i t => star ((V k i).eval (point a t))) hdelta (Real.exp_pos _)
      (hcard k) (hweight a ha k)
    apply (by simpa only [finiteCorrelation, star_star, rel] using hh)
    · intro t _
      simpa only [← star_sum, ← star_sub, norm_star] using happrox k (point a t)
    · simpa only [finiteCorrelation, star_star] using hcorr a ha k
  obtain ⟨choice, retained, hsub, hpos, hmass, hselected⟩ :=
    weighted_fixed_choices outer H hH rel hex hcard
  have hnonzero (k : K) : ∃ x, (V k (choice k)).observable x ≠ 0 := by
    by_contra! hz
    have hne : retained.Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty.mp he] at hpos
      simp only [FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hpos
    obtain ⟨a, ha⟩ := hne
    have he := hselected a ha k
    have heval (t : T) : (V k (choice k)).eval (point a t) = 0 := hz _
    change delta / (2 * Real.exp (verticalDecompositionBudget q)) ≤ _ at he
    simp only [heval, mul_zero, Finset.expect_const_zero, norm_zero] at he
    exact (not_le_of_gt (by positivity : 0 < delta / (2 * Real.exp
      (verticalDecompositionBudget q)))) he
  refine ⟨fun k => freq k (choice k), fun k => V k (choice k), retained,
    hsub, hpos, hmass, ?_, fun k => hheight k (choice k), fun k => hvert k (choice k),
    fun k => hint k (choice k) (hnonzero k), fun k z c hc x => hpres k z c hc (choice k) x,
    hselected⟩
  intro k
  obtain ⟨_, ho, hn, hl⟩ := hcert k (choice k)
  have hcOriginal : (V k (choice k)).ComplexityLE p := by
    refine ⟨(hQ k).1, ?_⟩
    rw [hn, hl]
    exact (hQ k).2
  exact ⟨hcOriginal, ho, hn, hl, hn ▸ hcap k⟩

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

private theorem norm_expect_scaled_product {T : Type*} (S : Finset T)
    (c : ℝ) (hc : 0 ≤ c) (f g : T → ℂ) :
    ‖𝔼 t ∈ S, ((c : ℂ) * f t) * g t‖ = c * ‖𝔼 t ∈ S, f t * g t‖ := by
  have he : (𝔼 t ∈ S, ((c : ℂ) * f t) * g t) =
      (c : ℂ) * (𝔼 t ∈ S, f t * g t) := by
    simp only [mul_assoc, Finset.mul_expect]
  rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]

theorem exists_localPivot_weighted_native_vertical_partners
    {Ω K T σ τ : Type*} [Fintype Ω] [Fintype K]
    {L : K → Type*} {Llocal : Ω → K → Type*}
    [∀ k, LieRing (L k)] [∀ k, LieAlgebra ℚ (L k)]
    [∀ a k, LieRing (Llocal a k)] [∀ a k, LieAlgebra ℚ (Llocal a k)]
    {s : ℕ} {d : K → ℕ} {sLocal dLocal : Ω → K → ℕ}
    [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L k)]
    [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L k)]
    [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L k)] [∀ k, T2Space (ℝ ⊗[ℚ] L k)]
    [∀ a k, TopologicalSpace (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, IsTopologicalAddGroup (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, ContinuousSMul ℝ (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, T2Space (ℝ ⊗[ℚ] Llocal a k)]
    (D : ∀ k, RationalFilteredNilmanifold (L k) s (d k))
    (Dlocal : ∀ a k, RationalFilteredNilmanifold (Llocal a k) (sLocal a k) (dLocal a k))
    {w : σ → ℕ} {wLocal : τ → ℕ}
    (Q : ∀ k, (D k).Niltest w) (P : ∀ a k, (Dlocal a k).Niltest wLocal)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (S : Ω → K → Finset T)
    (pointAmbient : Ω → T → σ → ℤ) (pointLocal : Ω → K → T → τ → ℤ)
    (twist : Ω → K → T → ℂ) {pNative pLocal r q : ℝ}
    (hpLocal : 0 ≤ pLocal) (hr : 0 ≤ r) (hpq : pNative ≤ q)
    (hprecision : pLocal + r + 1 ≤ q)
    (hQ : ∀ k, (Q k).ComplexityLE pNative)
    (hcap : ∀ k, ((Q k).normBound : ℝ) ≤ 1)
    (hP : ∀ a ∈ H, ∀ k, (P a k).ComplexityLE pLocal)
    (htwist : ∀ a ∈ H, ∀ k t, t ∈ S a k → ‖twist a k t‖ ≤ 1)
    (hcorr : ∀ a ∈ H, ∀ k, Real.exp (-r) ≤
      ‖𝔼 t ∈ S a k,
        ((P a k).eval (pointLocal a k t) * twist a k t) * (Q k).eval (pointAmbient a t)‖) :
    ∃ (freq : ∀ k, L k →ₗ[ℚ] ℚ) (V : ∀ k, (D k).Niltest w) (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      Real.exp (-verticalDecompositionBudget q * Fintype.card K) * outer.mass H ≤
        outer.mass retained ∧
      (∀ k, (V k).ComplexityLE pNative ∧ (V k).orbit = (Q k).orbit ∧
        (V k).normBound = (Q k).normBound ∧ (V k).lipBound = (Q k).lipBound ∧
        ((V k).normBound : ℝ) ≤ 1) ∧
      (∀ k i, rationalLogHeight (freq k ((D k).basis i)) ≤ verticalDecompositionBudget q) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s → ∀ x,
        (V k).observable (z • x) =
          character ((realifyFunctional (freq k) z.coord : ℝ) : CircleFourier.Circle) *
            (V k).observable x) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s →
        z ∈ (D k).realLattice → ∃ n : ℤ, realifyFunctional (freq k) z.coord = n) ∧
      (∀ k (z : (D k).RealGroup) (c : ℂ),
        (∀ x, (Q k).observable (z • x) = c * (Q k).observable x) →
        ∀ x, (V k).observable (z • x) = c * (V k).observable x) ∧
      ∀ a ∈ retained, ∀ k, Real.exp (-r) / (2 * Real.exp (verticalDecompositionBudget q)) ≤
        ‖𝔼 t ∈ S a k,
          ((P a k).eval (pointLocal a k t) * twist a k t) * (V k).eval (pointAmbient a t)‖ := by
  classical
  let weight : Ω → K → T → ℂ := fun a k t =>
    (Real.exp (-pLocal) : ℂ) * ((P a k).eval (pointLocal a k t) * twist a k t)
  have hweight (a : Ω) (ha : a ∈ H) (k : K) (t : T) (ht : t ∈ S a k) :
      ‖weight a k t‖ ≤ 1 := by
    change ‖((Real.exp (-pLocal) : ℂ) *
      ((P a k).eval (pointLocal a k t) * twist a k t))‖ ≤ 1
    rw [← mul_assoc, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (exp_scaled_norm_le_one ((P a k).eval_budget (hP a ha k) _))).trans
      (htwist a ha k t ht)
  have hS (a : Ω) (ha : a ∈ H) (k : K) : (S a k).Nonempty := by
    by_contra hn
    have hh := hcorr a ha k
    rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hh
    simp only [Finset.expect_empty, norm_zero] at hh
    exact (not_le_of_gt (Real.exp_pos _)) hh
  have hnormalized (a : Ω) (ha : a ∈ H) (k : K) :
      Real.exp (-pLocal) * Real.exp (-r) ≤
        ‖𝔼 t ∈ S a k, weight a k t * (Q k).eval (pointAmbient a t)‖ := by
    change _ ≤ ‖𝔼 t ∈ S a k,
      ((Real.exp (-pLocal) : ℂ) * ((P a k).eval (pointLocal a k t) * twist a k t)) *
        (Q k).eval (pointAmbient a t)‖
    rw [norm_expect_scaled_product _ _ (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hcorr a ha k) (Real.exp_nonneg _)
  obtain ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, hint,
      hpres, hselected⟩ := exists_weighted_native_vertical_partners D Q outer H hH S
    pointAmbient weight (by linarith : 0 ≤ q) hpq (by positivity)
    (nativeLocalPivotVertical_inverse_precision_le_exp hprecision) hQ hcap hS hweight hnormalized
  refine ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, hint, hpres, ?_⟩
  intro a ha k
  have hs := hselected a ha k
  change (Real.exp (-pLocal) * Real.exp (-r)) /
      (2 * Real.exp (verticalDecompositionBudget q)) ≤
    ‖𝔼 t ∈ S a k,
      ((Real.exp (-pLocal) : ℂ) * ((P a k).eval (pointLocal a k t) * twist a k t)) *
        (V k).eval (pointAmbient a t)‖ at hs
  rw [norm_expect_scaled_product _ _ (Real.exp_nonneg _), mul_div_assoc] at hs
  exact (mul_le_mul_iff_right₀ (Real.exp_pos (-pLocal))).mp
    (by simpa only [mul_comm] using hs)

end Erdos3

end

end OAI
