import GRHArticle.ProgressionFree.PolynomialTwoPrimeFibers
import GRHArticle.ProgressionFree.PolynomialRoughWeightLimit
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# From the finite triangle deficit to the polynomial density bound

The rough layer for two linear primes has normalized count `(1-z)^2`,
where `z = 1/q`. The extra `1-z` in the degree-ball convolution cancels
the geometric factor from summing the Roth numbers into row bounds.
-/

namespace GRHArticle.ProgressionFree

open Filter Topology Polynomial
open scoped Classical BigOperators

/-- The single-prime Roth series `U_q`, with `z = 1/q`. -/
noncomputable def polynomialOnePrimeRothBound (F : Type*) [Field F] [Fintype F] : ℝ :=
  let z := (Fintype.card F : ℝ)⁻¹
  (1-z)^2 * ∑' k : ℕ, (rothNumberNat (k+1) : ℝ) * z^k

private theorem summable_roth_weight {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) :
    Summable (fun t : ℕ ↦ (rothNumberNat (t+1) : ℝ) * z^t) := by
  have hn : ‖z‖ < 1 := by simpa [Real.norm_of_nonneg h₀] using h₁
  have hₐ := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have hᵦ := summable_geometric_of_lt_one h₀ h₁
  have hsum : Summable (fun t : ℕ ↦ ((t:ℝ)+1) * z^t) := by
    simpa only [pow_one, add_mul, one_mul] using hₐ.add hᵦ
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun t ↦ ?_) hsum
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg h₀ _)
  exact_mod_cast rothNumberNat_le (t+1)

/-- Successive interval Roth numbers increase by at most one. -/
theorem rothNumberNat_increment_le_one (n : ℕ) :
    rothNumberNat (n+1) - rothNumberNat n ≤ 1 := by
  have h := rothNumberNat_add_le n 1
  have h₁ := rothNumberNat_le 1
  omega

/-- The series of successive Roth increments converges for `0 ≤ z < 1`. -/
theorem summable_rothIncrement_weight {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) :
    Summable (fun t : ℕ ↦ ((rothNumberNat (t+1) - rothNumberNat t : ℕ) : ℝ) * z^t) := by
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun t ↦ ?_)
    (summable_geometric_of_lt_one h₀ h₁)
  have h := rothNumberNat_increment_le_one t
  exact mul_le_of_le_one_left (pow_nonneg h₀ _) (by exact_mod_cast h)

/-- Summation by parts converts the Roth series to successive increments. -/
theorem one_sub_mul_tsum_rothIncrement {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) :
    (1-z) * (∑' t : ℕ, ((rothNumberNat (t+1) - rothNumberNat t : ℕ) : ℝ) * z^t) =
      (1-z)^2 * (∑' t : ℕ, (rothNumberNat (t+1) : ℝ) * z^t) := by
  let f (t : ℕ) := (rothNumberNat (t+1) : ℝ) * z^t
  let g (t : ℕ) := (rothNumberNat t : ℝ) * z^t
  have hf : Summable f := summable_roth_weight h₀ h₁
  have hshift (t : ℕ) : g (t+1) = z * f t := by
    dsimp [g,f]
    rw [pow_succ]
    ring
  have hg : Summable g := by
    apply (summable_nat_add_iff 1).mp
    simpa only [hshift] using hf.mul_left z
  have hgSum : (∑' t, g t) = z * ∑' t, f t := by
    rw [hg.tsum_eq_zero_add]
    simp_rw [show g 0 = 0 by simp [g], zero_add, hshift, tsum_mul_left]
  have hterm (t : ℕ) : ((rothNumberNat (t+1) - rothNumberNat t : ℕ) : ℝ) * z^t = f t - g t := by
    rw [Nat.cast_sub (rothNumberNat.monotone (Nat.le_succ t)), sub_mul]
  simp_rw [hterm]
  rw [hf.tsum_sub hg, hgSum]
  change (1-z) * ((∑' t, f t) - z * (∑' t, f t)) = (1-z)^2 * (∑' t, f t)
  ring

/-- The single-prime Roth bound in the article's successive-increment form. -/
theorem polynomialOnePrimeRothBound_eq_increment_series
    (F : Type*) [Field F] [Fintype F] :
    polynomialOnePrimeRothBound F =
      let z := (Fintype.card F : ℝ)⁻¹
      (1-z) * ∑' t : ℕ, ((rothNumberNat (t+1) - rothNumberNat t : ℕ) : ℝ) * z^t := by
  have hq : 1 < (Fintype.card F : ℝ) := by
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
  exact (one_sub_mul_tsum_rothIncrement (by positivity) (inv_lt_one_of_one_lt₀ hq)).symm

/-- The one-prime bound with the degree index starting at one. -/
theorem polynomialOnePrimeRothBound_eq_article_series
    (F : Type*) [Field F] [Fintype F] :
    polynomialOnePrimeRothBound F =
      let q := (Fintype.card F : ℝ)
      (q-1) * ∑' t : ℕ, ((rothNumberNat (t+1) - rothNumberNat t : ℕ) : ℝ) * q⁻¹^(t+1) := by
  rw [polynomialOnePrimeRothBound_eq_increment_series]
  let q := (Fintype.card F : ℝ)
  have hq : q ≠ 0 := by dsimp [q]; positivity
  change (1-q⁻¹) * (∑' t : ℕ, ((rothNumberNat (t+1) - rothNumberNat t : ℕ) : ℝ) * q⁻¹^t) =
    (q-1) * ∑' t : ℕ, ((rothNumberNat (t+1) - rothNumberNat t : ℕ) : ℝ) * q⁻¹^(t+1)
  simp_rw [pow_succ', ← mul_left_comm q⁻¹, tsum_mul_left]
  field_simp [hq]

private theorem twoPrimeRows_weight_eq_convolution (z : ℝ) (t : ℕ) :
    (twoPrimeRothRows (t+1) : ℝ) * z^t =
      ∑ i ∈ Finset.range (t+1), ((rothNumberNat (i+1) : ℝ) * z^i) * z^(t-i) := by
  unfold twoPrimeRothRows
  have harg (i : ℕ) (hi : i ∈ Finset.range (t+1)) : t+1-i = (t+1-1-i)+1 := by
    have := Finset.mem_range.mp hi
    omega
  rw [Finset.sum_congr rfl (fun i hi ↦ congrArg rothNumberNat (harg i hi)),
    Finset.sum_range_reflect (fun i ↦ rothNumberNat (i+1)) (t+1), Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]

private theorem twoPrimeRows_series {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) :
    Summable (fun t ↦ (twoPrimeRothRows (t+1) : ℝ) * z^t) ∧
      (∑' t, (twoPrimeRothRows (t+1) : ℝ) * z^t) =
        (∑' t, (rothNumberNat (t+1) : ℝ) * z^t) * (1-z)⁻¹ := by
  have hf := summable_roth_weight h₀ h₁
  have hg := summable_geometric_of_lt_one h₀ h₁
  have hfg := hf.mul_of_nonneg hg (fun _ ↦ by positivity) (fun _ ↦ by positivity)
  simp_rw [twoPrimeRows_weight_eq_convolution]
  exact ⟨summable_sum_mul_range_of_summable_mul hfg,
    (hf.tsum_mul_tsum_eq_tsum_sum_range hg hfg).symm.trans (by rw [tsum_geometric_of_lt_one h₀ h₁])⟩

private theorem shiftedGeometric_series {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) (b : ℕ) :
    Summable (fun t : ℕ ↦ if b ≤ t then z^t else 0) ∧
      (∑' t : ℕ, if b ≤ t then z^t else 0) = z^b * (1-z)⁻¹ := by
  let a : ℕ → ℝ := fun t ↦ if b ≤ t then z^t else 0
  have hgs := summable_geometric_of_lt_one h₀ h₁
  have ha : Summable a := Summable.of_nonneg_of_le
    (fun t ↦ by dsimp [a]; split <;> positivity)
    (fun t ↦ by
      dsimp [a]
      split
      · rfl
      · exact pow_nonneg h₀ _) hgs
  refine ⟨ha, ?_⟩
  change ∑' t, a t = _
  rw [← ha.sum_add_tsum_nat_add b]
  have hzero : ∑ t ∈ Finset.range b, a t = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp [a, not_le_of_gt (Finset.mem_range.mp ht)]
  rw [hzero, zero_add]
  have htail (t : ℕ) : a (t+b) = z^b * z^t := by
    rw [show a (t+b) = z^(t+b) by simp [a], Nat.add_comm, pow_add]
  simp_rw [htail]
  rw [tsum_mul_left, tsum_geometric_of_lt_one h₀ h₁]

private theorem twoPrimePenalty_series {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) :
    Summable (fun t ↦ (twoPrimePenalty (t+1) : ℝ) * z^t) ∧
      (∑' t, (twoPrimePenalty (t+1) : ℝ) * z^t) =
        (z^8+z^19+z^29) * (1-z)⁻¹ := by
  have h8 := shiftedGeometric_series h₀ h₁ 8
  have h19 := shiftedGeometric_series h₀ h₁ 19
  have h29 := shiftedGeometric_series h₀ h₁ 29
  have hterm (t : ℕ) : (twoPrimePenalty (t+1) : ℝ) * z^t =
      ((if 8 ≤ t then z^t else 0) + (if 19 ≤ t then z^t else 0)) +
        (if 29 ≤ t then z^t else 0) := by
    unfold twoPrimePenalty
    simp only [show (9 ≤ t+1) ↔ (8 ≤ t) by omega, show (20 ≤ t+1) ↔ (19 ≤ t) by omega,
      show (30 ≤ t+1) ↔ (29 ≤ t) by omega]
    split_ifs <;> push_cast <;> ring
  simp_rw [hterm]
  refine ⟨(h8.1.add h19.1).add h29.1, ?_⟩
  rw [(h8.1.add h19.1).tsum_add h29.1, h8.1.tsum_add h19.1, h8.2, h19.2, h29.2]
  ring

private theorem twoPrimeFiberMaximum_series (ht : TwoPrimeTriangleBound)
    {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) :
    Summable (fun t ↦ (twoPrimeFiberMaximum t : ℝ) * z^t) ∧
      (1-z)^3 * (∑' t, (twoPrimeFiberMaximum t : ℝ) * z^t) =
        (1-z)^2 * (∑' t, (rothNumberNat (t+1) : ℝ) * z^t) -
          (1-z)^2 * (z^8+z^19+z^29) := by
  have hrows := twoPrimeRows_series h₀ h₁
  have hpen := twoPrimePenalty_series h₀ h₁
  have hle (t : ℕ) : twoPrimePenalty (t+1) ≤ twoPrimeRothRows (t+1) := by
    simpa using ht (L := t+1) ∅ (by simp) (by simp) (by simp)
  have hterm (t : ℕ) : (twoPrimeFiberMaximum t : ℝ) * z^t =
      (twoPrimeRothRows (t+1) : ℝ) * z^t - (twoPrimePenalty (t+1) : ℝ) * z^t := by
    rw [twoPrimeFiberMaximum, Nat.cast_sub (hle t), sub_mul]
  simp_rw [hterm]
  refine ⟨hrows.1.sub hpen.1, ?_⟩
  rw [hrows.1.tsum_sub hpen.1, hrows.2, hpen.2]
  have hz : 1-z ≠ 0 := by linarith
  field_simp [hz]

variable {F : Type*} [Field F] [Fintype F]

/-- The normalized rough count for two distinct chosen monic linears. -/
theorem tendsto_twoPrimeExcludingLayer {P Q : F[X]} (hPQ : P ≠ Q)
    (hmP : P.Monic) (hmQ : Q.Monic) (hiP : Irreducible P) (hiQ : Irreducible Q)
    (hP : P.natDegree = 1) (hQ : Q.natDegree = 1) :
    Tendsto (fun n ↦ ((primeExcludingLayer {P,Q} n).card : ℝ) / (Fintype.card F : ℝ)^n)
      atTop (𝓝 ((1-(Fintype.card F : ℝ)⁻¹)^2)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hS : ∀ p ∈ ({P,Q} : Finset F[X]), p.Monic ∧ Irreducible p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact ⟨hmP, hiP⟩
    · rcases Finset.mem_singleton.mp hp with rfl
      exact ⟨hmQ, hiQ⟩
  have hd : ∑ p ∈ ({P,Q} : Finset F[X]), p.natDegree ≤ n := by
    simpa [hPQ, hP, hQ] using hn
  symm
  simpa [hPQ, hP, hQ, pow_two] using normalized_primeExcludingLayer {P,Q} hS hd

/-- The two-prime bound for one polynomial-ratio progression-free set. -/
theorem limsup_polynomialBallProportion_le_twoPrime_of_triangle
    {E : Set F[X]} (hE : PolynomialRatioThreeGPFree E) (ht : TwoPrimeTriangleBound) :
    limsup (polynomialBallProportion E) atTop ≤
      let z := (Fintype.card F : ℝ)⁻¹
      polynomialOnePrimeRothBound F - (1-z)^2*(z^8+z^19+z^29) := by
  let P : F[X] := X
  let Q : F[X] := X-C 1
  have hPQ : P ≠ Q := by
    intro h
    have hc := congrArg (fun f : F[X] ↦ f.coeff 0) h
    simp [P,Q] at hc
  have hP : P.natDegree = 1 := natDegree_X
  have hQ : Q.natDegree = 1 := natDegree_X_sub_C _
  have hrough := tendsto_twoPrimeExcludingLayer hPQ monic_X (monic_X_sub_C _)
    irreducible_X (irreducible_X_sub_C _) hP hQ
  let q := (Fintype.card F : ℝ)
  let z := q⁻¹
  have hq : 1 < q := by
    change 1 < (Fintype.card F : ℝ)
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
  have hz₀ : 0 ≤ z := inv_nonneg.mpr (by linarith)
  have hz₁ : z < 1 := inv_lt_one_of_one_lt₀ hq
  let r (n : ℕ) := (primeExcludingLayer {P,Q} n).card
  have hr (n : ℕ) : (r n : ℝ) / q^n ∈ Set.Icc 0 1 := by
    refine ⟨by positivity, (div_le_one (pow_pos (by linarith) _)).mpr ?_⟩
    have hcard : r n ≤ Fintype.card F ^ n := by
      rw [← card_monicLayer (F := F) n]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    change (r n : ℝ) ≤ (Fintype.card F : ℝ)^n
    exact_mod_cast hcard
  have hs := twoPrimeFiberMaximum_series ht hz₀ hz₁
  have hsum := tendsto_weighted_rough_convolution _ hs.1 (fun _ ↦ by positivity) hr hrough
  have hsmall := (tendsto_pow_atTop_nhds_zero_of_lt_one hz₀ hz₁).comp (tendsto_add_atTop_nat 1)
  let B (N : ℕ) := z^(N+1) + (1-z) * ∑ t ∈ Finset.range (N+1),
    ((r (N-t) : ℝ) / q^(N-t)) * ((twoPrimeFiberMaximum t : ℝ) * z^t)
  have hlimit : Tendsto B atTop
      (𝓝 ((1-z)^3 * ∑' t, (twoPrimeFiberMaximum t : ℝ) * z^t)) := by
    have hcoef : (1-z) * ((1-z)^2 * (∑' t, (twoPrimeFiberMaximum t : ℝ) * z^t)) =
        (1-z)^3 * (∑' t, (twoPrimeFiberMaximum t : ℝ) * z^t) := by ring
    have hlim := hsmall.add (tendsto_const_nhds.mul hsum : Tendsto (fun N ↦ (1-z) * _)
      atTop (𝓝 ((1-z) * ((1-z)^2 * _))))
    simpa only [B, Function.comp_apply, zero_add, hcoef] using hlim
  have hbound (N : ℕ) : polynomialBallProportion E N ≤ B N := by
    have hc := PolynomialTwoPrimeFibers.card_polynomialBall_le hPQ monic_X (monic_X_sub_C _)
      irreducible_X (irreducible_X_sub_C _) hP hQ hE ht N
    unfold polynomialBallProportion
    calc
      _ ≤ ((↑(1 + (Fintype.card F - 1) * ∑ t ∈ Finset.range (N+1),
            r (N-t) * twoPrimeFiberMaximum t) : ℝ) / q^(N+1)) := by
          apply div_le_div_of_nonneg_right _ (pow_pos (by linarith) _).le
          exact_mod_cast hc
      _ = B N := by
          rw [Nat.cast_add, Nat.cast_one, add_div]
          change 1 / (Fintype.card F : ℝ)^(N+1) +
            _ / (Fintype.card F : ℝ)^(N+1) = _
          rw [polynomial_weighted_convolution_scale F N r twoPrimeFiberMaximum, one_div, ← inv_pow]
  have hlim := (limsup_le_limsup (Eventually.of_forall hbound)
    (isCoboundedUnder_le_of_le _ (polynomialBallProportion_nonneg E))
    hlimit.isBoundedUnder_le).trans_eq hlimit.limsup_eq
  rw [hs.2] at hlim
  exact hlim

/-- The triangle deficit yields the claimed bound on the actual density supremum. -/
theorem polynomialRatioDensitySupremum_le_twoPrime_of_triangle
    (F : Type*) [Field F] [Fintype F] (ht : TwoPrimeTriangleBound) :
    polynomialRatioDensitySupremum F ≤
      let z := (Fintype.card F : ℝ)⁻¹
      polynomialOnePrimeRothBound F - (1-z)^2*(z^8+z^19+z^29) := by
  apply csSup_le
  · exact ⟨_, ∅, by simp [PolynomialRatioThreeGPFree], rfl⟩
  · rintro d ⟨E, hE, rfl⟩
    exact limsup_polynomialBallProportion_le_twoPrime_of_triangle hE ht

/-- Each finite field has a positive gap below the one-prime Roth bound. -/
theorem polynomialRatioDensitySupremum_lt_onePrime_of_triangle
    (F : Type*) [Field F] [Fintype F] (ht : TwoPrimeTriangleBound) :
    polynomialRatioDensitySupremum F < polynomialOnePrimeRothBound F := by
  have hq : 1 < (Fintype.card F : ℝ) := by
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
  let z := (Fintype.card F : ℝ)⁻¹
  have h₀ : 0 < z := inv_pos.mpr (lt_trans zero_lt_one hq)
  have h₁ : 0 < 1-z := sub_pos.mpr (inv_lt_one_of_one_lt₀ hq)
  have hp : 0 < (1-z)^2 * (z^8+z^19+z^29) := by positivity
  exact (polynomialRatioDensitySupremum_le_twoPrime_of_triangle F ht).trans_lt
    (sub_lt_self _ hp)

end GRHArticle.ProgressionFree
