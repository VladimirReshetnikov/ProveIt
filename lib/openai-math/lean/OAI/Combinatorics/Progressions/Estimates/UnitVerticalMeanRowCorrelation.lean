import OAI.Combinatorics.Progressions.Estimates.NativeMeanRowCorrelation
import OAI.Combinatorics.Progressions.Estimates.PrescribedInvariantUnit

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_fin_two {G M : Type*} [Fintype G] [AddCommMonoid M] [Module ℚ≥0 M]
    (F : (Fin 2 → G) → M) : (𝔼 x, F x) = 𝔼 h : G, 𝔼 n : G, F ![h, n] := by
  rw [expect_fin_cons]
  apply Finset.expect_congr rfl
  intro h _
  rw [expect_fin_cons]
  apply Finset.expect_congr rfl
  intro n _
  have hc (y : Fin 0 → G) : F (Fin.cons h (Fin.cons n y)) = F ![h, n] := by
    congr 1
    funext k
    fin_cases k <;> rfl
  simp only [hc, Fintype.expect_const]

theorem norm_correlation_partition_bound {X I : Type*} [Fintype X] [Fintype I]
    (f u : X → ℂ) (v : I → X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖𝔼 x, f x * star (u x)‖ ≤
      (∑ i, ‖𝔼 x, f x * star (v i x)‖) + 𝔼 x, ‖u x - ∑ i, v i x‖ := by
  have he := norm_correlation_sub_le_mean f u (fun x => ∑ i, v i x) hf
  have ht := norm_le_norm_add_norm_sub
    (𝔼 x, f x * star (∑ i, v i x)) (𝔼 x, f x * star (u x))
  have hm : (𝔼 x, f x * star (∑ i, v i x)) = ∑ i, 𝔼 x, f x * star (v i x) := by
    simp only [star_sum, Finset.mul_sum, Finset.expect_sum_comm]
  rw [norm_sub_rev] at ht
  have hsum := norm_sum_le (s := Finset.univ) (f := fun i => 𝔼 x, f x * star (v i x))
  rw [hm] at ht he
  linarith

theorem exists_dense_row_partition_correlation {H X I : Type*}
    [Fintype H] [Nonempty H] [DecidableEq H] [Fintype X] [Nonempty X] [Fintype I]
    (S : Finset H) (f u : H → X → ℂ) (v : I → H → X → ℂ)
    {η M : ℝ} (hη : 0 < η) (hM : 0 < M) (hcard : (Fintype.card I : ℝ) ≤ M)
    (hf : ∀ h x, ‖f h x‖ ≤ 1) (hv : ∀ i h x, ‖v i h x‖ ≤ 1)
    (hmass : η ≤ 𝔼 h, if h ∈ S then ‖𝔼 x, f h x * star (u h x)‖ else 0)
    (herr : (𝔼 h, 𝔼 x, ‖u h x - ∑ i, v i h x‖) ≤ η / 2) :
    ∃ i : I, ∃ T : Finset H, T ⊆ S ∧ T.Nonempty ∧
      η / (4 * M) * Fintype.card H ≤ (T.card : ℝ) ∧
      ∀ h ∈ T, η / (4 * M) ≤ ‖𝔼 x, f h x * star (v i h x)‖ := by
  classical
  let value := fun (i : I) (h : H) => if h ∈ S then ‖𝔼 x, f h x * star (v i h x)‖ else 0
  have hnonneg (i : I) (h : H) : 0 ≤ value i h := by dsimp [value]; split_ifs <;> positivity
  have hpoint (h : H) : (if h ∈ S then ‖𝔼 x, f h x * star (u h x)‖ else 0) ≤
      (∑ i, value i h) + 𝔼 x, ‖u h x - ∑ i, v i h x‖ := by
    by_cases hh : h ∈ S
    · simpa only [value, hh, ite_true] using
        norm_correlation_partition_bound (f h) (u h) (fun i => v i h) (hf h)
    · simp only [value, hh, ite_false, Finset.sum_const_zero, zero_add]
      positivity
  have havg : η / 2 ≤ ∑ i, 𝔼 h, value i h := by
    have h := hmass.trans (Finset.expect_le_expect (fun h _ => hpoint h))
    rw [Finset.expect_add_distrib, Finset.expect_sum_comm] at h
    linarith
  have hI : (Finset.univ : Finset I).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at havg
    linarith
  obtain ⟨i, _hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => 𝔼 h, value i h) hI
  have hmax0 : 0 ≤ 𝔼 h, value i h := Finset.expect_nonneg (fun h _ => hnonneg i h)
  have hlarge : η / (2 * M) ≤ 𝔼 h, value i h := by
    have hsum : (∑ j, 𝔼 h, value j h) ≤ M * (𝔼 h, value i h) := by
      calc
        _ ≤ ∑ _j : I, 𝔼 h, value i h :=
          Finset.sum_le_sum (fun j _ => hmax j (Finset.mem_univ j))
        _ = (Fintype.card I : ℝ) * (𝔼 h, value i h) := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard hmax0
    have h := (div_le_iff₀ hM).mpr (by simpa only [mul_comm] using havg.trans hsum)
    simpa only [div_div] using h
  have hunit (h : H) : value i h ≤ 1 := by
    dsimp [value]
    split_ifs
    · calc
        _ ≤ 𝔼 x, ‖f h x * star (v i h x)‖ := RCLike.norm_expect_le (K := ℂ)
        _ ≤ 𝔼 _x : X, (1 : ℝ) := by
          apply Finset.expect_le_expect
          intro x _
          rw [norm_mul, norm_star]
          exact (mul_le_of_le_one_left (norm_nonneg _) (hf h x)).trans (hv i h x)
        _ = 1 := Fintype.expect_const _
    · norm_num
  obtain ⟨T, hTsize, hT⟩ := exists_dense_level_set (value i) (by positivity) hunit hlarge
  have hthreshold : η / (2 * M) / 2 = η / (4 * M) := by ring
  rw [hthreshold] at hTsize hT
  have hsub : T ⊆ S := by
    intro h hh
    by_contra hn
    have h := hT h hh
    simp only [value, hn, ite_false] at h
    have : 0 < η / (4 * M) := by positivity
    linarith
  have hTne : T.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast lt_of_lt_of_le (by positivity : 0 < η / (4 * M) * (Fintype.card H : ℝ)) hTsize
  exact ⟨i, T, hsub, hTne, hTsize, fun h hh => by
    simpa only [value, hsub hh, ite_true] using hT h hh⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def cyclicDivision (d : ℕ) {N : ℕ} (x : ZMod N) : ZMod N := (x.val / d : ℕ)

theorem cyclicDivision_val (d : ℕ) {N : ℕ} [NeZero N] (x : ZMod N) :
    (cyclicDivision d x).val = x.val / d :=
  ZMod.val_natCast_of_lt ((Nat.div_le_self _ _).trans_lt x.val_lt)

theorem cyclicDivision_with_residue_injective (d : ℕ) [NeZero d] {N : ℕ} [NeZero N] :
    Function.Injective (fun x : ZMod N => (cyclicDivision d x, (x.val : ZMod d))) := by
  intro x y h
  have hq := congrArg (fun z : ZMod N × ZMod d => z.1.val) h
  have hr := congrArg (fun z : ZMod N × ZMod d => z.2.val) h
  simp only [cyclicDivision_val] at hq
  simp only [ZMod.val_natCast] at hr
  apply ZMod.val_injective
  have hx := Nat.mod_add_div x.val d
  have hy := Nat.mod_add_div y.val d
  rw [hq, hr] at hx
  exact hx.symm.trans hy

theorem expect_cyclicDivision_le (d : ℕ) [NeZero d] {N : ℕ} [NeZero N] (f : ZMod N → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x : ZMod N, f (cyclicDivision d x)) ≤ d * (𝔼 x : ZMod N, f x) := by
  classical
  have hs : (∑ x : ZMod N, f (cyclicDivision d x)) ≤ ∑ z : ZMod N × ZMod d, f z.1 := by
    apply Finset.sum_le_sum_of_injOn (fun x : ZMod N => (cyclicDivision d x, (x.val : ZMod d)))
      (cyclicDivision_with_residue_injective d).injOn
    · exact Finset.subset_univ _
    · intro x _
      exact le_rfl
    · intro a _ _
      exact hf a.1
  have ht : (∑ z : ZMod N × ZMod d, f z.1) = d * ∑ x : ZMod N, f x := by
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, ← Finset.mul_sum]
  rw [ht] at hs
  simp only [Fintype.expect_eq_sum_div_card, ZMod.card]
  calc
    _ ≤ (d * ∑ x : ZMod N, f x) / N := div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)
    _ = _ := by ring

theorem expect_pair_cyclicDivision_le (d : ℕ) [NeZero d] {N : ℕ} [NeZero N]
    (f : (Fin 2 → ZMod N) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x : Fin 2 → ZMod N, f (fun i => cyclicDivision d (x i))) ≤
      (d : ℝ) ^ 2 * (𝔼 x : Fin 2 → ZMod N, f x) := by
  rw [expect_fin_two, expect_fin_two]
  have heq (h n : ZMod N) : (fun i => cyclicDivision d (![h, n] i)) =
      ![cyclicDivision d h, cyclicDivision d n] := by
    funext i
    fin_cases i <;> rfl
  simp only [heq]
  calc
    _ ≤ 𝔼 h : ZMod N, d * (𝔼 n : ZMod N, f ![cyclicDivision d h, n]) := by
      apply Finset.expect_le_expect
      intro h _
      exact expect_cyclicDivision_le d (fun n => f ![cyclicDivision d h, n]) (fun n => hf _)
    _ = d * (𝔼 h : ZMod N, 𝔼 n : ZMod N, f ![cyclicDivision d h, n]) := by
      rw [← Finset.mul_expect]
    _ ≤ d * (d * (𝔼 h : ZMod N, 𝔼 n : ZMod N, f ![h, n])) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
      exact expect_cyclicDivision_le d (fun h => 𝔼 n : ZMod N, f ![h, n])
        (fun h => Finset.expect_nonneg (fun n _ => hf _))
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def cyclicHalf {N : ℕ} (x : ZMod N) : ZMod N := (x.val / 2 : ℕ)

theorem cyclicHalf_val {N : ℕ} [NeZero N] (x : ZMod N) :
    (cyclicHalf x).val = x.val / 2 := by
  exact ZMod.val_natCast_of_lt ((Nat.div_le_self _ _).trans_lt x.val_lt)

theorem cyclicHalf_with_parity_injective {N : ℕ} [NeZero N] :
    Function.Injective (fun x : ZMod N => (cyclicHalf x, (x.val : ZMod 2))) := by
  intro x y h
  have hq := congrArg (fun z : ZMod N × ZMod 2 => z.1.val) h
  have hr := congrArg (fun z : ZMod N × ZMod 2 => z.2.val) h
  simp only [cyclicHalf_val] at hq
  simp only [ZMod.val_natCast] at hr
  apply ZMod.val_injective
  omega

theorem expect_cyclicHalf_le {N : ℕ} [NeZero N] (f : ZMod N → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x : ZMod N, f (cyclicHalf x)) ≤ 2 * (𝔼 x : ZMod N, f x) := by
  classical
  have hs : (∑ x : ZMod N, f (cyclicHalf x)) ≤ ∑ z : ZMod N × ZMod 2, f z.1 := by
    apply Finset.sum_le_sum_of_injOn (fun x : ZMod N => (cyclicHalf x, (x.val : ZMod 2)))
      cyclicHalf_with_parity_injective.injOn
    · exact Finset.subset_univ _
    · intro x _
      exact le_rfl
    · intro a _ _
      exact hf a.1
  have ht : (∑ z : ZMod N × ZMod 2, f z.1) = 2 * ∑ x : ZMod N, f x := by
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum]
  rw [ht] at hs
  simp only [Fintype.expect_eq_sum_div_card, ZMod.card]
  calc
    _ ≤ (2 * ∑ x : ZMod N, f x) / N := div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)
    _ = _ := by ring

theorem expect_pair_cyclicHalf_le {N : ℕ} [NeZero N] (f : (Fin 2 → ZMod N) → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x : Fin 2 → ZMod N, f (fun i => cyclicHalf (x i))) ≤
      4 * (𝔼 x : Fin 2 → ZMod N, f x) := by
  rw [expect_fin_two, expect_fin_two]
  have heq (h n : ZMod N) : (fun i => cyclicHalf (![h, n] i)) = ![cyclicHalf h, cyclicHalf n] := by
    funext i
    fin_cases i <;> rfl
  simp only [heq]
  calc
    _ ≤ 𝔼 h : ZMod N, 2 * (𝔼 n : ZMod N, f ![cyclicHalf h, n]) := by
      apply Finset.expect_le_expect
      intro h _
      exact expect_cyclicHalf_le (fun n => f ![cyclicHalf h, n]) (fun n => hf _)
    _ = 2 * (𝔼 h : ZMod N, 𝔼 n : ZMod N, f ![cyclicHalf h, n]) := by
      rw [← Finset.mul_expect]
    _ ≤ 2 * (2 * (𝔼 h : ZMod N, 𝔼 n : ZMod N, f ![h, n])) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact expect_cyclicHalf_le (fun h => 𝔼 n : ZMod N, f ![h, n])
        (fun h => Finset.expect_nonneg (fun n _ => hf _))
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def cyclicThird {N : ℕ} (x : ZMod N) : ZMod N := (x.val / 3 : ℕ)

theorem cyclicThird_val {N : ℕ} [NeZero N] (x : ZMod N) :
    (cyclicThird x).val = x.val / 3 := by
  exact ZMod.val_natCast_of_lt ((Nat.div_le_self _ _).trans_lt x.val_lt)

theorem cyclicThird_with_residue_injective {N : ℕ} [NeZero N] :
    Function.Injective (fun x : ZMod N => (cyclicThird x, (x.val : ZMod 3))) := by
  intro x y h
  have hq := congrArg (fun z : ZMod N × ZMod 3 => z.1.val) h
  have hr := congrArg (fun z : ZMod N × ZMod 3 => z.2.val) h
  simp only [cyclicThird_val] at hq
  simp only [ZMod.val_natCast] at hr
  apply ZMod.val_injective
  omega

theorem expect_cyclicThird_le {N : ℕ} [NeZero N] (f : ZMod N → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x : ZMod N, f (cyclicThird x)) ≤ 3 * (𝔼 x : ZMod N, f x) := by
  classical
  have hs : (∑ x : ZMod N, f (cyclicThird x)) ≤ ∑ z : ZMod N × ZMod 3, f z.1 := by
    apply Finset.sum_le_sum_of_injOn (fun x : ZMod N => (cyclicThird x, (x.val : ZMod 3)))
      cyclicThird_with_residue_injective.injOn
    · exact Finset.subset_univ _
    · intro x _
      exact le_rfl
    · intro a _ _
      exact hf a.1
  have ht : (∑ z : ZMod N × ZMod 3, f z.1) = 3 * ∑ x : ZMod N, f x := by
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum]
  rw [ht] at hs
  simp only [Fintype.expect_eq_sum_div_card, ZMod.card]
  calc
    _ ≤ (3 * ∑ x : ZMod N, f x) / N := div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)
    _ = _ := by ring

theorem expect_pair_cyclicThird_le {N : ℕ} [NeZero N] (f : (Fin 2 → ZMod N) → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x : Fin 2 → ZMod N, f (fun i => cyclicThird (x i))) ≤
      9 * (𝔼 x : Fin 2 → ZMod N, f x) := by
  rw [expect_fin_two, expect_fin_two]
  have heq (h n : ZMod N) : (fun i => cyclicThird (![h, n] i)) = ![cyclicThird h, cyclicThird n] := by
    funext i
    fin_cases i <;> rfl
  simp only [heq]
  calc
    _ ≤ 𝔼 h : ZMod N, 3 * (𝔼 n : ZMod N, f ![cyclicThird h, n]) := by
      apply Finset.expect_le_expect
      intro h _
      exact expect_cyclicThird_le (fun n => f ![cyclicThird h, n]) (fun n => hf _)
    _ = 3 * (𝔼 h : ZMod N, 𝔼 n : ZMod N, f ![cyclicThird h, n]) := by
      rw [← Finset.mul_expect]
    _ ≤ 3 * (3 * (𝔼 h : ZMod N, 𝔼 n : ZMod N, f ![h, n])) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact expect_cyclicThird_le (fun h => 𝔼 n : ZMod N, f ![h, n])
        (fun h => Finset.expect_nonneg (fun n _ => hf _))
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_unit_bounded_vertical_mean_row :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ H X L : Type*}
      [Fintype H] [Nonempty H] [Fintype X] [Nonempty X]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {s d : ℕ} (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ}
      (T : D.Niltest w) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ (sample : H → X → σ → ℤ) (f : H → X → ℂ), (∀ h x, ‖f h x‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 x, f h x * star (T.eval (sample h x))‖) →
      ∃ (η : L →ₗ[ℚ] ℚ) (U : D.Niltest w),
        U.ComplexityLE ((p + C) ^ C) ∧ U.normBound ≤ 1 ∧ U.orbit = T.orbit ∧
        (∀ i, rationalLogHeight (η (D.basis i)) ≤ (p + C) ^ C) ∧
        (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          U.observable (z • x) =
            character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * U.observable x) ∧
        (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
          ∃ n : ℤ, realifyFunctional η z.coord = n) ∧
        Real.exp (-((p + C) ^ C)) ≤
          (𝔼 h, ‖𝔼 x, f h x * star (U.eval (sample h x))‖) := by
  obtain ⟨A, _, hvertical⟩ := exists_verticalDecompositionBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (2 * X + 2 + Polynomial.C A) ^ A + (2 * X + 2) + 2)
  refine ⟨C, hC, ?_⟩
  intro σ H Y L _ _ _ _ _ _ _ _ _ _ s d D w T p hp hT sample f hf hcorr
  let r := 2 * p + 2
  let δ := Real.exp (-(p + 2))
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hδ : 0 < δ := Real.exp_pos _
  have hδr : δ⁻¹ ≤ Real.exp r := by
    dsimp [δ]
    rw [← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr (by dsimp [r]; linarith)
  obtain ⟨J, inst, η, U, hcard, hheight, hU, hchar, hint, _, _, herr⟩ :=
    T.exists_controlled_vertical_decomposition hr (hT.mono hpr) δ hδ hδr
  let := inst
  have hrow (h : H) : ‖𝔼 x, f h x * star (T.eval (sample h x))‖ ≤
      (∑ j : J, ‖𝔼 x, f h x * star ((U j).eval (sample h x))‖) + δ := by
    apply (norm_correlation_partition_bound (f h)
      (fun x => T.eval (sample h x)) (fun j x => (U j).eval (sample h x)) (hf h)).trans
    apply add_le_add le_rfl
    apply Finset.expect_le Finset.univ_nonempty
    intro x _
    simpa only [norm_sub_rev] using herr (sample h x)
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun h _ => hrow h)
  simp only [Finset.expect_add_distrib, Finset.expect_sum_comm, Fintype.expect_const] at hm
  have htwo : 2 * δ ≤ Real.exp (-p) := by
    calc
      _ ≤ Real.exp 2 * δ := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) hδ.le
      _ = _ := by dsimp [δ]; rw [← Real.exp_add]; congr 1; ring
  have hs : δ ≤ ∑ j : J, (𝔼 h, ‖𝔼 x, f h x * star ((U j).eval (sample h x))‖) := by
    linarith
  obtain ⟨j, hj⟩ := exists_large_nonnegative_weighted_term (fun _ : J => (1 : ℝ))
    (fun j => 𝔼 h, ‖𝔼 x, f h x * star ((U j).eval (sample h x))‖)
    (fun _ => by norm_num) (fun _ => Finset.expect_nonneg (fun _ _ => norm_nonneg _))
    hδ (Real.exp_pos _) (by simpa using hcard) (by simpa only [one_mul] using hs)
  have hne : ∃ x, (U j).observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, (U j).eval x = 0 := fun x => hzero _
    simp only [heval, star_zero, mul_zero, Finset.expect_const_zero, norm_zero] at hj
    exact (not_le_of_gt (div_pos hδ (Real.exp_pos _))) hj
  let q := p + verticalDecompositionBudget r + r + 2
  have hq : q ≤ (p + C) ^ C := by
    have hb : p + (r + A) ^ A + r + 2 ≤ (p + C) ^ C := by
      simpa [X, r, Polynomial.eval₂_pow] using hbudget p hp
    dsimp [q]
    linarith [hvertical r hr]
  have hrq : r ≤ (p + C) ^ C := by
    have hv := verticalDecompositionBudget_nonneg hr
    dsimp [q] at hq
    linarith
  have hvq : verticalDecompositionBudget r ≤ (p + C) ^ C := by
    dsimp [q] at hq
    linarith
  have hnormcorr : Real.exp (-q) ≤
      (𝔼 h, ‖𝔼 x, f h x * star (((U j).expNormalize r).eval (sample h x))‖) := by
    simp only [expNormalize_eval]
    rw [mean_row_correlation_scale f (fun h x => (U j).eval (sample h x)) (Real.exp_nonneg _)]
    have heq : Real.exp (-r) * (δ / Real.exp (verticalDecompositionBudget r)) =
        Real.exp (-q) := by
      dsimp [δ, q]
      rw [← Real.exp_sub, ← Real.exp_add]
      congr 1
      ring
    rw [← heq]
    exact mul_le_mul_of_nonneg_left hj (Real.exp_nonneg _)
  refine ⟨η j, (U j).expNormalize r,
    ((U j).expNormalize_complexity (hU j).1).mono hrq,
    (U j).expNormalize_norm (hU j).1, (hU j).2,
    fun i => (hheight j i).trans hvq, ?_, hint j hne,
    (Real.exp_le_exp.mpr (neg_le_neg hq)).trans hnormcorr⟩
  intro z hz x
  change (Real.exp (-r) : ℂ) * (U j).observable (z • x) =
    _ * ((Real.exp (-r) : ℂ) * (U j).observable x)
  rw [hchar j z hz]
  ring

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct NNReal

variable {σ L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {S : Subgroup D.RealGroup} {p : ℝ} {w : σ → ℕ}

noncomputable def test (V : D.UnitVerticalObservable S I p)
    (g : D.filtration.realification.PolynomialOrbit w) (i : I) : D.Niltest w where
  orbit := g
  observable := V.observable i
  normBound := 1
  lipBound := V.lipBound
  norm_le := V.norm i
  lipschitz := V.lipschitz i

theorem test_eval (V : D.UnitVerticalObservable S I p)
    (g : D.filtration.realification.PolynomialOrbit w) (i : I) (x : σ → ℤ) :
    (V.test g i).eval x = V.observable i
      (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)) := rfl

theorem test_complexity (V : D.UnitVerticalObservable S I p)
    (g : D.filtration.realification.PolynomialOrbit w) (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (i : I) : (V.test g i).ComplexityLE (p + 4) := by
  refine ⟨hD.mono D (by linarith), ?_⟩
  have ht := niltest_log_bound_of_exp (1 : ℝ≥0) V.lipBound (a := 0) (b := p)
    (by norm_num) hp (by simp) V.lip_bound
  simpa only [test, zero_add] using ht

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_unit_vertical_mean_row_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ H X L : Type*}
      [Fintype H] [Nonempty H] [Fintype X] [Nonempty X]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ}
      (T : D.Niltest w) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ (sample : H → X → σ → ℤ) (f : H → X → ℂ), (∀ h x, ‖f h x‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 x, f h x * star (T.eval (sample h x))‖) →
      ∃ n : ℕ, 0 < n ∧ (n + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ V : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
          (Fin (n + 1)) ((p + C) ^ C),
        D.GeometryComplexityLE ((p + C) ^ C) ∧
        Real.exp (-((p + C) ^ C)) ≤
          (𝔼 h, ‖𝔼 x, f h x * star ((V.test T.orbit 0).eval (sample h x))‖) := by
  obtain ⟨A, _, hmode⟩ := Niltest.exists_unit_bounded_vertical_mean_row
  obtain ⟨B, _, hcomplete⟩ := exists_native_unit_vertical_completion s
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C B) ^ B + 1)
  refine ⟨C, hC, ?_⟩
  intro σ H Y L _ _ _ _ _ _ _ _ _ _ d D w T p hp hT sample f hf hcorr
  let q := (p + A) ^ A
  let r := (q + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + r + 1 ≤ (p + C) ^ C := by
    simpa [X, Q, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨η, U, hU, hUnorm, horbit, hheight, hchar, hint, hcorrU⟩ :=
    hmode D T hp hT sample f hf hcorr
  obtain ⟨h, x, hx⟩ := exists_large_value_of_mean_row_correlation f
    (fun h x => U.eval (sample h x)) hf hcorrU
  let y : D.Space := QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval w (sample h x) U.orbit)
  obtain ⟨n, hn, hncard, K, hK, v, hv0, hvunit, hvnorm, hvLip, hvchar⟩ :=
    hcomplete D U hq hU hUnorm η hchar y hx
  let V : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
      (Fin (n + 1)) ((p + C) ^ C) :=
    { observable := v
      unit := hvunit
      norm := hvnorm
      lipBound := K
      lip_bound := hK.trans (Real.exp_le_exp.mpr hrC)
      lipschitz := hvLip
      frequency := η
      height := fun i => (hheight i).trans hqC
      vertical := hvchar
      integral := hint }
  have hscalar (z : σ → ℤ) : (V.test T.orbit 0).eval z = U.eval z / 2 := by
    rw [UnitVerticalObservable.test_eval]
    change v 0 _ = U.eval z / 2
    rw [hv0]
    unfold Niltest.eval
    rw [horbit]
  have hmean : (𝔼 h, ‖𝔼 x, f h x * star ((V.test T.orbit 0).eval (sample h x))‖) =
      (𝔼 h, ‖𝔼 x, f h x * star (U.eval (sample h x))‖) / 2 := by
    simp only [hscalar, star_div₀, star_ofNat, ← mul_div_assoc, ← Finset.expect_div,
      norm_div]
    norm_num
  refine ⟨n, hn, hncard.trans (Real.exp_le_exp.mpr hrC), V,
    hU.1.mono D hqC, ?_⟩
  rw [hmean]
  have hhalf : Real.exp (-(q + 1)) ≤ Real.exp (-q) / 2 := by
    simpa only [neg_add, sub_eq_add_neg] using exp_sub_one_le_half_exp (-q)
  exact (Real.exp_le_exp.mpr (by linarith)).trans
    (hhalf.trans (div_le_div_of_nonneg_right hcorrU (by norm_num)))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
