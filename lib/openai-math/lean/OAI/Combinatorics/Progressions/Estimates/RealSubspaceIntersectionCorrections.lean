import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic
import OAI.Combinatorics.Progressions.Geometry.ControlledSumCoordinates
import OAI.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection

namespace OAI

section

namespace Erdos3

theorem realDenominatorGrid_sub {ι : Type*} (l : ℕ) (x y : ι → ℝ)
    (hx : x ∈ realDenominatorGrid l) (hy : y ∈ realDenominatorGrid l) :
    x - y ∈ realDenominatorGrid l := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a - b, ?_⟩
  funext i
  change ((a i - b i : ℤ) : ℝ) = (l : ℝ) * (x i - y i)
  rw [Int.cast_sub, mul_sub]
  exact congrArg₂ (· - ·) (congrFun ha i) (congrFun hb i)

theorem realDenominatorGrid_sub_product {ι : Type*} (l m : ℕ) (x y : ι → ℝ)
    (hx : x ∈ realDenominatorGrid l) (hy : y ∈ realDenominatorGrid m) :
    x - y ∈ realDenominatorGrid (l * m) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨fun i => (m : ℤ) * a i - (l : ℤ) * b i, ?_⟩
  funext i
  change (((m : ℤ) * a i - (l : ℤ) * b i : ℤ) : ℝ) =
    (l * m : ℕ) * (x i - y i)
  have h1 : (a i : ℝ) = (l : ℝ) * x i := congrFun ha i
  have h2 : (b i : ℝ) = (m : ℝ) * y i := congrFun hb i
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, h1, h2]
  ring

theorem realDenominatorGrid_linear_combination {ι κ : Type*} [Fintype κ]
    (l m : ℕ) (c : κ → ℝ) (v : κ → ι → ℝ)
    (hc : c ∈ realDenominatorGrid l) (hv : ∀ k, v k ∈ realDenominatorGrid m) :
    (∑ k, c k • v k) ∈ realDenominatorGrid (m * l) := by
  classical
  obtain ⟨a, ha⟩ := hc
  choose b hb using hv
  refine ⟨fun i => ∑ k, a k * b k i, ?_⟩
  funext i
  change ((∑ k, a k * b k i : ℤ) : ℝ) = (m * l : ℕ) * (∑ k, c k • v k) i
  simp only [Int.cast_sum, Int.cast_mul, Nat.cast_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have h1 : (a k : ℝ) = (l : ℝ) * c k := congrFun ha k
  have h2 : (b k i : ℝ) = (m : ℝ) * v k i := congrFun (hb k) i
  rw [h1, h2]
  ring

theorem linear_lift_grid_of_coefficients {ι κ K : Type*} [Fintype κ]
    [AddCommGroup K] [Module ℝ K]
    (R : K →ₗ[ℝ] (ι → ℝ)) (v : κ → K) (c : κ → ℝ) (l m : ℕ)
    (hc : c ∈ realDenominatorGrid l) (hR : ∀ k, R (v k) ∈ realDenominatorGrid m) :
    R (∑ k, c k • v k) ∈ realDenominatorGrid (m * l) := by
  simp only [map_sum, map_smul]
  exact realDenominatorGrid_linear_combination l m c (fun k => R (v k)) hc hR

theorem rational_lift_absorption_grid {ι κ K : Type*} [Fintype κ]
    [AddCommGroup K] [Module ℝ K]
    (R : K →ₗ[ℝ] (ι → ℝ)) (v : κ → K) (c : κ → ℝ) (r : ι → ℝ) (l m n : ℕ)
    (hc : c ∈ realDenominatorGrid l) (hR : ∀ k, R (v k) ∈ realDenominatorGrid m)
    (hr : r ∈ realDenominatorGrid n) :
    r - R (∑ k, c k • v k) ∈ realDenominatorGrid (n * (m * l)) :=
  realDenominatorGrid_sub_product n (m * l) r _ hr
    (linear_lift_grid_of_coefficients R v c l m hc hR)

theorem norm_sub_lift_bound {E K V : Type*}
    [AddCommGroup E] [Module ℝ E] [SeminormedAddCommGroup K] [NormedSpace ℝ K]
    [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (N : E →ₗ[ℝ] V) (S : K →ₗ[ℝ] E) (s : E) (k : K)
    (A C M T : ℝ) (hC : 0 ≤ C) (hT : 0 < T)
    (hs : ‖N s‖ ≤ A / T) (hk : ‖k‖ ≤ M / T)
    (hS : ∀ x, ‖N (S x)‖ ≤ C * ‖x‖) :
    ‖N (s - S k)‖ ≤ (A + C * M) / T := by
  rw [map_sub]
  calc
    _ ≤ ‖N s‖ + ‖N (S k)‖ := norm_sub_le _ _
    _ ≤ A / T + C * (M / T) :=
      add_le_add hs ((hS k).trans (mul_le_mul_of_nonneg_left hk hC))
    _ = _ := by field_simp [hT.ne']

theorem norm_removed_derivative_bound {E V : Type*}
    [AddCommGroup E] [Module ℝ E] [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (N : E →ₗ[ℝ] V) (A : E →ₗ[ℝ] E) (x y : E)
    (C M D T : ℝ) (hC : 0 ≤ C) (hT : 0 < T)
    (hA : ∀ z, ‖N (A z)‖ ≤ C * ‖N z‖)
    (hx : ‖N x‖ ≤ M / T) (hy : ‖N y‖ ≤ D / T) :
    ‖N (A (x - y))‖ ≤ C * (M + D) / T := by
  calc
    _ ≤ C * ‖N (x - y)‖ := hA _
    _ ≤ C * (‖N x‖ + ‖N y‖) := by
      rw [map_sub]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hC
    _ ≤ C * (M / T + D / T) := mul_le_mul_of_nonneg_left (add_le_add hx hy) hC
    _ = _ := by field_simp [hT.ne']

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

theorem kernel_split_factor_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ((n : ℝ) + 1) * (H + 1) * Real.exp ((p + 2) ^ 18) ≤ Real.exp ((p + 2) ^ 19) := by
  have hfac : ((n : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    calc
      _ ≤ ((n : ℝ) + 1) * (Real.exp ((p + 2) ^ 1) + 1) := by
        gcongr
        exact hH.trans (Real.exp_le_exp.mpr (by simp))
      _ ≤ _ := matrix_weighted_factor_le_exp_power n hp hn 1 (by decide)
  have hpow : (p + 2) ^ 3 ≤ (p + 2) ^ 18 :=
    pow_le_pow_right₀ (by linarith) (by decide)
  have hsum : (p + 2) ^ 3 + (p + 2) ^ 18 ≤ (p + 2) ^ 19 := by
    calc
      _ ≤ (p + 2) ^ 18 + (p + 2) ^ 18 := add_le_add hpow (le_refl ((p + 2) ^ 18))
      _ = 2 * (p + 2) ^ 18 := by ring
      _ ≤ (p + 2) * (p + 2) ^ 18 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := (pow_succ' (p + 2) 18).symm
  calc
    _ ≤ Real.exp ((p + 2) ^ 3) * Real.exp ((p + 2) ^ 18) :=
      mul_le_mul_of_nonneg_right hfac (Real.exp_nonneg _)
    _ = Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hsum

theorem exists_controlled_kernel_split {ι κ ν τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν]
    (U K : Submodule ℝ (ι → ℝ)) (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ)
    (hAspan : Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) = U)
    (hBspan : Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) = K)
    (b : ν → K) (hb : ∀ j, (b j).val = (B.map (Rat.castHom ℝ)).col j)
    (R : K →ₗ[ℝ] (τ → ℝ)) (n : ℕ) (hR : ∀ j, R (b j) ∈ realDenominatorGrid n)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hB : ∀ i j, RationalHeightLE (B i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ split : (ι → ℝ) →ₗ[ℝ] K,
        (∀ x, x ∈ U ⊔ K → x - (split x).val ∈ U) ∧
        (∀ x, ‖split x‖ ≤ Real.exp ((p + 2) ^ 19) * ‖x‖) ∧
        ∀ x, x ∈ realDenominatorGrid l → R (split x) ∈ realDenominatorGrid (n * m) := by
  classical
  obtain ⟨m, hm, hmp, u, v, hdecomp, hnorm, hgrid⟩ :=
    exists_controlled_sum_coordinates A B hH hl hA hB hp hι hcols hHp hlp
  have hν : (Fintype.card ν : ℝ) ≤ p := by
    have hsum : (Fintype.card κ : ℝ) + Fintype.card ν ≤ p := by
      simpa only [Fintype.card_sum, Nat.cast_add] using hcols
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card κ)]
  let C : (ν → ℝ) →ₗ[ℝ] K := {
    toFun := fun c => ∑ j, c j • b j
    map_add' := by intros; simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    map_smul' := by intros; simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hC (c : ν → ℝ) : (C c).val = B.map (Rat.castHom ℝ) *ᵥ c := by
    change K.subtype (∑ j, c j • b j) = _
    rw [map_sum]
    simp only [map_smul]
    change (∑ j, c j • (b j).val) = _
    simp only [hb]
    ext i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨m, hm, hmp, C.comp v, ?_, ?_, ?_⟩
  · intro x hx
    have hd := hdecomp x (by simpa only [hAspan, hBspan] using hx)
    have hu : A.map (Rat.castHom ℝ) *ᵥ u x ∈ U := by
      rw [← hAspan]
      exact (real_column_span_mem_iff A _).mpr ⟨u x, rfl⟩
    change x - (C (v x)).val ∈ U
    have he : x - B.map (Rat.castHom ℝ) *ᵥ v x = A.map (Rat.castHom ℝ) *ᵥ u x :=
      (eq_sub_iff_add_eq.mpr hd).symm
    rw [hC, he]
    exact hu
  · intro x
    change ‖(C (v x)).val‖ ≤ _
    rw [hC]
    have hmat := norm_matrix_mulVec_le (B.map (Rat.castHom ℝ)) (H : ℝ≥0)
      (fun i j => (hB i j).abs_real_le) (v x)
    calc
      _ ≤ (((Fintype.card ν : ℝ) + 1) * (H + 1)) * ‖v x‖ := hmat
      _ ≤ (((Fintype.card ν : ℝ) + 1) * (H + 1)) * (Real.exp ((p + 2) ^ 18) * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hnorm x).2 (by positivity)
      _ = (((Fintype.card ν : ℝ) + 1) * (H + 1) * Real.exp ((p + 2) ^ 18)) * ‖x‖ :=
        (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (kernel_split_factor_le_exp (Fintype.card ν) H hp hν hHp) (norm_nonneg x)
  · intro x hx
    exact linear_lift_grid_of_coefficients R b (v x) m n (hgrid x hx).2 hR

theorem horizontal_absorption_with_split {H E : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]
    (U K : Submodule ℝ H) (P : E →ₗ[ℝ] H)
    (f : E →ₗ[ℝ] E) (hf : P.comp f = P) (S R : K →ₗ[ℝ] E)
    (hSR : S = f.comp R) (hS : P.comp S = K.subtype) (hR : P.comp R = K.subtype)
    (split : H →ₗ[ℝ] K) (hsplit : ∀ x, x ∈ U ⊔ K → x - (split x).val ∈ U)
    (y small rational : E) (k : K) (hsystem : y = small + f rational + S k)
    (hy : P y ∈ U) (hsmall : P small ∈ U ⊔ K) (hrational : P rational ∈ U ⊔ K) :
    let ks := split (P small)
    let kr := split (P rational)
    P (small - S ks) ∈ U ∧ P (rational - R kr) ∈ U ∧ (k + ks + kr).val ∈ U ∧
      y = (small - S ks) + f (rational - R kr) + S (k + ks + kr) := by
  let ks := split (P small)
  let kr := split (P rational)
  have hs : P (small - S ks) ∈ U := by
    rw [map_sub, show P (S ks) = ks.val from DFunLike.congr_fun hS ks]
    exact hsplit (P small) hsmall
  have hr : P (rational - R kr) ∈ U := by
    rw [map_sub, show P (R kr) = kr.val from DFunLike.congr_fun hR kr]
    exact hsplit (P rational) hrational
  have hnew := linear_derivative_absorb f S R hSR y small rational k ks kr hsystem
  refine ⟨hs, hr, ?_, hnew⟩
  have he : P y = P (small - S ks) + P (rational - R kr) + (k + ks + kr).val := by
    rw [hnew, map_add, map_add,
      show P (f (rational - R kr)) = P (rational - R kr) from DFunLike.congr_fun hf _,
      show P (S (k + ks + kr)) = (k + ks + kr).val from DFunLike.congr_fun hS _]
  have hm := U.sub_mem (U.sub_mem hy hs) hr
  have he' : P y - P (small - S ks) - P (rational - R kr) = (k + ks + kr).val := by
    rw [he]
    abel
  exact he' ▸ hm

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

theorem exists_image_intersection_corrections
    {ι κ ν σ : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hB : ∀ i j, RationalHeightLE (B i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 36) ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (a b u v : ι → ℝ),
        u ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) →
        v ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) →
        ‖a‖ ≤ Real.exp p / monomialScale T α → b ∈ realDenominatorGrid l →
        u - v = a + b → ∃ e q : ι → ℝ,
          e ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ∧
          q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ∧
          ‖e‖ ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α ∧
          q ∈ realDenominatorGrid m ∧
          u - e - q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ⊓
            LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) := by
  let C := Matrix.fromCols A B
  have hC : ∀ i j, RationalHeightLE (C i j) H := by
    intro i j
    cases j with
    | inl j => exact hA i j
    | inr j => exact hB i j
  obtain ⟨S, m, hm, hmp, hsolve⟩ :=
    exists_controlled_linear_splitting C hH hl hC hp hι hcols hHp hlp T hT
  have hκ : (Fintype.card κ : ℝ) ≤ p := by
    rw [Fintype.card_sum, Nat.cast_add] at hcols
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ν)]
  have hHp' : (H : ℝ) ≤ Real.exp ((p + 2) ^ 1) :=
    hHp.trans (Real.exp_le_exp.mpr (by simp))
  have hden : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    matrixDenominator_le_exp_power A hp 1 hι hκ
      (fun i j => (Nat.cast_le.mpr (hA i j).2).trans hHp')
  have hfac : ((Fintype.card κ : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power (Fintype.card κ) hp hκ 1 (by decide))
    exact mul_le_mul_of_nonneg_left (add_le_add hHp' le_rfl) (by positivity)
  have hnorm (y : κ → ℝ) :
      ‖(fun i j => (A i j : ℝ)) *ᵥ y‖ ≤ Real.exp ((p + 2) ^ 3) * ‖y‖ :=
    (norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hA i j).abs_real_le) y).trans
      (mul_le_mul_of_nonneg_right hfac (norm_nonneg y))
  refine ⟨matrixDenominator A * m, Nat.mul_pos (matrixDenominator_pos A) hm, ?_, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hden hmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  · intro α hα a b u v hu hv ha hb hdiff
    have hspan : Submodule.span ℝ (Set.range (fun j i => (C i j : ℝ))) =
        Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) ⊔
          Submodule.span ℝ (Set.range (fun j i => (B i j : ℝ))) :=
      real_column_span_fromCols A B
    have hdiffmem : u - v ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (C i j : ℝ))) := by
      apply (real_column_span_mem_iff C _).mp
      rw [hspan]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left ((real_column_span_mem_iff A _).mpr hu))
        (Submodule.mem_sup_right ((real_column_span_mem_iff B _).mpr hv))
    obtain ⟨z, hz⟩ := hdiffmem
    obtain ⟨hSa, hSb, hslow, hgrid, _⟩ := hsolve α hα a b z ha hb (hz.trans hdiff)
    let ca := (fun i j => (S i j : ℝ)) *ᵥ a
    let cb := (fun i j => (S i j : ℝ)) *ᵥ b
    let e := (fun i j => (A i j : ℝ)) *ᵥ (ca ∘ Sum.inl)
    let q := (fun i j => (A i j : ℝ)) *ᵥ (cb ∘ Sum.inl)
    let eB := (fun i j => (B i j : ℝ)) *ᵥ (ca ∘ Sum.inr)
    let qB := (fun i j => (B i j : ℝ)) *ᵥ (cb ∘ Sum.inr)
    have he : e ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := ⟨_, rfl⟩
    have hq : q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := ⟨_, rfl⟩
    have heB : eB ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) := ⟨_, rfl⟩
    have hqB : qB ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) := ⟨_, rfl⟩
    have hea : e + eB = a := by
      change (C.map (Rat.castHom ℝ)) *ᵥ ca = a at hSa
      dsimp only [C] at hSa
      rw [Matrix.fromCols_map, Matrix.fromCols_mulVec] at hSa
      exact hSa
    have hqb : q + qB = b := by
      change (C.map (Rat.castHom ℝ)) *ᵥ cb = b at hSb
      dsimp only [C] at hSb
      rw [Matrix.fromCols_map, Matrix.fromCols_mulVec] at hSb
      exact hSb
    refine ⟨e, q, he, hq, ?_,
      real_matrix_denominator_grid A m _ (realDenominatorGrid_comp m _ hgrid Sum.inl),
      Submodule.sub_mem _ (Submodule.sub_mem _ hu he) hq, ?_⟩
    · calc
        ‖e‖ ≤ Real.exp ((p + 2) ^ 3) * ‖ca ∘ Sum.inl‖ := hnorm _
        _ ≤ Real.exp ((p + 2) ^ 3) *
            (Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) :=
          mul_le_mul_of_nonneg_left ((pi_norm_restriction_le ca Sum.inl).trans hslow)
            (Real.exp_pos _).le
        _ = _ := by
          rw [← mul_div_assoc, ← Real.exp_add]
          congr 2
          ring
    · have heq : u - e - q = v + eB + qB := by
        rw [← hea, ← hqb] at hdiff
        have hu' : u = (e + eB) + (q + qB) + v := (sub_eq_iff_eq_add).mp hdiff
        rw [hu']
        abel
      rw [heq]
      exact Submodule.add_mem _ (Submodule.add_mem _ hv heB) hqB

end Erdos3

end

section

namespace Erdos3

theorem exists_common_intersection_corrections
    {ι κ ν σ : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hB : ∀ i j, RationalHeightLE (B i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (β e₁ e₂ q₁ q₂ : ι → ℝ),
        β - e₁ - q₁ ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) →
        β - e₂ - q₂ ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) →
        ‖e₁‖ ≤ Real.exp p / monomialScale T α →
        ‖e₂ - e₁‖ ≤ Real.exp p / monomialScale T α →
        q₁ ∈ realDenominatorGrid l → q₂ ∈ realDenominatorGrid l →
        ∃ e q : ι → ℝ,
          ‖e‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) /
            monomialScale T α ∧ q ∈ realDenominatorGrid m ∧
          β - e - q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ⊓
            LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) := by
  obtain ⟨m, hm, hmp, hsolve⟩ := exists_image_intersection_corrections A B hH hl hA hB hp
    hι hcols hHp hlp T hT
  refine ⟨l * m, Nat.mul_pos hl hm, ?_, dvd_mul_right l m, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hlp hmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  · intro α hα β e₁ e₂ q₁ q₂ h₁ h₂ he₁ he₂ hq₁ hq₂
    have hdiff : (β - e₁ - q₁) - (β - e₂ - q₂) = (e₂ - e₁) + (q₂ - q₁) := by abel
    obtain ⟨e, q, _, _, he, hq, hrem⟩ := hsolve α hα (e₂ - e₁) (q₂ - q₁)
      (β - e₁ - q₁) (β - e₂ - q₂) h₁ h₂ he₂
      (realDenominatorGrid_sub l q₂ q₁ hq₂ hq₁) hdiff
    refine ⟨e₁ + e, q₁ + q, ?_, ?_, ?_⟩
    · calc
        ‖e₁ + e‖ ≤ ‖e₁‖ + ‖e‖ := norm_add_le _ _
        _ ≤ Real.exp p / monomialScale T α +
            Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α :=
          add_le_add he₁ he
        _ = _ := (add_div _ _ _).symm
    · simpa only [sub_neg_eq_add] using
        realDenominatorGrid_sub_product l m q₁ (-q) hq₁ (realDenominatorGrid_neg m hq)
    · have heq : β - (e₁ + e) - (q₁ + q) = (β - e₁ - q₁) - e - q := by abel
      rwa [heq]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_basis_intersection_correction
    {μ κ ν σ L : Type*} [Fintype μ] [Fintype κ] [Fintype ν]
    [LieRing L] [LieAlgebra ℚ L]
    (b : Basis μ ℚ L) (U V : Submodule ℚ L) (v : κ → L) (w : ν → L)
    (hv : Submodule.span ℚ (Set.range v) = U) (hw : Submodule.span ℚ (Set.range w) = V)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ a i, RationalHeightLE (b.repr (v a) i) H)
    (hwH : ∀ a i, RationalHeightLE (b.repr (w a) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (x e q : ℝ ⊗[ℚ] L),
        x - e - q ∈ U.baseChange ℝ → x ∈ V.baseChange ℝ →
        ‖(b.baseChange ℝ).equivFun e‖ ≤ Real.exp p / monomialScale T α →
        (b.baseChange ℝ).equivFun q ∈ realDenominatorGrid l →
        ∃ E Q : ℝ ⊗[ℚ] L,
          ‖(b.baseChange ℝ).equivFun E‖ ≤
            (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) / monomialScale T α ∧
          (b.baseChange ℝ).equivFun Q ∈ realDenominatorGrid m ∧
          x - E - Q ∈ (U ⊓ V).baseChange ℝ := by
  let B := (b.baseChange ℝ).equivFun
  let A : Matrix μ κ ℚ := fun i a => b.repr (v a) i
  let C : Matrix μ ν ℚ := fun i a => b.repr (w a) i
  have hU (x : ℝ ⊗[ℚ] L) : x ∈ U.baseChange ℝ ↔
      B x ∈ LinearMap.range (Matrix.mulVecLin (fun i a => (A i a : ℝ))) := by
    rw [← real_span_rational_family U v hv, real_span_family_mem_iff_coordinates b v,
      real_column_span_mem_iff A]
  have hV (x : ℝ ⊗[ℚ] L) : x ∈ V.baseChange ℝ ↔
      B x ∈ LinearMap.range (Matrix.mulVecLin (fun i a => (C i a : ℝ))) := by
    rw [← real_span_rational_family V w hw, real_span_family_mem_iff_coordinates b w,
      real_column_span_mem_iff C]
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_common_intersection_corrections A C hH hl
    (fun i a => hvH a i) (fun i a => hwH a i) hp hμ hcols hHp hlp T hT
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro α hα x e q hxU hxV he hq
  have hu : B x - B e - B q ∈
      LinearMap.range (Matrix.mulVecLin (fun i a => (A i a : ℝ))) := by
    simpa only [map_sub] using (hU (x - e - q)).mp hxU
  have hz : B x - 0 - 0 ∈
      LinearMap.range (Matrix.mulVecLin (fun i a => (C i a : ℝ))) := by
    simpa only [sub_zero] using (hV x).mp hxV
  obtain ⟨E, Q, hE, hQ, hmem⟩ := hsolve α hα (B x) (B e) 0 (B q) 0 hu hz he
    (by simpa only [zero_sub, norm_neg] using he) hq (realDenominatorGrid_zero l)
  refine ⟨B.symm E, B.symm Q, ?_, ?_, ?_⟩
  · change ‖B (B.symm E)‖ ≤ _
    rw [B.apply_symm_apply]
    exact hE
  · change B (B.symm Q) ∈ _
    rw [B.apply_symm_apply]
    exact hQ
  · rw [realification_inf]
    constructor
    · apply (hU _).mpr
      rw [map_sub, map_sub, B.apply_symm_apply, B.apply_symm_apply]
      exact hmem.1
    · apply (hV _).mpr
      rw [map_sub, map_sub, B.apply_symm_apply, B.apply_symm_apply]
      exact hmem.2

end Erdos3

end

end OAI
