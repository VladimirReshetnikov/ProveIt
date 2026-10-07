/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Lattices.SmoothIntegerTranslation

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem independent_row_density_error {I X : Type*} [Fintype I] [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : I → PMF X) (A : I → ℝ) (f : I → X → ℝ) {B epsilon : ℝ}
    (hB : 1 ≤ B) (hepsilon : 0 ≤ epsilon)
    (hcap : ∀ i x, |f i x| ≤ B)
    (herror : ∀ i x, |A i * (p i x).toReal - f i x| ≤ epsilon) (x : I → X) :
    |(∏ i, A i) * (independentProductPMF p x).toReal - ∏ i, f i (x i)| ≤
      Fintype.card I * epsilon * (B + epsilon) ^ Fintype.card I := by
  rw [independentProductPMF_toReal, ← Finset.prod_mul_distrib]
  apply abs_finset_prod_sub_prod_le Finset.univ _ _ (by linarith) hepsilon
  · intro i _
    have h := abs_add_le (A i * (p i (x i)).toReal - f i (x i)) (f i (x i))
    have he := herror i (x i)
    have hc := hcap i (x i)
    rw [sub_add_cancel] at h
    linarith
  · intro i _
    exact (hcap i (x i)).trans (by linarith)
  · intro i _
    exact herror i (x i)

theorem product_masked_scalars {I : Type*} [Fintype I]
    (P : I → Prop) (f : I → ℝ) (m : ℝ) :
    (∏ i, if P i then m * f i else 0) =
      if ∀ i, P i then m ^ Fintype.card I * ∏ i, f i else 0 := by
  by_cases h : ∀ i, P i
  · simp [h, Finset.prod_mul_distrib]
  · have hn : ∃ i, ¬ P i := by simpa only [not_forall] using h
    obtain ⟨i, hi⟩ := hn
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem independent_masked_row_density_error {I X : Type*} [Fintype I] [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : I → PMF X) (A : I → ℝ) (P : I → X → Prop) (f : I → X → ℝ) (m : ℝ)
    {B epsilon : ℝ} (hB : 1 ≤ B) (hepsilon : 0 ≤ epsilon)
    (hcap : ∀ i x, |m * f i x| ≤ B)
    (herror : ∀ i x, |A i * (p i x).toReal - (if P i x then m * f i x else 0)| ≤ epsilon)
    (x : I → X) :
    |(∏ i, A i) * (independentProductPMF p x).toReal -
      (if ∀ i, P i (x i) then m ^ Fintype.card I * ∏ i, f i (x i) else 0)| ≤
      Fintype.card I * epsilon * (B + epsilon) ^ Fintype.card I := by
  have hc (i : I) (y : X) : |(if P i y then m * f i y else 0)| ≤ B := by
    split_ifs
    · exact hcap i y
    · simpa only [abs_zero] using zero_le_one.trans hB
  have h := independent_row_density_error p A (fun i y => if P i y then m * f i y else 0)
    hB hepsilon hc herror x
  rwa [product_masked_scalars] at h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def smoothPairCoefficientScale {J : Type*} (H L : ℝ) : Option J → ℝ :=
  fun c => match c with | none => H | some _ => H / L

theorem smoothPairCoefficientScale_pos {J : Type*} {H L : ℝ} (hH : 0 < H) (hL : 0 < L) :
    ∀ c : Option J, 0 < smoothPairCoefficientScale H L c := by
  intro c
  cases c
  · exact hH
  · exact div_pos hH hL

theorem affinePair_split_mulVec {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (z : Option J → ℤ) :
    affinePairMatrix t u *ᵥ z =
      affinePairPivot t u k *ᵥ (smoothInputSplit (affinePairColumnEquiv k) z).1 +
      affinePairFree t u k *ᵥ (smoothInputSplit (affinePairColumnEquiv k) z).2 := by
  calc
    _ = Matrix.fromCols (affinePairPivot t u k) (affinePairFree t u k) *ᵥ
        (z ∘ affinePairColumnEquiv k) := by
      rw [affinePairPivot_columns, Matrix.submatrix_mulVec_equiv]
      simp only [Function.comp_def, Equiv.apply_symm_apply, id_eq]
    _ = _ := by
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, smoothInputSplit, Matrix.fromCols]

theorem smooth_pair_input_law {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) {H L : ℝ} (hH : 0 < H) (hL : 0 < L)
    (hM : 0 < scaledInputMass (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
      (affinePairScale H L) (fun _ => H / L)) :
    (smoothProductPMF (smoothPairCoefficientScale H L) (smoothPairCoefficientScale_pos hH hL)).map
        (smoothInputSplit (affinePairColumnEquiv k)) =
      scaledInputPMF (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
        (fun z => (splitSmoothProductProfile_range _ _ z).1)
        (affinePairScale H L) (fun _ => H / L) (affinePairScale_pos hH hL)
        (fun _ => div_pos hH hL) (splitSmoothProductProfile_zero_outside _ _) hM := by
  have hs : (fun i => smoothPairCoefficientScale H L (affinePairColumnEquiv k (.inl i))) =
      affinePairScale H L := by
    funext i
    fin_cases i <;> rfl
  have ht : (fun j => smoothPairCoefficientScale H L (affinePairColumnEquiv k (.inr j))) =
      (fun _ : {j : J // j ≠ k} => H / L) := rfl
  have hm : 0 < scaledInputMass (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
      (fun i => smoothPairCoefficientScale H L (affinePairColumnEquiv k (.inl i)))
      (fun j => smoothPairCoefficientScale H L (affinePairColumnEquiv k (.inr j))) := by
    simpa only [hs, ht] using hM
  have h := smoothInputSplit_law (affinePairColumnEquiv k) (smoothPairCoefficientScale H L)
    (smoothPairCoefficientScale_pos hH hL) hm
  simpa only [hs, ht] using h

theorem smooth_pair_row_law {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) {H L : ℝ} (hH : 0 < H) (hL : 0 < L)
    (hM : 0 < scaledInputMass (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
      (affinePairScale H L) (fun _ => H / L)) :
    (smoothProductPMF (smoothPairCoefficientScale H L) (smoothPairCoefficientScale_pos hH hL)).map
        (fun z => affinePairMatrix t u *ᵥ z) =
      integerImagePMF (affinePairPivot t u k) (affinePairFree t u k)
        (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
        (fun z => (splitSmoothProductProfile_range _ _ z).1)
        (affinePairScale H L) (fun _ => H / L) (affinePairScale_pos hH hL)
        (fun _ => div_pos hH hL) (splitSmoothProductProfile_zero_outside _ _) hM := by
  rw [integerImagePMF, ← smooth_pair_input_law k hH hL hM, PMF.map_comp]
  congr 1
  funext z
  exact affinePair_split_mulVec t u k z

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem smooth_affinePairRowDensity_cap {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    {H L C κ : ℝ} (hH : 0 < H) (hL : 0 < L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) (y : Fin 2 → ℝ) :
    |affinePairRowDensity t u k hne H L hH hL
      (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)) y| ≤
      2 * (4 * C / κ) ^ 2 * (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} := by
  have hA : (affinePairPivot t u k).det ≠ 0 := by rwa [affinePairPivot_det]
  let e := normalizedPivotEquiv (affinePairPivot t u k) hA (affinePairScale H L)
    (fun _ => H) (affinePairScale_pos hH hL) (fun _ => hH)
  let b := matrixSupCLM (normalizedIntegerColumns (affinePairFree t u k) (fun _ => H / L) (fun _ => H))
  have hinv : ‖e.symm.toContinuousLinearMap‖ ≤ 4 * C / κ := by
    dsimp only [e]
    rw [normalizedPivotEquiv_inverse_eq]
    exact normalized_affinePairPivot_inverse t u k hH.ne' hL.ne' hC hκ ht hu hgap
  have hb (z : ({j : J // j ≠ k} → ℝ) × (Fin 2 → ℝ)) :
      ‖splitSmoothProductProfile {j : J // j ≠ k} (Fin 2) z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (splitSmoothProductProfile_range _ _ z).1]
    exact (splitSmoothProductProfile_range _ _ z).2
  have h := pivotOutputDensity_abs_le_uniform e b _ zero_le_one zero_le_one
    (splitSmoothProductProfile_zero_outside _ _) hb hinv y
  norm_num at h
  simpa [affinePairRowDensity, normalizedFiberDensity, e, b] using h

theorem smooth_affinePairRowDensity_lipschitz {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    {H L C κ : ℝ} (hH : 0 < H) (hL : 0 < L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) :
    LipschitzWith (Real.toNNReal (2 * (4 * C / κ) ^ 3 * (smoothPairRowLipschitz k : ℝ) *
      (2 : ℝ) ^ Fintype.card {j : J // j ≠ k}))
      (affinePairRowDensity t u k hne H L hH hL
        (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))) := by
  have hA : (affinePairPivot t u k).det ≠ 0 := by rwa [affinePairPivot_det]
  let e := normalizedPivotEquiv (affinePairPivot t u k) hA (affinePairScale H L)
    (fun _ => H) (affinePairScale_pos hH hL) (fun _ => hH)
  let b := matrixSupCLM (normalizedIntegerColumns (affinePairFree t u k) (fun _ => H / L) (fun _ => H))
  have hU : 0 ≤ 4 * C / κ := div_nonneg (by linarith) hκ.le
  have hinv : ‖e.symm.toContinuousLinearMap‖ ≤ 4 * C / κ := by
    dsimp only [e]
    rw [normalizedPivotEquiv_inverse_eq]
    exact normalized_affinePairPivot_inverse t u k hH.ne' hL.ne' hC hκ ht hu hgap
  have hLip : LipschitzWith (smoothPairRowLipschitz k)
      (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)) := by
    simpa only [smoothPairRowLipschitz, Fintype.card_fin] using
      splitSmoothProductProfile_lipschitz {j : J // j ≠ k} (Fin 2)
  have h := pivotOutputDensity_lipschitz e b 1 (smoothPairRowLipschitz k) hLip
    (splitSmoothProductProfile_zero_outside _ _)
  apply h.weaken
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ (by positivity)]
  change inverseJacobian e * (smoothPairRowLipschitz k : ℝ) * (2 * 1) ^ Fintype.card {j : J // j ≠ k} *
    ‖e.symm.toContinuousLinearMap‖ ≤ _
  rw [mul_one]
  have hj := inverseJacobian_le_norm_bound e hinv
  norm_num at hj
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hj (smoothPairRowLipschitz k).coe_nonneg)
    (by positivity : 0 ≤ (2 : ℝ) ^ Fintype.card {j : J // j ≠ k})
  apply (mul_le_mul hm hinv (norm_nonneg _) (by positivity)).trans_eq
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

theorem centeredSmoothAffinePairRows_law {K I : Type*} [Fintype K] [Fintype I]
    (S : Option K → ℝ) (hS : ∀ j, 0 < S j) (t u : K → ℤ) :
    (smoothProductPMF (fun z : Option K × I => S z.1) (fun z => hS z.1)).map
        (smoothAffinePairRows t u) =
      independentProductPMF (fun _ : I => (smoothProductPMF S hS).map
        (fun z => affinePairMatrix t u *ᵥ z)) := by
  have h := congrArg (fun p : PMF (I → Option K → ℤ) =>
    p.map (fun rows i => affinePairMatrix t u *ᵥ rows i))
      (smoothProductPMF_rows (fun z : Option K × I => S z.1) (fun z => hS z.1))
  rw [PMF.map_comp, independentProductPMF_map] at h
  exact h

noncomputable def smoothPairProbabilityError {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (Q : ℕ) (C κ δ : ℝ) : ℝ :=
  normalizedFiberErrorConstant 2 (Fintype.card {j : J // j ≠ k}) Q
    (4 * C / κ) ((Fintype.card J : ℝ) * C) 1 1 (smoothPairRowLipschitz k) * δ

noncomputable def smoothPairProbabilityCap {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (Q : ℕ) (C κ : ℝ) : ℝ :=
  1 + (Q : ℝ) * (2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k})

theorem smooth_pair_actual_row_error {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    {H L C κ δ : ℝ} (Q : ℕ) (hH : 0 < H) (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs ≤ Q)
    (hmesh : ((u k - t k).natAbs : ℝ) * L / H ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) *
      smoothPairRowLipschitz k * δ ≤ 1 / 2) (v : Fin 2 → ℤ) :
    |H ^ 2 * ((smoothProductPMF (smoothPairCoefficientScale H L)
          (smoothPairCoefficientScale_pos hH (zero_lt_one.trans_le hL))).map
          (fun z => affinePairMatrix t u *ᵥ z) v).toReal -
      (if BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0 then
        ((BohrLattice.Primitive.content (fun j => u j - t j)).natAbs : ℝ) *
          affinePairRowDensity t u k hne H L hH (zero_lt_one.trans_le hL)
            (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
            (fun i => (v i : ℝ) / H) else 0)| ≤
      smoothPairProbabilityError k Q C κ δ := by
  obtain ⟨hM, he⟩ := smooth_affinePair_probability_law t u k hne Q hH hL hC hκ
    hδ hδ1 ht hu hgap hQ hmesh hsmall
  rw [smooth_pair_row_law t u k hH (zero_lt_one.trans_le hL) hM]
  exact he v

theorem smooth_pair_product_probability_law {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    {H L C κ δ : ℝ} (Q : ℕ) (hH : 0 < H) (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs ≤ Q)
    (hmesh : ((u k - t k).natAbs : ℝ) * L / H ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) *
      smoothPairRowLipschitz k * δ ≤ 1 / 2) (v : I → Fin 2 → ℤ) :
    |H ^ (2 * Fintype.card I) *
        ((smoothProductPMF (fun z : Option J × I => smoothPairCoefficientScale H L z.1)
          (fun z => smoothPairCoefficientScale_pos hH (zero_lt_one.trans_le hL) z.1)).map
          (smoothAffinePairRows t u) v).toReal -
      (if ∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣ v i 1 - v i 0 then
        ((BohrLattice.Primitive.content (fun j => u j - t j)).natAbs : ℝ) ^ Fintype.card I *
          ∏ i, affinePairRowDensity t u k hne H L hH (zero_lt_one.trans_le hL)
            (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
            (fun j => (v i j : ℝ) / H) else 0)| ≤
      Fintype.card I * smoothPairProbabilityError k Q C κ δ *
        (smoothPairProbabilityCap k Q C κ + smoothPairProbabilityError k Q C κ δ) ^ Fintype.card I := by
  classical
  let density : (Fin 2 → ℤ) → ℝ := fun v =>
    affinePairRowDensity t u k hne H L hH (zero_lt_one.trans_le hL)
      (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)) (fun j => (v j : ℝ) / H)
  let m : ℝ := (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs
  have hrow := smooth_pair_actual_row_error t u k hne Q hH hL hC hκ hδ hδ1 ht hu hgap hQ hmesh hsmall
  have hepsilon : 0 ≤ smoothPairProbabilityError k Q C κ δ := (abs_nonneg _).trans (hrow 0)
  have hbound (v : Fin 2 → ℤ) : |density v| ≤
      2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k} :=
    smooth_affinePairRowDensity_cap t u k hne hH (zero_lt_one.trans_le hL) hC hκ (ht k) (hu k) hgap _
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hmQ : m ≤ Q := by
    dsimp only [m]
    exact_mod_cast hQ
  have hcap0 : 0 ≤ 2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k} := by positivity
  have hB : 1 ≤ smoothPairProbabilityCap k Q C κ := by
    unfold smoothPairProbabilityCap
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hcap0)
  have hcap (v : Fin 2 → ℤ) : |m * density v| ≤ smoothPairProbabilityCap k Q C κ := by
    rw [abs_mul, abs_of_nonneg hm]
    apply (mul_le_mul hmQ (hbound v) (abs_nonneg _) (Nat.cast_nonneg _)).trans
    change (Q : ℝ) * _ ≤ 1 + (Q : ℝ) * _
    linarith
  rw [centeredSmoothAffinePairRows_law]
  have h := independent_masked_row_density_error
    (fun _ : I => (smoothProductPMF (smoothPairCoefficientScale H L)
      (smoothPairCoefficientScale_pos hH (zero_lt_one.trans_le hL))).map
        (fun z => affinePairMatrix t u *ᵥ z))
    (fun _ => H ^ 2) (fun _ v => BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0)
    (fun _ => density) m hB hepsilon (fun _ => hcap) (fun _ x => by
      by_cases hx : BohrLattice.Primitive.content (fun j => u j - t j) ∣ x 1 - x 0
      · simpa only [hx, ite_true, m, density] using hrow x
      · simpa only [hx, ite_false] using hrow x) v
  simpa only [Finset.prod_const, Finset.card_univ, ← pow_mul, density, m] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

theorem affine_pair_shift_divisibility {J : Type*} [Fintype J]
    (t u : J → ℤ) (b : Option J → ℤ) (v : Fin 2 → ℤ) :
    (BohrLattice.Primitive.content (fun j => u j - t j) ∣
      (v 1 - (affinePairMatrix t u *ᵥ b) 1) - (v 0 - (affinePairMatrix t u *ᵥ b) 0)) ↔
      BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0 := by
  have hb : affinePairMatrix t u *ᵥ b ∈ affinePairImage t u := ⟨b, rfl⟩
  have hd := (affinePairImage_iff_content_dvd t u _).mp hb
  rw [show (v 1 - (affinePairMatrix t u *ᵥ b) 1) - (v 0 - (affinePairMatrix t u *ᵥ b) 0) =
    (v 1 - v 0) - ((affinePairMatrix t u *ᵥ b) 1 - (affinePairMatrix t u *ᵥ b) 0) by ring]
  exact dvd_sub_left hd

theorem shifted_smooth_pair_product_probability_law {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    {H L C κ δ : ℝ} (Q : ℕ) (hH : 0 < H) (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs ≤ Q)
    (hmesh : ((u k - t k).natAbs : ℝ) * L / H ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) *
      smoothPairRowLipschitz k * δ ≤ 1 / 2)
    (b : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (b z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale H L z.1))
    (v : I → Fin 2 → ℤ) :
    |H ^ (2 * Fintype.card I) *
        ((shiftedSmoothProductPMF (fun z => (b z : ℝ))
          (fun z : Option J × I => smoothPairCoefficientScale H L z.1)
          (fun z => smoothPairCoefficientScale_pos hH (zero_lt_one.trans_le hL) z.1) hZ).map
          (smoothAffinePairRows t u) v).toReal -
      (if ∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣ v i 1 - v i 0 then
        ((BohrLattice.Primitive.content (fun j => u j - t j)).natAbs : ℝ) ^ Fintype.card I *
          ∏ i, affinePairRowDensity t u k hne H L hH (zero_lt_one.trans_le hL)
            (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
            (fun j => ((v i j - smoothAffinePairRows t u b i j : ℤ) : ℝ) / H) else 0)| ≤
      Fintype.card I * smoothPairProbabilityError k Q C κ δ *
        (smoothPairProbabilityCap k Q C κ + smoothPairProbabilityError k Q C κ δ) ^ Fintype.card I := by
  classical
  rw [shiftedSmoothAffinePairRows_integer_apply]
  have h := smooth_pair_product_probability_law t u k hne Q hH hL hC hκ hδ hδ1 ht hu hgap
    hQ hmesh hsmall (v - smoothAffinePairRows t u b)
  have hm : (∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣
      (v i 1 - smoothAffinePairRows t u b i 1) - (v i 0 - smoothAffinePairRows t u b i 0)) ↔
      (∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣ v i 1 - v i 0) :=
    forall_congr' (fun i => affine_pair_shift_divisibility t u (independentArrayRows b i) (v i))
  simpa only [Pi.sub_apply, hm] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

theorem centeredSmoothAffinePairRows_variable {J I : Type*} [Fintype J] [Fintype I]
    (S : Option J × I → ℝ) (hS : ∀ z, 0 < S z) (t u : J → ℤ) :
    (smoothProductPMF S hS).map (smoothAffinePairRows t u) =
      independentProductPMF (fun i => (smoothProductPMF (fun j => S (j, i))
        (fun j => hS (j, i))).map (fun z => affinePairMatrix t u *ᵥ z)) := by
  have h := congrArg (fun p : PMF (I → Option J → ℤ) =>
    p.map (fun rows i => affinePairMatrix t u *ᵥ rows i)) (smoothProductPMF_rows S hS)
  rw [PMF.map_comp, independentProductPMF_map] at h
  exact h

theorem smoothPairProbabilityError_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (Q : ℕ) (C κ δ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ smoothPairProbabilityError k Q C κ δ := by
  unfold smoothPairProbabilityError normalizedFiberErrorConstant integerFiberErrorConstant
  positivity

theorem anisotropic_smooth_pair_product_probability_law {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i) (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs ≤ Q)
    (hmesh : ∀ i, ((u k - t k).natAbs : ℝ) * L / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) *
      smoothPairRowLipschitz k * δ ≤ 1 / 2) (v : I → Fin 2 → ℤ) :
    |(∏ i, H i ^ 2) *
        ((smoothProductPMF (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
          (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1)).map
          (smoothAffinePairRows t u) v).toReal -
      (if ∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣ v i 1 - v i 0 then
        ((BohrLattice.Primitive.content (fun j => u j - t j)).natAbs : ℝ) ^ Fintype.card I *
          ∏ i, affinePairRowDensity t u k hne (H i) L (hH i) (zero_lt_one.trans_le hL)
            (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
            (fun j => (v i j : ℝ) / H i) else 0)| ≤
      Fintype.card I * smoothPairProbabilityError k Q C κ δ *
        (smoothPairProbabilityCap k Q C κ + smoothPairProbabilityError k Q C κ δ) ^ Fintype.card I := by
  classical
  let density : I → (Fin 2 → ℤ) → ℝ := fun i v =>
    affinePairRowDensity t u k hne (H i) L (hH i) (zero_lt_one.trans_le hL)
      (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)) (fun j => (v j : ℝ) / H i)
  let m : ℝ := (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs
  have hrow (i : I) := smooth_pair_actual_row_error t u k hne Q (hH i) hL hC hκ hδ hδ1 ht hu hgap hQ (hmesh i) hsmall
  have hepsilon : 0 ≤ smoothPairProbabilityError k Q C κ δ := smoothPairProbabilityError_nonneg k Q C κ δ hδ
  have hbound (i : I) (v : Fin 2 → ℤ) : |density i v| ≤
      2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k} :=
    smooth_affinePairRowDensity_cap t u k hne (hH i) (zero_lt_one.trans_le hL) hC hκ (ht k) (hu k) hgap _
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hmQ : m ≤ Q := by
    dsimp only [m]
    exact_mod_cast hQ
  have hcap0 : 0 ≤ 2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k} := by positivity
  have hB : 1 ≤ smoothPairProbabilityCap k Q C κ := by
    unfold smoothPairProbabilityCap
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hcap0)
  have hcap (i : I) (v : Fin 2 → ℤ) : |m * density i v| ≤ smoothPairProbabilityCap k Q C κ := by
    rw [abs_mul, abs_of_nonneg hm]
    apply (mul_le_mul hmQ (hbound i v) (abs_nonneg _) (Nat.cast_nonneg _)).trans
    change (Q : ℝ) * _ ≤ 1 + (Q : ℝ) * _
    linarith
  rw [centeredSmoothAffinePairRows_variable]
  have h := independent_masked_row_density_error
    (fun i : I => (smoothProductPMF (smoothPairCoefficientScale (H i) L)
      (smoothPairCoefficientScale_pos (hH i) (zero_lt_one.trans_le hL))).map
        (fun z => affinePairMatrix t u *ᵥ z))
    (fun i => H i ^ 2) (fun _ v => BohrLattice.Primitive.content (fun j => u j - t j) ∣ v 1 - v 0)
    density m hB hepsilon hcap (fun i x => by
      by_cases hx : BohrLattice.Primitive.content (fun j => u j - t j) ∣ x 1 - x 0
      · simpa only [hx, ite_true, m, density] using hrow i x
      · simpa only [hx, ite_false] using hrow i x) v
  simpa only [density, m] using h

theorem shifted_anisotropic_smooth_pair_product_probability_law {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i) (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs ≤ Q)
    (hmesh : ∀ i, ((u k - t k).natAbs : ℝ) * L / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) *
      smoothPairRowLipschitz k * δ ≤ 1 / 2)
    (b : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (b z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (v : I → Fin 2 → ℤ) :
    |(∏ i, H i ^ 2) *
        ((shiftedSmoothProductPMF (fun z => (b z : ℝ))
          (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
          (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).map
          (smoothAffinePairRows t u) v).toReal -
      (if ∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣ v i 1 - v i 0 then
        ((BohrLattice.Primitive.content (fun j => u j - t j)).natAbs : ℝ) ^ Fintype.card I *
          ∏ i, affinePairRowDensity t u k hne (H i) L (hH i) (zero_lt_one.trans_le hL)
            (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))
            (fun j => ((v i j - smoothAffinePairRows t u b i j : ℤ) : ℝ) / H i) else 0)| ≤
      Fintype.card I * smoothPairProbabilityError k Q C κ δ *
        (smoothPairProbabilityCap k Q C κ + smoothPairProbabilityError k Q C κ δ) ^ Fintype.card I := by
  classical
  rw [shiftedSmoothAffinePairRows_integer_apply]
  have h := anisotropic_smooth_pair_product_probability_law t u k hne H Q hH hL hC hκ hδ hδ1 ht hu hgap
    hQ hmesh hsmall (v - smoothAffinePairRows t u b)
  have hm : (∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣
      (v i 1 - smoothAffinePairRows t u b i 1) - (v i 0 - smoothAffinePairRows t u b i 0)) ↔
      (∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣ v i 1 - v i 0) :=
    forall_congr' (fun i => affine_pair_shift_divisibility t u (independentArrayRows b i) (v i))
  simpa only [Pi.sub_apply, hm] using h

end Erdos3

end

end OAI
