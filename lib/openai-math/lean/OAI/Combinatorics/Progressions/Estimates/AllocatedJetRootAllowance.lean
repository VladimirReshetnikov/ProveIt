import OAI.Combinatorics.Progressions.Geometry.AllocatedJetChartSupport

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem realAffineCube_abs_le_root_allowance {α K : Type*} [Fintype α]
    (root : K → ℝ) (difference : α → K → ℝ) {H : ℝ}
    (hroot : ∀ k, |root k| ≤ H) (hd : ∀ r k, |difference r k| ≤ 1)
    (t : Finset α) (k : K) :
    |realAffineCube root difference t k| ≤ H + Fintype.card α := by
  unfold realAffineCube
  calc
    _ ≤ |root k| + |∑ r ∈ t, difference r k| := abs_add_le _ _
    _ ≤ H + ∑ r ∈ t, |difference r k| :=
      add_le_add (hroot k) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ H + ∑ _r ∈ t, (1 : ℝ) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun r _ => hd r k))
    _ = H + t.card := by simp
    _ ≤ H + Fintype.card α := by
      have hc : (t.card : ℝ) ≤ Fintype.card α := by exact_mod_cast Finset.card_le_univ t
      exact add_le_add le_rfl hc

theorem boundedDegreeRealJetMatrix_entry_root_allowance {α K O : Type*}
    [Fintype α] [DecidableEq α] (root : K → ℝ) (difference : α → K → ℝ)
    {H : ℝ} (hH : 1 ≤ H) (hroot : ∀ k, |root k| ≤ H)
    (hd : ∀ r k, |difference r k| ≤ 1)
    (h : ℕ) (rows : O → Finset α) (o : O) (e : BoundedIntegerExponent K h) :
    |boundedDegreeRealJetMatrix root difference h rows o e| ≤
      (2 : ℝ) ^ Fintype.card α * (H + Fintype.card α) ^ h := by
  have hbase : 1 ≤ H + Fintype.card α := hH.trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hb := booleanCoefficient_abs_le
    (fun t => MvPolynomial.eval (realAffineCube root difference t)
      (MvPolynomial.monomial e.val (1 : ℝ))) (rows o)
    (fun t _ => real_monomial_eval_abs_le e.val _ hbase
      (realAffineCube_abs_le_root_allowance root difference hroot hd t) e.property)
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hbase) _)
  exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ _)

theorem boundedCoefficientJetMatrix_scaled_root_allowance {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℤ) (A : Matrix α K ℤ) (T : K → ℝ) (hT : ∀ k, 0 < T k)
    {H : ℝ} (hH : 1 ≤ H) (hroot : ∀ k, |(root k : ℝ) / T k| ≤ H)
    (hA : ∀ i k, |(A i k : ℝ) / T k| ≤ 1)
    (h : ℕ) (rows : O → Finset α) (o : O) (e : VectorPolynomial.BoundedCoefficientExponent K h) :
    |(boundedCoefficientJetMatrix root A h rows o e : ℝ)| / monomialScale T e.val ≤
      (2 : ℝ) ^ Fintype.card α * (H + Fintype.card α) ^ h := by
  let e' := boundedCoefficientIntegerExponentEquiv K h e
  have he := congrFun (congrFun (normalizedBoundedIntegerJetMatrix_eq root A h rows T
    (H := 1) one_ne_zero) o) e'
  rw [normalizedIntegerColumns_entry_div] at he
  have hb := boundedDegreeRealJetMatrix_entry_root_allowance _ _ hH hroot hA h rows o e'
  rw [← he] at hb
  change |(boundedDegreeIntegerJetMatrix root A h rows o e' : ℝ)| / monomialScale T e'.val ≤ _
  simpa only [div_one, mul_one_div, abs_div, abs_of_pos (monomialScale_pos T hT e'.val)] using hb

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

include hR in
theorem allocatedJetRadius_implies_chartRadius {α : Type*} [Fintype α]
    {H : ℝ} (hH : 1 ≤ H) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hjet : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * (H + Fintype.card α) ^ (j.val + 1)) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * R j)) ≤ 1 / 4) :
    ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4 := by
  intro j
  have hn : 1 ≤ (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨constantCoefficientSlot _ _⟩)
  have hp : 1 ≤ (2 : ℝ) ^ Fintype.card α := one_le_pow₀ (by norm_num)
  have hq : 1 ≤ (H + Fintype.card α) ^ (j.val + 1) :=
    one_le_pow₀ (hH.trans (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  have hfactor := one_le_mul_of_one_le_of_one_le hn (one_le_mul_of_one_le_of_one_le hp hq)
  have hQ : 0 ≤ C j * (((Fintype.card (I j) : ℝ) + 1) * R j) :=
    mul_nonneg (hC j) (mul_nonneg (by positivity) (hR j).le)
  calc
    _ = 1 * (C j * (((Fintype.card (I j) : ℝ) + 1) * R j)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor hQ
    _ ≤ 1 / 4 := hjet j

theorem allocatedLayerSupported_matrix_quarter
    (hσ1 : ∀ j, σ j ≤ 1) (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (j : Fin m) {O : Type*}
    (A : Matrix O (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) ℤ)
    (M : ℝ)
    (hA : ∀ t e, |(A t e : ℝ)| / monomialScale (layerSamplerBox B U b S) e.val ≤ M)
    (hsmall : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      M * (C j * (((Fintype.card (I j) : ℝ) + 1) * R j)) ≤ 1 / 4)
    (a) (ha : mixedArraySupported (allocatedLayerCenters B U b S j) (allocatedLayerWidths B U b S j)
      (allocatedLayerIntegerPMFs B U b hR hσ S j) a) (t : O) (i : J j) :
    |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (mixedArrayIntegerImage A a) t)) i| ≤ 1 / 4 := by
  classical
  let T := layerSamplerBox B U b S
  let Q := C j * (((Fintype.card (I j) : ℝ) + 1) * R j)
  have hT (k) : 0 < T k := lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)
  have hQ : 0 ≤ Q := mul_nonneg (hC j) (mul_nonneg (by positivity) (hR j).le)
  have hc (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :
      |mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) a e i| ≤ Q / monomialScale T e.val := by
    have h := allocatedLayerCoefficient_scaled_bounds B U b hR hσ S hσ1 j a ha e
    exact mixedRealPoint_scaled_coordinate_bound _ (b j) (o j) (hC j) (hR j).le
      (monomialScale_pos T hT e.val) (hchart j) _ _ h.1 h.2 i
  have hterm (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :
      |(A t e : ℝ) * mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) a e i| ≤ M * Q := by
    rw [abs_mul]
    calc
      _ ≤ |(A t e : ℝ)| * (Q / monomialScale T e.val) :=
        mul_le_mul_of_nonneg_left (hc e) (abs_nonneg _)
      _ = (|(A t e : ℝ)| / monomialScale T e.val) * Q := by ring
      _ ≤ M * Q := mul_le_mul_of_nonneg_right (hA t e) hQ
  have he := congrArg (fun v : EuclideanSpace ℝ (J j) => v i)
    (mixedArrayIntegerImage_point (euclideanSubspace (U j)) (b j) (o j) A a t)
  change _ = (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : J j => ℝ) i) _ at he
  rw [map_sum] at he
  simp only [map_zsmul, zsmul_eq_mul] at he
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1), M * Q :=
      Finset.sum_le_sum (fun e _ => hterm e)
    _ = (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) * M * Q := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
    _ ≤ 1 / 4 := hsmall

theorem allocatedLayerSupported_jet_root_allowance {α : Type*} [Fintype α] [DecidableEq α]
    {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (root : LayerSamplerVariables G I n B → ℤ)
    (A : Matrix α (LayerSamplerVariables G I n B) ℤ) (rows : ∀ j, O j → Finset α)
    {H : ℝ} (hH : 1 ≤ H) (hroot : ∀ k, |(root k : ℝ) / layerSamplerBox B U b S k| ≤ H)
    (hA : ∀ i k, |(A i k : ℝ) / layerSamplerBox B U b S k| ≤ 1)
    (hσ1 : ∀ j, σ j ≤ 1) (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * (H + Fintype.card α) ^ (j.val + 1)) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * R j)) ≤ 1 / 4)
    (j : Fin m) (a) (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (t : O j) (i : J j) :
    |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _
        (mixedArrayIntegerImage (boundedCoefficientJetMatrix root A (j.val + 1) (rows j)) a) t)) i| ≤ 1 / 4 := by
  exact allocatedLayerSupported_matrix_quarter B U b hR hσ S hσ1 o C hC hchart j
    (boundedCoefficientJetMatrix root A (j.val + 1) (rows j)) _
    (boundedCoefficientJetMatrix_scaled_root_allowance root A (layerSamplerBox B U b S)
      (fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)) hH hroot hA _ (rows j))
    (hsmall j) a ha t i

end Erdos3.VectorPolynomial

end

end OAI
