import OAI.Combinatorics.Progressions.Dynamics.SharedRefinementBudget
import OAI.Combinatorics.Progressions.Linear.RealFourBalancedDual

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem exists_native_full_coefficient_corrections (hs : 1 ≤ s) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples) :
    let I := R.interval ⟨t, D.subset ht⟩
    let V : I.SunflowerWitness P := D.witness t ht
    ∃ E Q : ∀ α : Unit →₀ ℕ,
        (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ,
      (∀ α j, |(W.fourRankBasis.baseChange ℝ).repr (E α).val j| ≤
        Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α) ∧
      (∀ α, (W.fourRankBasis.baseChange ℝ).equivFun (Q α).val ∈
        realDenominatorGrid V.projectedDenominator) ∧
      ∀ (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s),
        (fun k => coefficients
          (W.orbit (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α) -
          (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) (E α).val -
          (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) (Q α).val ∈
            D.realCoefficientFourSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ := by
  intro I V
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.exists_bounded_coefficient_corrections hs hP t ht
  refine ⟨E, Q, hE, hQ, ?_⟩
  intro α hα
  let d : Fin (s + 1) := ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩
  let e4 := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)
  let u := e4 (V.projectedOrbitCoefficient α).val
  let β : Fin 4 → ℝ ⊗[ℚ] W.L := fun k => coefficients
    (W.orbit (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α
  let e := e4 (E α).val
  let a := e4 (Q α).val
  have hu : u - e - a ∈ D.realCoefficientFourSpace d := by
    have h := (D.mem_real_coefficientFourSpace d (V.projectedOrbitCoefficient α - E α - Q α)).mpr
      (hres α hα)
    simpa only [Submodule.coe_sub, map_sub] using h
  have hk (k : Fin 4) : (u - e - a) k - (β - e - a) k ∈
      (W.rank.filtration.layer d.val 2).baseChange ℝ := by
    have heq : (u - e - a) k - (β - e - a) k = u k - β k := by
      simp only [Pi.sub_apply]
      abel
    rw [heq]
    exact V.projectedOrbitCoefficient_native_log_mod_kernel hs c τ hG α k
  exact (D.realCoefficientFourSpace_congr_mod_kernel d _ _ hk).mp hu

theorem native_full_scaled_correction (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples) :
    ∃ E Q : ℝ ⊗[ℚ] (Fin 4 → W.L),
      ‖(W.fourRankBasis.baseChange ℝ).equivFun E‖ ≤
        Real.exp ((P + 3) ^ 2 + (s : ℝ) * p) / monomialScale (fun _ : Unit => (N : ℝ)) α ∧
      (W.fourRankBasis.baseChange ℝ).equivFun Q ∈ realDenominatorGrid l ∧
      (fun k => coefficients
        (W.orbit (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α) -
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) E -
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) Q ∈
          D.realCoefficientFourSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ := by
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.exists_native_full_coefficient_corrections hs hP c τ hG t ht
  let I := R.interval ⟨t, D.subset ht⟩
  have hlength : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  have hnorm : ‖(W.fourRankBasis.baseChange ℝ).equivFun (E α).val‖ ≤
      Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg (Real.exp_pos _).le
      (monomialScale_pos _ (fun _ => hlength) α).le)).mpr
    exact fun j => hE α j
  refine ⟨(E α).val, (Q α).val, ?_, ?_, hres α hα⟩
  · have h := I.norm_bound_on_modulus hp α hα (Real.exp_pos _).le
      ((W.fourRankBasis.baseChange ℝ).equivFun (E α).val) hnorm
    simpa only [Real.exp_add] using h
  · simpa only [hdenom t ht] using hQ α

theorem exists_uniform_native_full_scaled_corrections (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i})) :
    let B := (P + 2) ^ 3 + 2 * P
    ∃ (C : R.CommonData B) (l : ℕ), C.quadruples ⊆ D.quadruples ∧ C.spaces = D.spaces ∧
      0 < l ∧ (l : ℝ) ≤ Real.exp ((P + 2) ^ 3 + P) ∧
      ∀ (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
        (t : ZMod N × ZMod N × ZMod N), t ∈ C.quadruples →
        ∃ E Q : ℝ ⊗[ℚ] (Fin 4 → W.L),
          ‖(W.fourRankBasis.baseChange ℝ).equivFun E‖ ≤
            Real.exp ((B + 3) ^ 2 + (s : ℝ) * p) / monomialScale (fun _ : Unit => (N : ℝ)) α ∧
          (W.fourRankBasis.baseChange ℝ).equivFun Q ∈ realDenominatorGrid l ∧
          (fun k => coefficients
            (W.orbit (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α) -
            (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) E -
            (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) Q ∈
              C.realCoefficientFourSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ := by
  intro B
  obtain ⟨C, l, hCD, hspaces, hl, hbound, hdenom⟩ := D.exists_common_projected_denominator hP
  refine ⟨C, l, hCD, hspaces, hl, hbound, ?_⟩
  intro α hα t ht
  exact C.native_full_scaled_correction hs hp (by positivity)
    c τ hG l hdenom α hα t ht

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

noncomputable def sharedLogCoefficientTuple
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s N : ℕ}
    (F : NilpotentLieFiltration L s)
    (ξ : F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) (t : ZMod N × ZMod N × ZMod N) : Fin 4 → ℝ ⊗[ℚ] L :=
  fun k => coefficients ξ.log α + coefficients
    (v (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α

theorem sharedLogCoefficientTuple_mem_common
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s N : ℕ}
    (F : NilpotentLieFiltration L s) (C D : Submodule ℚ L) (hDC : D ≤ C)
    (ξ : F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) (t : ZMod N × ZMod N × ZMod N)
    (hξ : coefficients ξ.log α ∈ C.baseChange ℝ)
    (hv : ∀ h, coefficients (v h).log α ∈ D.baseChange ℝ) :
    sharedLogCoefficientTuple F ξ v α t ∈ fourCommonModulo (C.baseChange ℝ) (D.baseChange ℝ) := by
  apply (mem_fourCommonModulo _ _ _).mpr
  constructor
  · intro k
    exact (C.baseChange ℝ).add_mem hξ (Submodule.baseChange_mono ℝ hDC (hv _))
  · intro k
    change (coefficients ξ.log α + coefficients (v _).log α) -
      (coefficients ξ.log α + coefficients (v _).log α) ∈ D.baseChange ℝ
    rw [add_sub_add_left_eq_sub]
    exact (D.baseChange ℝ).sub_mem (hv _) (hv _)

namespace NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem native_shared_scaled_correction (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (ξ : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (horbit : ∀ h, W.orbit h = ξ * v h)
    (l : ℕ) (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples) :
    ∃ E Q : ℝ ⊗[ℚ] (Fin 4 → W.L),
      ‖(W.fourRankBasis.baseChange ℝ).equivFun E‖ ≤
        Real.exp ((P + 3) ^ 2 + (s : ℝ) * p) / monomialScale (fun _ : Unit => (N : ℝ)) α ∧
      (W.fourRankBasis.baseChange ℝ).equivFun Q ∈ realDenominatorGrid l ∧
      sharedLogCoefficientTuple W.model.filtration ξ v α t -
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) E -
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) Q ∈
          D.realCoefficientFourSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ := by
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.native_full_scaled_correction hs hp hP c τ hG
    l hdenom α hα t ht
  refine ⟨E, Q, hE, hQ, ?_⟩
  apply (D.realCoefficientFourSpace_congr_mod_kernel _ _ _ ?_).mp hres
  intro k
  let a := rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)
  let e := (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) E k
  let z := (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) Q k
  change (coefficients (W.orbit a).log α - e - z) -
    (coefficients ξ.log α + coefficients (v a).log α - e - z) ∈ _
  rw [horbit a]
  have heq : (coefficients (ξ * v a).log α - e - z) -
      (coefficients ξ.log α + coefficients (v a).log α - e - z) =
      coefficients (ξ * v a).log α - (coefficients ξ.log α + coefficients (v a).log α) := by abel
  rw [heq]
  exact W.rank.orbit_log_mul_mod_rank_two hs c τ hG (fun _ : Unit => 1) α ξ (v a)

end NativeRankRelation.CommonData
end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

theorem sharedLogCoefficientTuple_annihilator_decomposition
    {L J : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype J] {s N : ℕ}
    (F : NilpotentLieFiltration L s) (C D : Submodule ℚ L) (hDC : D ≤ C)
    (ℓ : (Fin 4 → L) →ₗ[ℚ] (J → ℚ))
    (hℓ : fourBalancedDependent D ≤ LinearMap.ker ℓ)
    (ξ : F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) (t : ZMod N × ZMod N × ZMod N)
    (hξ : coefficients ξ.log α ∈ C.baseChange ℝ)
    (hv : ∀ h, coefficients (v h).log α ∈ D.baseChange ℝ) :
    let φ := ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => L) 0)
    let a := fun h => realifyCoordinateMap φ (coefficients (v h).log α)
    realFourCoordinateMap ℓ (sharedLogCoefficientTuple F ξ v α t) =
      realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) (coefficients ξ.log α) +
        (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
          a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) := by
  intro φ a
  have h := realFourCoordinateMap_shared_decomposition C D hDC ℓ hℓ
    (coefficients ξ.log α) hξ
    (fun k => coefficients (v (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α)
    (fun k => hv _)
  change realFourCoordinateMap ℓ (sharedLogCoefficientTuple F ξ v α t) =
    realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) (coefficients ξ.log α) +
      realifyCoordinateMap φ
        (coefficients (v (rankQuadrupleParameters t 1)).log α +
          coefficients (v (rankQuadrupleParameters t 2)).log α -
          coefficients (v (rankQuadrupleParameters t 0)).log α -
          coefficients (v (rankQuadrupleParameters t 3)).log α) at h
  simpa only [map_add, map_sub] using h

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem exists_uniform_shared_refinement
    (hs : 2 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P) (hbP : b ≤ P) (hpP : p ≤ P)
    (U V : Fin s → Submodule ℚ W.L) (hVU : ∀ d, V d ≤ U d)
    (u : ∀ d, Basis (Fin (finrank ℚ (U d))) ℚ (U d))
    (v : ∀ d, Basis (Fin (finrank ℚ (V d))) ℚ (V d))
    (hu : ∀ d a i, rationalLogHeight (W.model.basis.repr (u d a : W.L) i) ≤ P)
    (hv : ∀ d a i, rationalLogHeight (W.model.basis.repr (v d a : W.L) i) ≤ P)
    (ξ : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (g : ZMod N → W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (horbit : ∀ h, W.orbit h = ξ * g h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈ (U d).baseChange ℝ)
    (hg : ∀ h (d : Fin s), coefficients (g h).log (Finsupp.single () (d.val + 1)) ∈
      (V d).baseChange ℝ)
    (hN : Real.exp (separationBudget (8 * sharedRefinementInputBudget s P + 1)) ≤ (N : ℝ)) :
    let B := (P + 2) ^ 3 + 2 * P
    let z := 8 * sharedRefinementInputBudget s P + 1
    ∃ D₁ : R.CommonData B, D₁.quadruples ⊆ D.quadruples ∧ D₁.spaces = D.spaces ∧
      ∀ d : Fin s, ∃ m : ℕ, 0 < m ∧
        (m : ℝ) ≤ Real.exp (z + ((z + 2) ^ 3 + (z + 2) ^ 36)) ∧
        ∀ t ∈ D₁.quadruples, ∃ E Q : ℝ ⊗[ℚ] (Fin 4 → W.L),
          ‖(W.fourRankBasis.baseChange ℝ).equivFun E‖ ≤
            (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
              monomialScale (fun _ : Unit => (N : ℝ)) (Finsupp.single () (d.val + 1)) ∧
          (W.fourRankBasis.baseChange ℝ).equivFun Q ∈ realDenominatorGrid m ∧
          (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)).symm
              (sharedLogCoefficientTuple W.model.filtration ξ g (Finsupp.single () (d.val + 1)) t) -
            E - Q ∈ (fourRefinedRelation (U d) (V d)
              (D.coefficientFourSpace ⟨d.val + 1, by omega⟩)).baseChange ℝ := by
  intro B z
  classical
  let A := sharedRefinementInputBudget s P
  obtain ⟨hB, hPB, hA, hPA, hHA, hEA, hLA⟩ := sharedRefinementInputBudget_bounds s hP
  have hAz : A ≤ z := by dsimp only [z, A]; linarith
  have hdim : (Fintype.card (Fin W.dim) : ℝ) ≤ A := by
    simpa only [Fintype.card_fin] using W.complexity.1.1.trans (hbP.trans hPA)
  let : FiniteDimensional ℚ W.L := W.model.basis.finiteDimensional_of_finite
  obtain ⟨c, τ, _, _, hF⟩ := W.rank.filtration.associatedDegree.exists_sorted_adapted_basis
  obtain ⟨D₁, l, hsub, hspaces, hl, hlbound, hdenom⟩ := D.exists_common_projected_denominator hP
  refine ⟨D₁, hsub, hspaces, ?_⟩
  intro d
  let δ : Fin (s + 1) := ⟨d.val + 1, by omega⟩
  let α : Unit →₀ ℕ := Finsupp.single () (d.val + 1)
  have hα : Finsupp.weight (fun _ : Unit => 1) α = δ.val := by
    simp only [α, δ, Finsupp.weight_single, smul_eq_mul, mul_one]
  have hαs : Finsupp.weight (fun _ : Unit => 1) α ≤ s := by rw [hα]; exact Nat.le_of_lt_succ δ.isLt
  have hα0 : α ≠ 0 := by simp [α]
  obtain ⟨k, hk⟩ := D₁.exists_coefficientFour_basis hs hB (hbP.trans hPB) δ
  have hlA : (l : ℝ) ≤ Real.exp A := hlbound.trans (Real.exp_le_exp.mpr hLA)
  obtain ⟨m, hm, hmp, _, hsolve⟩ := exists_fourRefinedRelation_correction W.model.basis
    (U d) (V d) (hVU d) (D₁.coefficientFourSpace δ) (u d) (v d) k hA hdim
    (fun a i => (hu d a i).trans hPA) (fun a i => (hv d a i).trans hPA)
    (fun a i => (hk a i).trans hHA) l hl hlA (fun _ : Unit => (N : ℝ)) (fun _ => hN)
  refine ⟨m, hm, hmp, ?_⟩
  intro t ht
  obtain ⟨E₀, Q₀, hE₀, hQ₀, hres⟩ := D₁.native_shared_scaled_correction (by omega) hp hB
    c τ hF ξ g horbit l hdenom α hαs t ht
  have hδ : (⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hαs⟩ : Fin (s + 1)) = δ :=
    Fin.ext hα
  rw [hδ] at hres
  let e4 := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)
  let β := sharedLogCoefficientTuple W.model.filtration ξ g α t
  let x := e4.symm β
  have hxK : x - E₀ - Q₀ ∈ (D₁.coefficientFourSpace δ).baseChange ℝ := by
    change β - e4 E₀ - e4 Q₀ ∈ ((D₁.coefficientFourSpace δ).baseChange ℝ).map e4.toLinearMap at hres
    have h := (Submodule.mem_map_equiv _).mp hres
    change e4.symm (β - e4 E₀ - e4 Q₀) ∈ _ at h
    rw [map_sub, map_sub, e4.symm_apply_apply, e4.symm_apply_apply] at h
    exact h
  have hxS : x ∈ (fourCommonModulo (U d) (V d)).baseChange ℝ := by
    have h := sharedLogCoefficientTuple_mem_common W.model.filtration (U d) (V d) (hVU d)
      ξ g α t (hξ d) (fun h => hg h d)
    rw [← realification_fourCommonModulo] at h
    exact (Submodule.mem_map_equiv _).mp h
  have herror : (B + 3) ^ 2 + (s : ℝ) * p ≤ z := by
    have hmul := mul_le_mul_of_nonneg_left hpP (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
    exact (add_le_add_right hmul _).trans (hEA.trans hAz)
  have hEbound : ‖(W.fourRankBasis.baseChange ℝ).equivFun E₀‖ ≤
      Real.exp z / monomialScale (fun _ : Unit => (N : ℝ)) α := by
    apply hE₀.trans
    apply div_le_div_of_nonneg_right (Real.exp_le_exp.mpr herror)
    exact (monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) α).le
  obtain ⟨E, Q, hE, hQ, hmem⟩ := hsolve α hα0 x E₀ Q₀ hxK hxS hEbound hQ₀
  have hK : D₁.coefficientFourSpace δ = D.coefficientFourSpace δ := by
    rw [D₁.coefficientFourSpace_eq_sup, D.coefficientFourSpace_eq_sup, hspaces]
  rw [hK] at hmem
  exact ⟨E, Q, hE, hQ, hmem⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_correlation_refined_basis (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P')
    (d : Fin s) :
    ∃ a : Basis (Fin (finrank ℚ (fourRefinedRelation (D.coefficientFreeSpan d)
        (D.dependentFreeSpan d) (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)))) ℚ
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)),
      ∀ j i, rationalLogHeight ((Pi.basis (fun _ : Fin 4 => E.basis)).repr
        (a j : Fin 4 → D.CoefficientFreeLieAlgebra) i) ≤
          fourRefinementBasisBudget (Q + coefficientFourHeightBudget P') := by
  obtain ⟨c, hc⟩ := D.exists_coefficientFreeSpan_basis E.basis F (by omega) d
  obtain ⟨b, hb⟩ := D.exists_dependentFreeSpan_basis E.basis F (by omega) d
  obtain ⟨k, hk⟩ := D'.exists_coefficientFour_basis hs hP' hQP' ⟨d.val + 1, by omega⟩
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hB := coefficientFourHeightBudget_nonneg hP'
  have hQA : Q ≤ Q + coefficientFourHeightBudget P' := le_add_of_nonneg_right hB
  have hBA : coefficientFourHeightBudget P' ≤ Q + coefficientFourHeightBudget P' :=
    le_add_of_nonneg_left hQ
  apply exists_fourRefinedRelation_basis_logHeight E.basis _ _
    (D.dependentFreeSpan_le_coefficientFreeSpan d) _ c b k (add_nonneg hQ hB)
    (by simpa only [Fintype.card_fin] using hT.1.1.trans hQA)
    (fun a i => (hc a i).trans hQA) (fun a i => (hb a i).trans hQA)
  exact fun a i => (hk a i).trans hBA

theorem exists_correlation_refined_annihilator (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P')
    (d : Fin s) :
    ∃ m : ℕ, m ≤ 4 * finrank ℚ D.CoefficientFreeLieAlgebra ∧
      ∃ ℓ : (Fin 4 → D.CoefficientFreeLieAlgebra) →ₗ[ℚ] (Fin m → ℚ),
        Function.Surjective ℓ ∧ LinearMap.ker ℓ =
          fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩) ∧
        (∀ k i j, rationalLogHeight (ℓ (LinearMap.single ℚ
          (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) k (E.basis i)) j) ≤
            fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P')) ∧
        (∀ x ∈ D.dependentFreeSpan d, ℓ (fourDiagonalMap (R := ℚ) x) = 0) ∧
        (∀ z ∈ fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩),
          ℓ (fourDiagonalMap (R := ℚ) (z 0)) +
            ℓ (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0
              (z 0 + z 1 - z 2 - z 3)) = 0) ∧
        fourPetalSpace (D.dependentFreeSpan d)
          (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)) =
          D.dependentFreeSpan d ⊓ LinearMap.ker
            (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0)) := by
  obtain ⟨c, hc⟩ := D.exists_coefficientFreeSpan_basis E.basis F (by omega) d
  obtain ⟨b, hb⟩ := D.exists_dependentFreeSpan_basis E.basis F (by omega) d
  obtain ⟨k, hk⟩ := D'.exists_coefficientFour_basis hs hP' hQP' ⟨d.val + 1, by omega⟩
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hB := coefficientFourHeightBudget_nonneg hP'
  have hQA : Q ≤ Q + coefficientFourHeightBudget P' := le_add_of_nonneg_right hB
  have hBA : coefficientFourHeightBudget P' ≤ Q + coefficientFourHeightBudget P' :=
    le_add_of_nonneg_left hQ
  simpa only [Fintype.card_fin] using
    exists_fourRefinedRelation_annihilator E.basis _ _
      (D.dependentFreeSpan_le_coefficientFreeSpan d) _ c b k (add_nonneg hQ hB)
      (by simpa only [Fintype.card_fin] using hT.1.1.trans hQA)
      (fun a i => (hc a i).trans hQA) (fun a i => (hb a i).trans hQA)
      (fun a i => (hk a i).trans hBA)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_controlled_shared_free_refinement
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp (separationBudget (8 * sharedRefinementInputBudget s P' + 1)) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let z := 8 * sharedRefinementInputBudget s P' + 1
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∀ d : Fin s, ∃ m : ℕ, 0 < m ∧
        (m : ℝ) ≤ Real.exp (z + ((z + 2) ^ 3 + (z + 2) ^ 36)) ∧
        ∀ t ∈ D₁.quadruples, ∃ A S : ℝ ⊗[ℚ] (Fin 4 → D.CoefficientFreeLieAlgebra),
          ‖((Pi.basis (fun _ : Fin 4 => E.basis)).baseChange ℝ).equivFun A‖ ≤
            (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
              monomialScale (fun _ : Unit => (N : ℝ)) (Finsupp.single () (d.val + 1)) ∧
          ((Pi.basis (fun _ : Fin 4 => E.basis)).baseChange ℝ).equivFun S ∈ realDenominatorGrid m ∧
          (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra)).symm
              (sharedLogCoefficientTuple E.filtration ξ v (Finsupp.single () (d.val + 1)) t) - A - S ∈
            (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
              (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).baseChange ℝ := by
  have hC := fun d : Fin s => D.exists_coefficientFreeSpan_basis E.basis F (by omega) d
  have hD := fun d : Fin s => D.exists_dependentFreeSpan_basis E.basis F (by omega) d
  choose c hc using hC
  choose a ha using hD
  exact D'.exists_uniform_shared_refinement hs hp' hP' hQP' hpp'
    D.coefficientFreeSpan D.dependentFreeSpan D.dependentFreeSpan_le_coefficientFreeSpan c a
    (fun d j i => (hc d j i).trans hQP') (fun d j i => (ha d j i).trans hQP') ξ v hsplit
    (fun d => Submodule.baseChange_mono ℝ (D.commonFreeSpan_le_coefficientFreeSpan d) (hξ d)) hv hN

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_real_correlation_refined_equations
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P') (d : Fin s) :
    ∃ m : ℕ, m ≤ 4 * finrank ℚ D.CoefficientFreeLieAlgebra ∧
      ∃ ℓ : (Fin 4 → D.CoefficientFreeLieAlgebra) →ₗ[ℚ] (Fin m → ℚ),
        Function.Surjective ℓ ∧ LinearMap.ker ℓ =
          fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩) ∧
        (∀ k i j, rationalLogHeight (ℓ (LinearMap.single ℚ
          (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) k (E.basis i)) j) ≤
            fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P')) ∧
        (∀ v : Fin 4 → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra,
          v ∈ fourRefinedRelation ((D.coefficientFreeSpan d).baseChange ℝ)
            ((D.dependentFreeSpan d).baseChange ℝ)
            (D'.realCoefficientFourSpace ⟨d.val + 1, by omega⟩) ↔
          ∀ j, realifyFunctional ((LinearMap.proj j).comp ℓ)
            ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra)).symm v) = 0) ∧
        (∀ v : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra,
          v ∈ fourPetalSpace ((D.dependentFreeSpan d).baseChange ℝ)
            (fourRefinedRelation ((D.coefficientFreeSpan d).baseChange ℝ)
              ((D.dependentFreeSpan d).baseChange ℝ)
              (D'.realCoefficientFourSpace ⟨d.val + 1, by omega⟩)) ↔
          v ∈ (D.dependentFreeSpan d).baseChange ℝ ∧ ∀ j, realifyFunctional
            (((LinearMap.proj j).comp ℓ).comp
              (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0)) v = 0) := by
  obtain ⟨m, hm, ℓ, hsurj, hker, hheight, _, _, _⟩ :=
    D.exists_correlation_refined_annihilator E T hbQ hT F V g hg D' hs hP' hQP' d
  have hspace := realification_fourRefinedRelation (D.coefficientFreeSpan d)
    (D.dependentFreeSpan d) (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)
  change _ = fourRefinedRelation ((D.coefficientFreeSpan d).baseChange ℝ)
    ((D.dependentFreeSpan d).baseChange ℝ)
    (D'.realCoefficientFourSpace ⟨d.val + 1, by omega⟩) at hspace
  refine ⟨m, hm, ℓ, hsurj, hker, hheight, ?_, ?_⟩
  · intro v
    rw [← hspace]
    exact mem_real_four_annihilator_iff _ ℓ hker v
  · intro v
    have hpetal := realification_fourPetalSpace (D.dependentFreeSpan d)
      (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))
    rw [hspace] at hpetal
    rw [← hpetal]
    exact mem_real_petal_annihilator_iff _ _ ℓ hker v

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

noncomputable def sharedFreeEquationInputBudget (s : ℕ) (q p : ℝ) : ℝ :=
  let z := 8 * sharedRefinementInputBudget s p + 1
  4 * p + (fourRefinementAnnihilatorBudget (q + coefficientFourHeightBudget p) + 1) +
    (z + ((z + 2) ^ 3 + (z + 2) ^ 36))

theorem sharedFreeEquationInputBudget_bounds (s : ℕ) {q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) :
    let z := 8 * sharedRefinementInputBudget s p + 1
    let a := fourRefinementAnnihilatorBudget (q + coefficientFourHeightBudget p)
    let A := sharedFreeEquationInputBudget s q p
    0 ≤ A ∧ 4 * p ≤ A ∧ a + 1 ≤ A ∧ z + ((z + 2) ^ 3 + (z + 2) ^ 36) ≤ A := by
  intro z a A
  have hi := (sharedRefinementInputBudget_bounds s hp).2.2.1
  have hz : 0 ≤ z := by dsimp only [z]; linarith
  have ha : 0 ≤ a :=
    fourRefinementAnnihilatorBudget_nonneg (add_nonneg hq (coefficientFourHeightBudget_nonneg hp))
  have hZ : 0 ≤ z + ((z + 2) ^ 3 + (z + 2) ^ 36) := by positivity
  have hA : A = 4 * p + (a + 1) + (z + ((z + 2) ^ 3 + (z + 2) ^ 36)) := rfl
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

namespace NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_controlled_shared_free_equations
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp (separationBudget (8 * sharedRefinementInputBudget s P' + 1)) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let z := 8 * sharedRefinementInputBudget s P' + 1
    let A := sharedFreeEquationInputBudget s Q P'
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∀ d : Fin s, ∃ n : ℕ, n ≤ 4 * finrank ℚ D.CoefficientFreeLieAlgebra ∧
        ∃ ℓ : (Fin 4 → D.CoefficientFreeLieAlgebra) →ₗ[ℚ] (Fin n → ℚ),
          Function.Surjective ℓ ∧ LinearMap.ker ℓ =
            fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
              (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩) ∧
          (∀ k i j, rationalLogHeight (ℓ (LinearMap.single ℚ
            (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) k (E.basis i)) j) ≤
              fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P')) ∧
          ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((A + 2) ^ 4) ∧
            let α := Finsupp.single () (d.val + 1)
            let φ := ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0)
            let a := fun h => realifyCoordinateMap φ (coefficients (v h).log α)
            let c := realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) (coefficients ξ.log α)
            ∀ t ∈ D₁.quadruples, ∃ q ∈ realDenominatorGrid m,
              ‖c + (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
                a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) - q‖ ≤
                Real.exp ((A + 2) ^ 3) *
                  ((Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
                    monomialScale (fun _ : Unit => (N : ℝ)) α) := by
  intro B z A
  classical
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  obtain ⟨hA, hdimA, hheightA, hdenomA⟩ := sharedFreeEquationInputBudget_bounds s hQ hP'
  obtain ⟨D₁, hsub, hspaces, hcorr⟩ :=
    D.exists_controlled_shared_free_refinement E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  refine ⟨D₁, hsub, hspaces, ?_⟩
  intro d
  obtain ⟨n, hn, ℓ, hsurj, hker, hheight, _, _, _⟩ :=
    D.exists_correlation_refined_annihilator E T hbQ hT F V g hg D' hs hP' hQP' d
  obtain ⟨l, hl, hlp, hcorr⟩ := hcorr d
  let e4 := Pi.basis (fun _ : Fin 4 => E.basis)
  let H := ⌈Real.exp (fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P'))⌉₊
  have hheightH : ∀ j i, RationalHeightLE (ℓ (e4 i) j) H := by
    intro j i
    apply rationalHeightLE_ceil_exp
    have he : e4 i = LinearMap.single ℚ
        (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) i.1 (E.basis i.2) := by
      simp only [e4, Pi.basis_apply, LinearMap.single_apply]
    rw [he]
    exact hheight i.1 i.2 j
  have hdim : (4 : ℝ) * finrank ℚ D.CoefficientFreeLieAlgebra ≤ 4 * P' :=
    mul_le_mul_of_nonneg_left (hT.1.1.trans hQP') (by norm_num)
  have hI : (Fintype.card (Σ _ : Fin 4, Fin (finrank ℚ D.CoefficientFreeLieAlgebra)) : ℝ) ≤ A := by
    simpa only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using hdim.trans hdimA
  have hJ : (Fintype.card (Fin n) : ℝ) ≤ A := by
    have hn' := (Nat.cast_le (α := ℝ)).mpr hn
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hn'
    simpa only [Fintype.card_fin] using hn'.trans (hdim.trans hdimA)
  have hH : (H : ℝ) ≤ Real.exp A :=
    (ceil_exp_le_exp_add_one (fourRefinementAnnihilatorBudget_nonneg
      (add_nonneg hQ (coefficientFourHeightBudget_nonneg hP')))).trans
        (Real.exp_le_exp.mpr hheightA)
  have hlA : (l : ℝ) ≤ Real.exp A := hlp.trans (Real.exp_le_exp.mpr hdenomA)
  obtain ⟨m, hm, hmA, _, hsolve⟩ :=
    exists_real_annihilator_correction e4 ℓ hheightH hA hI hJ hH hl hlA
  refine ⟨n, hn, ℓ, hsurj, hker, hheight, m, hm, hmA, ?_⟩
  intro α φ a c t ht
  obtain ⟨E₀, Q₀, hE₀, hQ₀, hmem⟩ := hcorr t ht
  rw [← hker] at hmem
  obtain ⟨q, hq, hbound⟩ := hsolve _ E₀ Q₀ _ hmem hE₀ hQ₀
  refine ⟨q, hq, ?_⟩
  have hbalanced : fourBalancedDependent (D.dependentFreeSpan d) ≤ LinearMap.ker ℓ := by
    rw [hker]
    exact fourBalancedDependent_le_refined _ _ _
  have hdecomp := sharedLogCoefficientTuple_annihilator_decomposition E.filtration
    (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
    (D.dependentFreeSpan_le_coefficientFreeSpan d) ℓ hbalanced ξ v α t
    (Submodule.baseChange_mono ℝ (D.commonFreeSpan_le_coefficientFreeSpan d) (hξ d))
    (fun h => hv h d)
  change realFourCoordinateMap ℓ (sharedLogCoefficientTuple E.filtration ξ v α t) =
    c + (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
      a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) at hdecomp
  change ‖realFourCoordinateMap ℓ (sharedLogCoefficientTuple E.filtration ξ v α t) - q‖ ≤ _ at hbound
  rw [hdecomp] at hbound
  exact hbound

end NativeRankRelation.CommonData
end Erdos3

end

section

namespace Erdos3

theorem sharedFree_rounding_small {A z : ℝ} (hA : 0 ≤ A) (hz : 0 ≤ z)
    (hbudget : z + ((z + 2) ^ 3 + (z + 2) ^ 36) ≤ A)
    (N l d : ℕ) [NeZero N] (hd : 1 ≤ d)
    (hl : (l : ℝ) ≤ Real.exp ((A + 2) ^ 4))
    (hN : Real.exp ((A + 2) ^ 5) ≤ (N : ℝ)) :
    2 * (l : ℝ) * (Real.exp ((A + 2) ^ 3) *
      ((Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) / (N : ℝ) ^ d)) ≤ 1 := by
  have hzA : z ≤ A := by
    have h3 : 0 ≤ (z + 2) ^ 3 := by positivity
    have h36 : 0 ≤ (z + 2) ^ 36 := by positivity
    linarith
  have h18 : (z + 2) ^ 18 ≤ (z + 2) ^ 36 :=
    pow_le_pow_right₀ (by linarith) (by decide)
  have hwA : (z + 2) ^ 3 + (z + 2) ^ 18 + z ≤ A := by linarith
  have hsum : Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z) ≤
      2 * Real.exp A := by
    linarith [Real.exp_le_exp.mpr hzA, Real.exp_le_exp.mpr hwA]
  have hpoly : (A + 2) ^ 4 + (A + 2) ^ 3 + A + 4 ≤ (A + 2) ^ 5 := by
    have hh : 0 ≤ A ^ 5 + 9 * A ^ 4 + 31 * A ^ 3 + 50 * A ^ 2 + 35 * A + 4 := by positivity
    nlinarith
  have hnum : 2 * (l : ℝ) * (Real.exp ((A + 2) ^ 3) *
      (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z))) ≤
        Real.exp ((A + 2) ^ 5) := by
    calc
      _ ≤ 2 * Real.exp ((A + 2) ^ 4) * (Real.exp ((A + 2) ^ 3) * (2 * Real.exp A)) := by
        gcongr
      _ = 4 * Real.exp ((A + 2) ^ 4 + (A + 2) ^ 3 + A) := by
        simp only [Real.exp_add]
        ring
      _ ≤ Real.exp 4 * Real.exp ((A + 2) ^ 4 + (A + 2) ^ 3 + A) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp (4 : ℝ)]
      _ = Real.exp ((A + 2) ^ 4 + (A + 2) ^ 3 + A + 4) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hpoly
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hpower : (N : ℝ) ≤ (N : ℝ) ^ d := by
    simpa only [pow_one] using pow_le_pow_right₀ hN1 hd
  have hdenpos : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  have hquot := (div_le_one hdenpos).mpr (hnum.trans (hN.trans hpower))
  simpa only [mul_div_assoc] using hquot

noncomputable def sharedFreeRecoveryThreshold (s : ℕ) (q p : ℝ) : ℝ :=
  max (separationBudget (8 * sharedRefinementInputBudget s p + 1))
    ((sharedFreeEquationInputBudget s q p + 2) ^ 5)

theorem sharedFreeRecoveryThreshold_spec (s : ℕ) {q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p)
    (N : ℕ) [NeZero N] (hN : Real.exp (sharedFreeRecoveryThreshold s q p) ≤ (N : ℝ)) :
    let z := 8 * sharedRefinementInputBudget s p + 1
    let A := sharedFreeEquationInputBudget s q p
    Real.exp (separationBudget z) ≤ (N : ℝ) ∧
      ∀ (l d : ℕ), 1 ≤ d → (l : ℝ) ≤ Real.exp ((A + 2) ^ 4) →
        2 * (l : ℝ) * (Real.exp ((A + 2) ^ 3) *
          ((Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) / (N : ℝ) ^ d)) ≤ 1 := by
  intro z A
  constructor
  · exact (Real.exp_le_exp.mpr (le_max_left _ _)).trans hN
  · intro l d hd hl
    have hb := sharedFreeEquationInputBudget_bounds s hq hp
    have hz : 0 ≤ z := by
      have h := (sharedRefinementInputBudget_bounds s hp).2.2.1
      dsimp only [z]
      linarith
    exact sharedFree_rounding_small hb.1 hz hb.2.2.2 N l d hd hl
      ((Real.exp_le_exp.mpr (le_max_right _ _)).trans hN)

end Erdos3

end

end OAI
