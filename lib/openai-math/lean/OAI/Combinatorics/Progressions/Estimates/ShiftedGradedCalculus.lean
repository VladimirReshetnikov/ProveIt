/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Linear.DualLogarithmicDifferential
import OAI.Combinatorics.Progressions.Nilpotent.RealizedDualBCH
import OAI.Combinatorics.Progressions.Polynomial.ShiftedGradedPolynomial

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

abbrev FilteredFirstJet := F.adaptedLieSubalgebra w ⧸ F.shiftedPolynomialIdeal w 2

noncomputable def filteredFirstJetMap : F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.FilteredFirstJet w :=
  lieQuotientMap (F.shiftedPolynomialIdeal w 2)

theorem filteredFirstJetMap_surjective : Function.Surjective (F.filteredFirstJetMap w) :=
  lieQuotientMap_surjective _

theorem filteredFirstJetMap_eq_zero_iff (p : F.adaptedLieSubalgebra w) :
    F.filteredFirstJetMap w p = 0 ↔ ∀ α, coefficients p.val α ∈ F.layer (Finsupp.weight w α + 2) :=
  lieQuotientMap_eq_zero _ p

theorem filteredFirstJetMap_eq_iff (p q : F.adaptedLieSubalgebra w) :
    F.filteredFirstJetMap w p = F.filteredFirstJetMap w q ↔
      ∀ α, coefficients (p.val - q.val) α ∈ F.layer (Finsupp.weight w α + 2) := by
  rw [← sub_eq_zero, ← map_sub, F.filteredFirstJetMap_eq_zero_iff]
  rfl

noncomputable def filteredFirstJetSymbol : F.FilteredFirstJet w →ₗ⁅ℚ⁆ F.PolynomialSymbol w :=
  { toLinearMap := (F.shiftedPolynomialIdeal w 2).toSubmodule.liftQ
      (F.polynomialSymbolMap w).toLinearMap (by
        intro p hp
        apply (F.polynomialSymbolMap_eq_zero_iff w p).mpr
        exact F.shiftedAdaptedSubmodule_antitone w (by decide : 1 ≤ 2) hp)
    map_lie' {x y} := by
      obtain ⟨p, rfl⟩ := F.filteredFirstJetMap_surjective w x
      obtain ⟨q, rfl⟩ := F.filteredFirstJetMap_surjective w y
      change F.polynomialSymbolMap w ⁅p, q⁆ = ⁅F.polynomialSymbolMap w p, F.polynomialSymbolMap w q⁆
      exact (F.polynomialSymbolMap w).map_lie p q }

@[simp] theorem filteredFirstJetSymbol_map (p : F.adaptedLieSubalgebra w) :
    F.filteredFirstJetSymbol w (F.filteredFirstJetMap w p) = F.polynomialSymbolMap w p := rfl

theorem filteredFirstJetSymbol_surjective : Function.Surjective (F.filteredFirstJetSymbol w) := by
  intro x
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  exact ⟨F.filteredFirstJetMap w p, rfl⟩

theorem filteredFirstJet_kernel_lie_eq_zero {x y : F.FilteredFirstJet w}
    (hx : F.filteredFirstJetSymbol w x = 0) (hy : F.filteredFirstJetSymbol w y = 0) : ⁅x, y⁆ = 0 := by
  obtain ⟨p, rfl⟩ := F.filteredFirstJetMap_surjective w x
  obtain ⟨q, rfl⟩ := F.filteredFirstJetMap_surjective w y
  change F.polynomialSymbolMap w p = 0 at hx
  change F.polynomialSymbolMap w q = 0 at hy
  have hp : p ∈ F.shiftedPolynomialIdeal w 1 :=
    (F.polynomialSymbolMap_eq_zero_iff w p).mp hx
  have hq : q ∈ F.shiftedPolynomialIdeal w 1 :=
    (F.polynomialSymbolMap_eq_zero_iff w q).mp hy
  have hpq : ⁅p, q⁆ ∈ F.shiftedPolynomialIdeal w 2 :=
    F.shiftedPolynomialIdeal_lie_mem w (i := 1) (j := 1) hp hq
  exact ((F.filteredFirstJetMap w).map_lie p q).symm.trans
    ((lieQuotientMap_eq_zero (F.shiftedPolynomialIdeal w 2) ⁅p, q⁆).mpr hpq)

theorem filteredFirstJet_lowerCentralSeries_eq_bot :
    LieModule.lowerCentralSeries ℚ (F.FilteredFirstJet w) (F.FilteredFirstJet w) s = ⊥ :=
  lie_quotient_lowerCentralSeries_eq_bot (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot _

abbrev FilteredFirstJetGroup :=
  NilpotentLieBCHGroup (F.FilteredFirstJet w) s (F.filteredFirstJet_lowerCentralSeries_eq_bot w)

noncomputable def filteredFirstJetHom : (F.adaptedPolynomialFiltration w).Group →* F.FilteredFirstJetGroup w :=
  NilpotentLieBCHGroup.map (F.filteredFirstJetMap w)

noncomputable def filteredFirstJetSymbolHom : F.FilteredFirstJetGroup w →* F.PolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.map (F.filteredFirstJetSymbol w)

theorem filteredFirstJet_kernel_mul (x y : F.FilteredFirstJetGroup w)
    (hx : F.filteredFirstJetSymbolHom w x = 1) (hy : F.filteredFirstJetSymbolHom w y = 1) :
    (x * y).coord = x.coord + y.coord :=
  lieBCH_eq_add_of_lie_eq_zero (F.filteredFirstJet_lowerCentralSeries_eq_bot w)
    (F.filteredFirstJet_kernel_lie_eq_zero w (congrArg NilpotentLieBCHGroup.coord hx)
      (congrArg NilpotentLieBCHGroup.coord hy))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem common_derivative_identity (A B D : NilpotentLieBCHGroup L s hnil)
    (YA YB YD YX e m u Z v : L)
    (hprod : YX = YA + dualAdjoint A YB + dualAdjoint (A * B) YD)
    (hsquare : YX - e - dualAdjoint (A * B * D) m =
      u + dualAdjoint A Z + dualAdjoint (A * B) v) :
    YB = dualAdjoint A⁻¹ (e + u - YA) +
      dualAdjoint B (v + dualAdjoint D m - YD) + Z := by
  apply dualAdjoint_injective A
  simp only [dualAdjoint_add, dualAdjoint_sub, ← dualAdjoint_mul, mul_inv_cancel,
    dualAdjoint_one, ← mul_assoc]
  calc
    dualAdjoint A YB =
        (YX - e - dualAdjoint (A * B * D) m) - YA - dualAdjoint (A * B) YD +
          e + dualAdjoint (A * B * D) m := by rw [hprod]; abel
    _ = (u + dualAdjoint A Z + dualAdjoint (A * B) v) - YA -
        dualAdjoint (A * B) YD + e + dualAdjoint (A * B * D) m := by rw [hsquare]
    _ = _ := by abel

theorem common_derivative_mod_submodule (V : Submodule ℚ L)
    (A B D : NilpotentLieBCHGroup L s hnil) (YA YB YD YX e m u Z v ZB : L)
    (hprod : YX = YA + dualAdjoint A YB + dualAdjoint (A * B) YD)
    (hsquare : YX - e - dualAdjoint (A * B * D) m =
      u + dualAdjoint A Z + dualAdjoint (A * B) v)
    (hZ : Z - ZB ∈ V) :
    YB - (dualAdjoint A⁻¹ (e + u - YA) +
      dualAdjoint B (v + dualAdjoint D m - YD) + ZB) ∈ V := by
  rw [common_derivative_identity A B D YA YB YD YX e m u Z v hprod hsquare]
  convert hZ using 1; abel

theorem common_derivative_difference (V : Submodule ℚ L)
    (B : NilpotentLieBCHGroup L s hnil) (Y Y₀ S S₀ R R₀ ZB : L)
    (hY : Y - (S + dualAdjoint B R + ZB) ∈ V)
    (hY₀ : Y₀ - (S₀ + dualAdjoint B R₀ + ZB) ∈ V) :
    (Y - Y₀) - ((S - S₀) + dualAdjoint B (R - R₀)) ∈ V := by
  have hd := V.sub_mem hY hY₀
  rw [dualAdjoint_sub]
  convert hd using 1; abel

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem coefficients_pderiv (i : σ) (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor L p) α =
      (α i + 1 : ℚ) • coefficients p (α + Finsupp.single i 1) := by
  induction p using TensorProduct.inductionOn with
  | tmul q x =>
    rw [LinearMap.rTensor_tmul]
    rw [coefficients_tmul, coefficients_tmul]
    change (MvPolynomial.pderiv i q).coeff α • x =
      (α i + 1 : ℚ) • (q.coeff (α + Finsupp.single i 1) • x)
    rw [MvPolynomial.coeff_pderiv, smul_smul]
    congr 1
    ring
  | add p q hp hq => simp only [map_add, Finsupp.add_apply, hp, hq, smul_add]

theorem coefficients_directionalDerivative [Fintype σ]
    (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    coefficients (directionalDerivative h p) α =
      ∑ i, h i • ((α i + 1 : ℚ) • coefficients p (α + Finsupp.single i 1)) := by
  simp only [directionalDerivative, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, coefficients_pderiv]

end VectorPolynomial

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem directionalDerivative_mem_shifted [Fintype σ] (h : σ → ℚ) (k : ℕ)
    {p : VectorPolynomial σ ℚ L} (hp : p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) k) :
    directionalDerivative h p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) (k + 1) := by
  intro α
  rw [coefficients_directionalDerivative]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  have hi := hp (α + Finsupp.single i 1)
  simpa only [map_add, Finsupp.weight_single, one_smul, Nat.add_right_comm, Nat.add_assoc] using hi

theorem directionalDerivative_mem_next [Fintype σ] (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    directionalDerivative h p.val ∈ F.shiftedAdaptedSubmodule (fun _ => 1) 1 := by
  apply F.directionalDerivative_mem_shifted h 0
  intro α
  simpa only [Nat.add_zero] using p.property α

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem common_derivative_defect (A B D : NilpotentLieBCHGroup L s hnil)
    (YA YB YD YX e m u Z v : L)
    (hprod : YX = YA + dualAdjoint A YB + dualAdjoint (A * B) YD) :
    YB - (dualAdjoint A⁻¹ (e + u - YA) +
      dualAdjoint B (v + dualAdjoint D m - YD) + Z) =
    dualAdjoint A⁻¹ (YX - e - dualAdjoint (A * B * D) m -
      (u + dualAdjoint A Z + dualAdjoint (A * B) v)) := by
  apply dualAdjoint_injective A
  simp only [dualAdjoint_add, dualAdjoint_sub, ← dualAdjoint_mul, mul_inv_cancel,
    dualAdjoint_one, ← mul_assoc, one_mul, hprod]
  abel

theorem common_derivative_mod_of_defect (V W : Submodule ℚ L)
    (A B D : NilpotentLieBCHGroup L s hnil) (YA YB YD YX e m u Z v ZB : L)
    (hprod : YX = YA + dualAdjoint A YB + dualAdjoint (A * B) YD)
    (hdefect : YX - e - dualAdjoint (A * B * D) m -
      (u + dualAdjoint A Z + dualAdjoint (A * B) v) ∈ W)
    (htransport : ∀ x ∈ W, dualAdjoint A⁻¹ x ∈ V) (hZ : Z - ZB ∈ V) :
    YB - (dualAdjoint A⁻¹ (e + u - YA) +
      dualAdjoint B (v + dualAdjoint D m - YD) + ZB) ∈ V := by
  have hd := htransport _ hdefect
  rw [← common_derivative_defect A B D YA YB YD YX e m u Z v hprod] at hd
  convert V.add_mem hd hZ using 1; abel

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def taylorRemainder (h : σ → ℚ) :
    VectorPolynomial σ ℚ L →ₗ[ℚ] VectorPolynomial σ ℚ L :=
  (scalarTaylorRemainder h).rTensor L

theorem taylorRemainder_apply (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    taylorRemainder h p = translate h p - p - directionalDerivative h p := by
  induction p using TensorProduct.inductionOn with
  | tmul q x =>
    change scalarTaylorRemainder h q ⊗ₜ[ℚ] x = _
    rw [scalarTaylorRemainder_apply, TensorProduct.sub_tmul, TensorProduct.sub_tmul,
      translate_tmul, directionalDerivative_tmul, scalarDirectionalDerivative_apply, TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    abel

theorem coefficients_taylorRemainder_monomial (h : σ → ℚ) (α β : σ →₀ ℕ) (x : L) :
    coefficients (taylorRemainder h (monomial α x)) β =
      (scalarTaylorRemainder h (MvPolynomial.monomial α 1)).coeff β • x := by
  change coefficients (scalarTaylorRemainder h (MvPolynomial.monomial α 1) ⊗ₜ[ℚ] x) β = _
  exact coefficients_tmul _ _ _

theorem coefficients_taylorRemainder (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    coefficients (taylorRemainder h p) α = ∑ β ∈ (coefficients p).support,
      (scalarTaylorRemainder h (MvPolynomial.monomial β 1)).coeff α • coefficients p β := by
  conv_lhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, Finsupp.finsetSum_apply, coefficients_taylorRemainder_monomial]

end VectorPolynomial

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem taylorRemainder_mem_shifted (h : σ → ℚ) (k : ℕ) {p : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) k) :
    translate h p - p - directionalDerivative h p ∈ F.shiftedAdaptedSubmodule (fun _ => 1) (k + 2) := by
  rw [← taylorRemainder_apply]
  intro α
  rw [coefficients_taylorRemainder]
  apply Submodule.sum_mem
  intro β _
  by_cases hc : (scalarTaylorRemainder h (MvPolynomial.monomial β 1)).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply F.antitone _ (hp β)
    have hd := scalarTaylorRemainder_monomial h β (MvPolynomial.mem_support_iff.mpr hc)
    change Finsupp.weight (fun _ : σ => 1) α + 2 ≤ Finsupp.weight (fun _ : σ => 1) β at hd
    omega

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

noncomputable def adaptedDirectionalDerivative :
    F.adaptedLieSubalgebra (fun _ : σ => 1) →ₗ[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1) :=
  ((directionalDerivative h).comp (F.adaptedLieSubalgebra (fun _ => 1)).incl.toLinearMap).codRestrict
    (F.adaptedLieSubalgebra (fun _ => 1)).toSubmodule (by
      intro p α
      exact F.antitone (Nat.le_succ _) (F.directionalDerivative_mem_next h p α))

@[simp] theorem adaptedDirectionalDerivative_coe (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (F.adaptedDirectionalDerivative h p : VectorPolynomial σ ℚ L) = directionalDerivative h p.val := rfl

theorem adaptedDirectionalDerivative_mem_shifted (k : ℕ)
    {p : F.adaptedLieSubalgebra (fun _ : σ => 1)}
    (hp : p ∈ F.shiftedPolynomialIdeal (fun _ => 1) k) :
    F.adaptedDirectionalDerivative h p ∈ F.shiftedPolynomialIdeal (fun _ => 1) (k + 1) :=
  F.directionalDerivative_mem_shifted h k hp

noncomputable def symbolFirstDerivative :
    F.PolynomialSymbol (fun _ : σ => 1) →ₗ[ℚ] F.FilteredFirstJet (fun _ : σ => 1) :=
  (F.shiftedAdaptedIdeal (fun _ => 1)).toSubmodule.liftQ
    ((F.filteredFirstJetMap (fun _ => 1)).toLinearMap.comp (F.adaptedDirectionalDerivative h)) (by
      intro p hp
      exact (F.filteredFirstJetMap_eq_zero_iff (fun _ => 1) _).mpr
        (F.adaptedDirectionalDerivative_mem_shifted h 1 hp))

@[simp] theorem symbolFirstDerivative_map (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.symbolFirstDerivative h (F.polynomialSymbolMap (fun _ => 1) p) =
      F.filteredFirstJetMap (fun _ => 1) (F.adaptedDirectionalDerivative h p) := rfl

theorem symbolFirstDerivative_in_kernel (x : F.PolynomialSymbol (fun _ : σ => 1)) :
    F.filteredFirstJetSymbol (fun _ => 1) (F.symbolFirstDerivative h x) = 0 := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective (fun _ => 1) x
  rw [F.symbolFirstDerivative_map, F.filteredFirstJetSymbol_map]
  exact (F.polynomialSymbolMap_eq_zero_iff (fun _ => 1) _).mpr
    (F.directionalDerivative_mem_next h p)

theorem filteredFirstJet_translate (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.filteredFirstJetMap (fun _ => 1)
      ⟨translate h p.val, (F.mem_adaptedSubmodule (fun _ => 1) _).mpr
        (F.adapted_translate (fun _ => 1) (by simp) h
          ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property))⟩ =
      F.filteredFirstJetMap (fun _ => 1) p +
        F.symbolFirstDerivative h (F.polynomialSymbolMap (fun _ => 1) p) := by
  rw [F.symbolFirstDerivative_map, ← map_add]
  apply (F.filteredFirstJetMap_eq_iff (fun _ => 1) _ _).mpr
  have hp : p.val ∈ F.shiftedAdaptedSubmodule (fun _ => 1) 0 := by
    intro α
    simpa only [Nat.add_zero] using p.property α
  have hr := F.taylorRemainder_mem_shifted h 0 hp
  change ∀ α, coefficients (translate h p.val - (p.val + directionalDerivative h p.val)) α ∈ _
  rw [show translate h p.val - (p.val + directionalDerivative h p.val) =
      translate h p.val - p.val - directionalDerivative h p.val by abel]
  exact hr

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem filteredFirstJet_constant_eq (w : σ → ℕ) {a b : L} (hab : a - b ∈ F.layer 2) :
    F.filteredFirstJetMap w (F.adaptedConstant w a) = F.filteredFirstJetMap w (F.adaptedConstant w b) := by
  change F.filteredFirstJetMap w (F.adaptedConstantLieHom w a) =
    F.filteredFirstJetMap w (F.adaptedConstantLieHom w b)
  rw [← sub_eq_zero, ← map_sub, ← map_sub]
  apply (F.filteredFirstJetMap_eq_zero_iff w _).mpr
  exact F.adaptedConstant_mem_shiftedPolynomialIdeal w 2 hab

theorem filteredFirstJet_normalizedShift [Fintype σ] (h : σ → ℚ) (a b : L)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.filteredFirstJetMap (fun _ => 1)
      ⟨normalizedShiftLog s h a b p.val,
        (F.mem_adaptedSubmodule (fun _ => 1) _).mpr
          (F.normalizedShiftLog_adapted (fun _ => 1) (by simp) h a b
            ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property))⟩ =
      lieBCH s (F.filteredFirstJetMap (fun _ => 1) (F.adaptedConstant (fun _ => 1) a))
        (lieBCH s (F.filteredFirstJetMap (fun _ => 1) p +
          F.symbolFirstDerivative h (F.polynomialSymbolMap (fun _ => 1) p))
            (F.filteredFirstJetMap (fun _ => 1) (F.adaptedConstant (fun _ => 1) b))) := by
  let q : F.adaptedLieSubalgebra (fun _ : σ => 1) :=
    ⟨translate h p.val, (F.mem_adaptedSubmodule (fun _ => 1) _).mpr
      (F.adapted_translate (fun _ => 1) (by simp) h
        ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property))⟩
  have he : (⟨normalizedShiftLog s h a b p.val,
        (F.mem_adaptedSubmodule (fun _ => 1) _).mpr
          (F.normalizedShiftLog_adapted (fun _ => 1) (by simp) h a b
            ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property))⟩ :
      F.adaptedLieSubalgebra (fun _ : σ => 1)) =
      lieBCH s (F.adaptedConstant (fun _ => 1) a)
        (lieBCH s q (F.adaptedConstant (fun _ => 1) b)) := by
    apply Subtype.ext
    change normalizedShiftLog s h a b p.val =
      (F.adaptedLieSubalgebra (fun _ : σ => 1)).incl
        (lieBCH s (F.adaptedConstant (fun _ => 1) a) (lieBCH s q (F.adaptedConstant (fun _ => 1) b)))
    rw [map_lieBCH, map_lieBCH]
    rfl
  rw [he, map_lieBCH, map_lieBCH]
  have ht : F.filteredFirstJetMap (fun _ => 1) q = F.filteredFirstJetMap (fun _ => 1) p +
      F.symbolFirstDerivative h (F.polynomialSymbolMap (fun _ => 1) p) := F.filteredFirstJet_translate h p
  rw [ht]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

noncomputable def adaptedPolynomialJet (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    DualGroup (F.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot :=
  ⟨dualConstantLie p + dualInfinitesimal (F.adaptedDirectionalDerivative h p)⟩

@[simp] theorem adaptedPolynomialJet_base (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    dualBaseLinear (F.adaptedPolynomialJet h p).coord = p := by
  change dualBaseLinear (dualConstantLie p + dualInfinitesimal (F.adaptedDirectionalDerivative h p)) = p
  rw [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

@[simp] theorem adaptedPolynomialJet_tangent (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    dualTangentLinear (F.adaptedPolynomialJet h p).coord = F.adaptedDirectionalDerivative h p := by
  change dualTangentLinear (dualConstantLie p + dualInfinitesimal (F.adaptedDirectionalDerivative h p)) = _
  rw [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]

@[simp] theorem adaptedPolynomialJet_baseHom (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    dualBaseHom (F.adaptedPolynomialJet h p) =
      (⟨p⟩ : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) := by
  apply NilpotentLieBCHGroup.ext
  exact F.adaptedPolynomialJet_base h p

noncomputable def normalizedShiftAdapted (a b : L)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) : F.adaptedLieSubalgebra (fun _ : σ => 1) :=
  ⟨normalizedShiftLog s h a b p.val, (F.mem_adaptedSubmodule (fun _ => 1) _).mpr
    (F.normalizedShiftLog_adapted (fun _ => 1) (by simp) h a b
      ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property))⟩

noncomputable def normalizedRelativeLog (e m : L)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) : F.adaptedLieSubalgebra (fun _ : σ => 1) :=
  lieBCH s (F.normalizedShiftAdapted h (-e) (-m) p) (-p)

noncomputable def adaptedLogDerivative (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.adaptedLieSubalgebra (fun _ : σ => 1) := dualLogDerivative (F.adaptedPolynomialJet h p)

theorem filteredFirstJet_normalizedRelativeLog (e m : L)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.filteredFirstJetMap (fun _ => 1) (F.normalizedRelativeLog h e m p) =
      F.filteredFirstJetMap (fun _ => 1)
        (F.adaptedLogDerivative h p - F.adaptedConstant (fun _ => 1) e -
          dualAdjoint (⟨p⟩ : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
            (F.adaptedConstant (fun _ => 1) m)) := by
  have hbracket : ∀ x ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1,
      ∀ y ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1,
        ⁅x, y⁆ ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 2 := by
    intro x hx y hy
    exact F.shiftedPolynomialIdeal_lie_mem (fun _ => 1) (i := 1) (j := 1) hx hy
  have hz : dualTangentLinear (F.adaptedPolynomialJet h p).coord ∈
      F.shiftedPolynomialIdeal (fun _ : σ => 1) 1 := by
    rw [F.adaptedPolynomialJet_tangent]
    exact F.directionalDerivative_mem_next h p
  have hid := dualBCH_insertion_quotient
    (F.shiftedPolynomialIdeal (fun _ : σ => 1) 1) (F.shiftedPolynomialIdeal (fun _ : σ => 1) 2)
    hbracket (F.adaptedPolynomialJet h p)
    (F.adaptedConstant (fun _ => 1) e) (F.adaptedConstant (fun _ => 1) m) hz
    (F.adaptedConstant_mem_shiftedIdeal (fun _ => 1) e)
    (F.adaptedConstant_mem_shiftedIdeal (fun _ => 1) m)
  rw [F.adaptedPolynomialJet_base, F.adaptedPolynomialJet_tangent,
    F.adaptedPolynomialJet_baseHom] at hid
  change F.filteredFirstJetMap (fun _ => 1)
    (lieBCH s (F.normalizedShiftAdapted h (-e) (-m) p) (-p)) = _
  rw [map_lieBCH, map_neg]
  have hn := F.filteredFirstJet_normalizedShift h (-e) (-m) p
  change F.filteredFirstJetMap (fun _ => 1) (F.normalizedShiftAdapted h (-e) (-m) p) = _ at hn
  rw [hn, F.symbolFirstDerivative_map]
  have hc (a : L) : F.adaptedConstant (fun _ : σ => 1) (-a) =
      -F.adaptedConstant (fun _ : σ => 1) a := (F.adaptedConstantLieHom (fun _ => 1)).map_neg a
  rw [hc e, hc m, map_neg, map_neg,
    ← lieBCH_assoc (F.filteredFirstJet_lowerCentralSeries_eq_bot (fun _ : σ => 1))]
  rw [map_add] at hid
  exact hid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

theorem adaptedDirectionalDerivative_lie (p q : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.adaptedDirectionalDerivative h ⁅p, q⁆ =
      ⁅F.adaptedDirectionalDerivative h p, q⁆ + ⁅p, F.adaptedDirectionalDerivative h q⁆ := by
  apply Subtype.ext
  exact directionalDerivative_lie h p.val q.val

noncomputable def adaptedPolynomialJetLie :
    F.adaptedLieSubalgebra (fun _ : σ => 1) →ₗ⁅ℚ⁆
      DualLieAlgebra (F.adaptedLieSubalgebra (fun _ : σ => 1)) where
  toLinearMap := dualConstantLie.toLinearMap +
    dualInfinitesimal.comp (F.adaptedDirectionalDerivative h)
  map_lie' {p q} := by
    change dualConstantLie ⁅p, q⁆ + dualInfinitesimal (F.adaptedDirectionalDerivative h ⁅p, q⁆) =
      ⁅dualConstantLie p + dualInfinitesimal (F.adaptedDirectionalDerivative h p),
        dualConstantLie q + dualInfinitesimal (F.adaptedDirectionalDerivative h q)⁆
    apply dual_ext
    · simp only [map_add, dualBaseLinear_constant,
        dualBaseLinear_infinitesimal, add_zero, dualBaseLinear_lie]
    · simp only [map_add, dualTangentLinear_constant,
        dualTangentLinear_infinitesimal, zero_add, dualTangentLinear_lie,
        dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]
      rw [F.adaptedDirectionalDerivative_lie]
      exact add_comm _ _

noncomputable def adaptedPolynomialJetHom :
    (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group →*
      DualGroup (F.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot :=
  NilpotentLieBCHGroup.map (F.adaptedPolynomialJetLie h)

@[simp] theorem adaptedPolynomialJetHom_apply
    (P : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    F.adaptedPolynomialJetHom h P = F.adaptedPolynomialJet h P.coord := rfl

theorem adaptedLogDerivative_mul
    (P Q : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    F.adaptedLogDerivative h (P * Q).coord =
      F.adaptedLogDerivative h P.coord + dualAdjoint P (F.adaptedLogDerivative h Q.coord) := by
  change dualLogDerivative (F.adaptedPolynomialJetHom h (P * Q)) = _
  rw [map_mul, dualLogDerivative_mul, F.adaptedPolynomialJetHom_apply,
    F.adaptedPolynomialJet_baseHom]
  rfl

theorem adaptedLogDerivative_triple
    (A B D : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    F.adaptedLogDerivative h (A * B * D).coord =
      F.adaptedLogDerivative h A.coord + dualAdjoint A (F.adaptedLogDerivative h B.coord) +
        dualAdjoint (A * B) (F.adaptedLogDerivative h D.coord) := by
  rw [F.adaptedLogDerivative_mul, F.adaptedLogDerivative_mul]

theorem adapted_common_derivative_identity
    (A B D : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (e m u Z v : F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hsquare : F.adaptedLogDerivative h (A * B * D).coord - e - dualAdjoint (A * B * D) m =
      u + dualAdjoint A Z + dualAdjoint (A * B) v) :
    F.adaptedLogDerivative h B.coord =
      dualAdjoint A⁻¹ (e + u - F.adaptedLogDerivative h A.coord) +
        dualAdjoint B (v + dualAdjoint D m - F.adaptedLogDerivative h D.coord) + Z :=
  common_derivative_identity A B D _ _ _ _ e m u Z v
    (F.adaptedLogDerivative_triple h A B D) hsquare

theorem adapted_common_derivative_mod_submodule
    (V : Submodule ℚ (F.adaptedLieSubalgebra (fun _ : σ => 1)))
    (A B D : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (e m u Z v ZB : F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hsquare : F.adaptedLogDerivative h (A * B * D).coord - e - dualAdjoint (A * B * D) m =
      u + dualAdjoint A Z + dualAdjoint (A * B) v) (hZ : Z - ZB ∈ V) :
    F.adaptedLogDerivative h B.coord -
      (dualAdjoint A⁻¹ (e + u - F.adaptedLogDerivative h A.coord) +
        dualAdjoint B (v + dualAdjoint D m - F.adaptedLogDerivative h D.coord) + ZB) ∈ V :=
  common_derivative_mod_submodule V A B D _ _ _ _ e m u Z v ZB
    (F.adaptedLogDerivative_triple h A B D) hsquare hZ

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualLogDerivative_tangent (x : L) :
    dualLogDerivative (hnil := hnil) (dualTangentElement x) = x := by
  simpa only [map_one, mul_one] using
    dualLogDerivative_tangent_mul_constant x (1 : NilpotentLieBCHGroup L s hnil)

end Erdos3.NilpotentLieBCHGroup

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adaptedLogDerivative_constant (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hp : coefficients p.val 0 = 0) :
    coefficients (F.adaptedLogDerivative h p).val 0 =
      coefficients (directionalDerivative h p.val) 0 := by
  let φ : F.adaptedLieSubalgebra (fun _ : σ => 1) →ₗ⁅ℚ⁆ L :=
    (evalLie (0 : σ → ℚ)).comp (F.adaptedLieSubalgebra (fun _ => 1)).incl
  have hφ (q : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
      φ q = coefficients q.val 0 := eval_zero_eq_coefficient q.val
  have hjet : dualLinearLift φ φ.toLinearMap (F.adaptedPolynomialJet h p).coord =
      (dualTangentElement (hnil := F.lowerCentralSeries_eq_bot)
        (φ (F.adaptedDirectionalDerivative h p))).coord := by
    rw [dualLinearLift_apply, F.adaptedPolynomialJet_base, F.adaptedPolynomialJet_tangent]
    change dualConstantLie (φ p) + dualInfinitesimal (φ (F.adaptedDirectionalDerivative h p)) = _
    rw [hφ p, hp, map_zero, zero_add]
    rfl
  have he := dualLinearLift_logDerivative_eq F.lowerCentralSeries_eq_bot
    (⊤ : LieIdeal ℚ (F.adaptedLieSubalgebra (fun _ : σ => 1))) φ φ.toLinearMap
    (fun x y _ => φ.map_lie x y) (F.adaptedPolynomialJet h p) (by trivial)
    (dualTangentElement (φ (F.adaptedDirectionalDerivative h p))) hjet
  rw [dualLogDerivative_tangent] at he
  change φ (F.adaptedLogDerivative h p) = φ (F.adaptedDirectionalDerivative h p) at he
  simpa only [hφ, F.adaptedDirectionalDerivative_coe] using he

theorem adaptedLogDerivative_constant_unit [DecidableEq σ] (i : σ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hp : coefficients p.val 0 = 0) :
    coefficients (F.adaptedLogDerivative (Pi.single i 1) p).val 0 =
      coefficients p.val (Finsupp.single i 1) := by
  classical
  rw [F.adaptedLogDerivative_constant _ p hp, coefficients_directionalDerivative]
  simp [Pi.single_apply]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedDirectionalTangent
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (σ → ℚ) →ₗ[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1) where
  toFun h := F.adaptedDirectionalDerivative h p
  map_add' h k := Subtype.ext (directionalDerivative_direction_add h k p.val)
  map_smul' r h := Subtype.ext (directionalDerivative_direction_smul r h p.val)

noncomputable def adaptedLogDerivativeLinear
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (σ → ℚ) →ₗ[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1) :=
  (dualLogarithmicDifferential
    (hnil := (F.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot) p).comp
      (F.adaptedDirectionalTangent p)

@[simp] theorem adaptedLogDerivativeLinear_apply
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) (h : σ → ℚ) :
    F.adaptedLogDerivativeLinear p h = F.adaptedLogDerivative h p := rfl

theorem adaptedLogDerivative_direction_sub
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) (h k : σ → ℚ) :
    F.adaptedLogDerivative (h - k) p = F.adaptedLogDerivative h p - F.adaptedLogDerivative k p :=
  (F.adaptedLogDerivativeLinear p).map_sub h k

theorem adapted_common_derivative_difference
    (V : Submodule ℚ (F.adaptedLieSubalgebra (fun _ : σ => 1)))
    (B : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (h h₀ : σ → ℚ) (S S₀ R R₀ ZB : F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hh : F.adaptedLogDerivative h B.coord - (S + dualAdjoint B R + ZB) ∈ V)
    (hh₀ : F.adaptedLogDerivative h₀ B.coord - (S₀ + dualAdjoint B R₀ + ZB) ∈ V) :
    F.adaptedLogDerivative (h - h₀) B.coord -
      ((S - S₀) + dualAdjoint B (R - R₀)) ∈ V := by
  rw [F.adaptedLogDerivative_direction_sub]
  exact common_derivative_difference V B _ _ S S₀ R R₀ ZB hh hh₀

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem gradedPieceProjection_lie {i j : ℕ} {u v : L}
    (hu : u ∈ F.layer i) (hv : v ∈ F.layer j) :
    F.gradedPieceProjection b ω hlayers (i + j) ⁅u, v⁆ =
      ⁅F.gradedPieceProjection b ω hlayers i u, F.gradedPieceProjection b ω hlayers j v⁆ := by
  have hi := F.gradedPieceProjection_eq_pieceMap b ω hlayers i ⟨u, hu⟩
  have hj := F.gradedPieceProjection_eq_pieceMap b ω hlayers j ⟨v, hv⟩
  have hij := F.gradedPieceProjection_eq_pieceMap b ω hlayers (i + j) ⟨⁅u, v⁆, F.lie_mem hu hv⟩
  change F.gradedPieceProjection b ω hlayers i u = _ at hi
  change F.gradedPieceProjection b ω hlayers j v = _ at hj
  change F.gradedPieceProjection b ω hlayers (i + j) ⁅u, v⁆ = _ at hij
  rw [hi, hj, hij, F.associatedGradedPieceMap_lie]

theorem shiftedGradedPolynomial_lie (w : σ → ℕ) {i j : ℕ} {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftedAdaptedSubmodule w i) (hq : q ∈ F.shiftedAdaptedSubmodule w j) :
    F.shiftedGradedPolynomial b ω hlayers w (i + j) ⁅p, q⁆ =
      ⁅F.shiftedGradedPolynomial b ω hlayers w i p, F.shiftedGradedPolynomial b ω hlayers w j q⁆ := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum, sum_lie_sum, map_sum, lie_monomial, F.shiftedGradedPolynomial_monomial]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  have hdeg : Finsupp.weight w (α + β) + (i + j) =
      (Finsupp.weight w α + i) + (Finsupp.weight w β + j) := by
    rw [map_add]
    omega
  rw [hdeg, F.gradedPieceProjection_lie b ω hlayers (hp α) (hq β)]

theorem shiftedGradedPolynomial_directionalDerivative [Fintype σ] (h : σ → ℚ)
    (k : ℕ) (p : VectorPolynomial σ ℚ L) :
    F.shiftedGradedPolynomial b ω hlayers (fun _ : σ => 1) (k + 1) (directionalDerivative h p) =
      directionalDerivative h (F.shiftedGradedPolynomial b ω hlayers (fun _ : σ => 1) k p) := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.shiftedGradedPolynomial_coefficient, coefficients_directionalDerivative,
    coefficients_directionalDerivative, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul, F.shiftedGradedPolynomial_coefficient]
  simp only [map_add, Finsupp.weight_single, one_smul, Nat.add_right_comm, Nat.add_assoc]

end Erdos3.NilpotentLieFiltration

end

end OAI
