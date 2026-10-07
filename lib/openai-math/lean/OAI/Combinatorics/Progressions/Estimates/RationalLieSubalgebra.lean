import Mathlib.LinearAlgebra.Quotient.Basic
import OAI.Combinatorics.Progressions.Geometry.LieStructureTransport
import OAI.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder

namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

def rationalLieStructureHeight (d H : ℕ) : ℕ :=
  (d ^ 3 + 1) * (H ^ 4) ^ (d ^ 3)

theorem rationalLieStructureHeight_le_exp (d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (a : ℕ) (hH : (H : ℝ) ≤ Real.exp ((p + 2) ^ a)) :
    (rationalLieStructureHeight d H : ℝ) ≤ Real.exp ((p + 2) ^ (a + 6)) := by
  have hterm : ((H ^ 4 : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (a + 2)) := by
    rw [Nat.cast_pow]
    calc
      _ ≤ (Real.exp ((p + 2) ^ a)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg H) hH 4
      _ = Real.exp (4 * (p + 2) ^ a) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [pow_add]
        have hsq : (4 : ℝ) ≤ (p + 2) ^ 2 := by nlinarith
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ (p + 2) ^ a)
  have hcard : ((d ^ 3 : ℕ) : ℝ) ≤ (p + 2) ^ 3 := by
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg d) (hd.trans (by linarith)) _
  exact rational_sum_cost_le_exp (d ^ 3) (H ^ 4) hp (a + 2) 3 hterm hcard

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
theorem transportedLieConstants_height_uniform (c : ι → ι → ι → ℚ)
    (P : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (hP : ∀ i j, RationalHeightLE (P i j) H)
    (hS : ∀ i j, RationalHeightLE (S i j) H) (i j k : κ) :
    RationalHeightLE (transportedLieConstants c P S i j k) (rationalLieStructureHeight (Fintype.card ι) H) := by
  have h := transportedLieConstants_height c P S hc hP hS i j k
  simpa only [rationalLieStructureHeight, pow_succ, pow_zero, one_mul] using h

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [DecidableEq ι] [DecidableEq κ]

theorem exists_bounded_lie_embedding_retraction (b : Basis κ ℚ M) (e : Basis ι ℚ L)
    (φ : M →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hB : ∀ i j, RationalHeightLE (LinearMap.toMatrix b e φ.toLinearMap i j) H) :
    ∃ P : Matrix κ ι ℚ, P * LinearMap.toMatrix b e φ.toLinearMap = 1 ∧
      (∀ i j, RationalHeightLE (P i j) (rationalSolveHeight (Fintype.card κ) H)) ∧
      ∀ i j k, RationalHeightLE (lieStructureConstants b i j k)
        (rationalLieStructureHeight (Fintype.card ι) (max H (rationalSolveHeight (Fintype.card κ) H))) := by
  have hli := Matrix.mulVec_injective_iff.mp (basisMatrix_injective b e φ.toLinearMap hφ)
  obtain ⟨P, hP, hPH⟩ := exists_bounded_rational_left_inverse (LinearMap.toMatrix b e φ.toLinearMap) hli hH hB
  refine ⟨P, hP, hPH, ?_⟩
  intro i j k
  rw [lieStructureConstants_embedding b e φ P hP]
  exact transportedLieConstants_height_uniform _ _ _
    (fun u v w => (hc u v w).mono (le_max_left _ _))
    (fun u v => (hPH u v).mono (le_max_right _ _))
    (fun u v => (hB u v).mono (le_max_left _ _)) i j k

theorem exists_bounded_lie_quotient_section (e : Basis ι ℚ L) (b : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : Function.Surjective φ) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hD : ∀ i j, RationalHeightLE (LinearMap.toMatrix e b φ.toLinearMap i j) H) :
    ∃ S : Matrix ι κ ℚ, LinearMap.toMatrix e b φ.toLinearMap * S = 1 ∧
      (∀ i j, RationalHeightLE (S i j) (rationalSolveHeight (Fintype.card κ) H)) ∧
      ∀ i j k, RationalHeightLE (lieStructureConstants b i j k)
        (rationalLieStructureHeight (Fintype.card ι) (max H (rationalSolveHeight (Fintype.card κ) H))) := by
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section (LinearMap.toMatrix e b φ.toLinearMap)
    (basisMatrix_surjective e b φ.toLinearMap hφ) hH hD
  refine ⟨S, hS, hSH, ?_⟩
  intro i j k
  rw [lieStructureConstants_quotient_matrix e b φ S hS]
  exact transportedLieConstants_height_uniform _ _ _
    (fun u v w => (hc u v w).mono (le_max_left _ _))
    (fun u v => (hD u v).mono (le_max_left _ _))
    (fun u v => (hSH u v).mono (le_max_right _ _)) i j k

theorem rationalLieStructureHeight_inverse_budget (d r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hr : (r : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalLieStructureHeight d (max H (rationalSolveHeight r H)) : ℝ) ≤
      Real.exp ((p + 2) ^ 11) := by
  apply rationalLieStructureHeight_le_exp d _ hp hd 5
  rw [Nat.cast_max]
  apply max_le
  · exact hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide : 1 ≤ 5)))
  · exact rationalSolveHeight_le_budget r H hp hr hH

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [LieRing L] [LieAlgebra ℚ L]

noncomputable def lieQuotientCoordinateEquiv (e : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (D : Matrix κ ι ℚ)
    (hker : LinearMap.ker D.mulVecLin = I.toSubmodule.map e.equivFun.toLinearMap)
    (hsurj : Function.Surjective D.mulVec) : (L ⧸ I) ≃ₗ[ℚ] (κ → ℚ) :=
  (Submodule.Quotient.equiv I.toSubmodule (I.toSubmodule.map e.equivFun.toLinearMap)
    e.equivFun rfl).trans (rationalQuotientEquiv D _ hker hsurj)

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem lieQuotientCoordinateEquiv_apply_mk (e : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (D : Matrix κ ι ℚ)
    (hker : LinearMap.ker D.mulVecLin = I.toSubmodule.map e.equivFun.toLinearMap)
    (hsurj : Function.Surjective D.mulVec) (x : L) :
    lieQuotientCoordinateEquiv e I D hker hsurj (lieQuotientMap I x) = D *ᵥ e.equivFun x := by
  change rationalQuotientEquiv D _ hker hsurj (Submodule.Quotient.mk (e.equivFun x)) = _
  exact rationalQuotientEquiv_apply_mk D _ hker hsurj _

noncomputable def lieQuotientCoordinateBasis (e : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (D : Matrix κ ι ℚ)
    (hker : LinearMap.ker D.mulVecLin = I.toSubmodule.map e.equivFun.toLinearMap)
    (hsurj : Function.Surjective D.mulVec) : Basis κ ℚ (L ⧸ I) :=
  Basis.ofEquivFun (lieQuotientCoordinateEquiv e I D hker hsurj)

omit [DecidableEq κ] in
theorem lieQuotientCoordinateBasis_matrix (e : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (D : Matrix κ ι ℚ)
    (hker : LinearMap.ker D.mulVecLin = I.toSubmodule.map e.equivFun.toLinearMap)
    (hsurj : Function.Surjective D.mulVec) :
    LinearMap.toMatrix e (lieQuotientCoordinateBasis e I D hker hsurj) (lieQuotientMap I).toLinearMap = D := by
  ext i j
  rw [LinearMap.toMatrix_apply, lieQuotientCoordinateBasis, Basis.ofEquivFun_repr_apply]
  change (lieQuotientCoordinateEquiv e I D hker hsurj (lieQuotientMap I (e j))) i = _
  rw [lieQuotientCoordinateEquiv_apply_mk]
  simp [Basis.equivFun_self, Matrix.mulVec, dotProduct]

omit [DecidableEq ι] in

theorem lieQuotientCoordinateEquiv_symm_apply (e : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (D : Matrix κ ι ℚ)
    (hker : LinearMap.ker D.mulVecLin = I.toSubmodule.map e.equivFun.toLinearMap)
    (hsurj : Function.Surjective D.mulVec) (S : Matrix ι κ ℚ) (hS : D * S = 1) (y : κ → ℚ) :
    (lieQuotientCoordinateEquiv e I D hker hsurj).symm y =
      lieQuotientMap I (e.equivFun.symm (S *ᵥ y)) := by
  apply (lieQuotientCoordinateEquiv e I D hker hsurj).injective
  rw [LinearEquiv.apply_symm_apply, lieQuotientCoordinateEquiv_apply_mk,
    LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, hS, Matrix.one_mulVec]

omit [DecidableEq ι] in
theorem coordinate_span_matrix_range {η : Type*} [Fintype η]
    (e : Basis ι ℚ L) (v : η → L) (I : Submodule ℚ L)
    (hspan : Submodule.span ℚ (Set.range v) = I) :
    LinearMap.range (Matrix.mulVecLin (show Matrix ι η ℚ from fun i j => e.repr (v j) i)) =
      I.map e.equivFun.toLinearMap := by
  rw [Matrix.range_mulVecLin, ← hspan, Submodule.map_span, ← Set.range_comp]
  rfl

theorem exists_bounded_lie_quotient_coordinates {η : Type*} [Fintype η]
    (e : Basis ι ℚ L) (I : LieIdeal ℚ L) (v : η → L)
    (hspan : Submodule.span ℚ (Set.range v) = I.toSubmodule) {H : ℕ} (hHpos : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (e.repr (v j) i) H) :
    ∃ t : ℕ, t ≤ Fintype.card η ∧ ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ b : Basis (Fin d) ℚ (L ⧸ I), ∃ D : Matrix (Fin d) ι ℚ, ∃ S : Matrix ι (Fin d) ℚ,
        LinearMap.toMatrix e b (lieQuotientMap I).toLinearMap = D ∧ D * S = 1 ∧
        (∀ i j, RationalHeightLE (D i j) (rationalKernelHeight t H)) ∧
        ∀ i j, RationalHeightLE (S i j) (rationalSolveHeight d (rationalKernelHeight t H)) := by
  classical
  let A : Matrix ι η ℚ := fun i j => e.repr (v j) i
  obtain ⟨t, ht, d, hd, D, S, hker, hDS, hD, hS⟩ := exists_bounded_quotient_presentation A hHpos hv
  have hker' : LinearMap.ker D.mulVecLin = I.toSubmodule.map e.equivFun.toLinearMap :=
    hker.trans (coordinate_span_matrix_range e v I.toSubmodule hspan)
  have hsurj : Function.Surjective D.mulVec := by
    intro y
    refine ⟨S *ᵥ y, ?_⟩
    rw [Matrix.mulVec_mulVec, hDS, Matrix.one_mulVec]
  exact ⟨t, ht, d, hd, lieQuotientCoordinateBasis e I D hker' hsurj, D, S,
    lieQuotientCoordinateBasis_matrix e I D hker' hsurj, hDS, hD, hS⟩

theorem exists_bounded_lie_quotient_with_structure {η : Type*} [Fintype η]
    (e : Basis ι ℚ L) (I : LieIdeal ℚ L) (v : η → L)
    (hspan : Submodule.span ℚ (Set.range v) = I.toSubmodule) {H : ℕ} (hHpos : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (e.repr (v j) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) :
    ∃ t : ℕ, t ≤ Fintype.card η ∧ ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ b : Basis (Fin d) ℚ (L ⧸ I), ∃ D : Matrix (Fin d) ι ℚ, ∃ S : Matrix ι (Fin d) ℚ,
        LinearMap.toMatrix e b (lieQuotientMap I).toLinearMap = D ∧ D * S = 1 ∧
        (∀ i j, RationalHeightLE (D i j) (rationalKernelHeight t H)) ∧
        (∀ i j, RationalHeightLE (S i j) (rationalSolveHeight d (rationalKernelHeight t H))) ∧
        ∀ i j k, RationalHeightLE (lieStructureConstants b i j k)
          (rationalLieStructureHeight (Fintype.card ι)
            (max H (max (rationalKernelHeight t H) (rationalSolveHeight d (rationalKernelHeight t H))))) := by
  obtain ⟨t, ht, d, hd, b, D, S, hmatrix, hDS, hD, hS⟩ :=
    exists_bounded_lie_quotient_coordinates e I v hspan hHpos hv
  refine ⟨t, ht, d, hd, b, D, S, hmatrix, hDS, hD, hS, ?_⟩
  intro i j k
  rw [lieStructureConstants_quotient_matrix e b (lieQuotientMap I) S
    (by rw [hmatrix]; exact hDS), hmatrix]
  exact transportedLieConstants_height_uniform _ _ _
    (fun u v w => (hc u v w).mono (le_max_left _ _))
    (fun u v => (hD u v).mono ((le_max_left _ _).trans (le_max_right _ _)))
    (fun u v => (hS u v).mono ((le_max_right _ _).trans (le_max_right _ _))) i j k

end Erdos3

end

section

namespace Erdos3

open Module

variable {ι η L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem exists_bounded_lie_subalgebra_basis (e : Basis ι ℚ L) (K : LieSubalgebra ℚ L)
    (v : η → K) (hspan : Submodule.span ℚ (Set.range v) = ⊤) {H : ℕ}
    (hv : ∀ i j, RationalHeightLE (e.repr (v i : L) j) H) :
    ∃ b : Basis (Fin (Module.finrank ℚ K)) ℚ K,
      ∀ i j, RationalHeightLE (e.repr (b i : L) j) H := by
  classical
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hspan, finrank_top] at hex
  obtain ⟨w, hw, hwspan, hwli⟩ := hex
  refine ⟨Basis.mk hwli (by rw [hwspan]), ?_⟩
  intro i j
  rw [Basis.mk_apply]
  obtain ⟨a, ha⟩ := hw i
  rw [← ha]
  exact hv a j

theorem lie_subalgebra_finrank_le (e : Basis ι ℚ L) (K : LieSubalgebra ℚ L) :
    Module.finrank ℚ K ≤ Fintype.card ι := by
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  have h := LinearMap.finrank_le_finrank_of_injective (f := K.incl.toLinearMap)
    (fun _ _ h => Subtype.ext h)
  simpa only [Module.finrank_eq_card_basis e] using h

theorem lie_lowerCentralSeries_eq_bot_of_injective {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (φ : M →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    LieModule.lowerCentralSeries ℚ M M s = ⊥ := by
  apply LieIdeal.bot_of_map_eq_bot hφ
  apply le_antisymm _ bot_le
  rw [← hnil]
  exact LieIdeal.map_lowerCentralSeries_le s

theorem lie_subalgebra_lowerCentralSeries_eq_bot {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (K : LieSubalgebra ℚ L) :
    LieModule.lowerCentralSeries ℚ K K s = ⊥ :=
  lie_lowerCentralSeries_eq_bot_of_injective K.incl (fun _ _ h => Subtype.ext h) hnil

theorem exists_lie_subalgebra_basis_exp_height (e : Basis ι ℚ L) (K : LieSubalgebra ℚ L)
    (v : η → K) (hspan : Submodule.span ℚ (Set.range v) = ⊤) {H : ℕ} (hHpos : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (e.repr (v i : L) j) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ b : Basis (Fin (Module.finrank ℚ K)) ℚ K,
      (∀ i j, RationalHeightLE (e.repr (b i : L) j) H) ∧
      ∀ i j k, ((lieStructureConstants b i j k).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 11) ∧
        ((lieStructureConstants b i j k).den : ℝ) ≤ Real.exp ((p + 2) ^ 11) := by
  classical
  obtain ⟨b, hb⟩ := exists_bounded_lie_subalgebra_basis e K v hspan hv
  obtain ⟨_, _, _, hstructure⟩ := exists_bounded_lie_embedding_retraction b e K.incl
    (fun _ _ h => Subtype.ext h) hHpos hc (by
      intro i j
      rw [LinearMap.toMatrix_apply]
      change RationalHeightLE (e.repr (b j : L) i) H
      exact hb j i)
  refine ⟨b, hb, ?_⟩
  have hr : (Fintype.card (Fin (Module.finrank ℚ K)) : ℝ) ≤ p := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr (lie_subalgebra_finrank_le e K)).trans hd
  have hbound := rationalLieStructureHeight_inverse_budget (Fintype.card ι)
    (Fintype.card (Fin (Module.finrank ℚ K))) H hp hd hr hH
  intro i j k
  exact ⟨(Nat.cast_le.mpr (hstructure i j k).1).trans hbound,
    (Nat.cast_le.mpr (hstructure i j k).2).trans hbound⟩

end Erdos3

end

end OAI
