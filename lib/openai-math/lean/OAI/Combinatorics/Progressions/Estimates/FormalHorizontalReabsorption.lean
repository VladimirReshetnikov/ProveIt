import OAI.Combinatorics.Progressions.Linear.FormalKernelAbsorption
import OAI.Combinatorics.Progressions.Polynomial.PolynomialLiftMatching

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hF in
theorem formal_horizontal_logDerivative (hs : 1 ≤ s) (i : σ)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot) :
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ) (formalLogDerivative i P) =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord) := by
  have hP : ∀ α, coefficients P.coord α ∈ F.realification.layer 1 := by
    intro α
    rw [F.realification.one_eq_top]
    trivial
  have hD := pderiv_mem_submodule (F.realification.layer 1) P.coord hP i
  have hrem := F.realification.polynomialFiltration.dualLogDerivative_sub_tangent_mem_layer hs
    (i := 1) (j := 1) (formalPolynomialJetHom i P)
    (by rw [formalPolynomialJet_base]; exact hP)
    (by rw [formalPolynomialJet_tangent]; exact hD)
  rw [formalPolynomialJet_tangent] at hrem
  exact F.polynomial_grade_eq_of_sub_mem_next b w hF 1 _ _ hrem

include hF in
theorem formal_derivative_horizontal_balance (hs : 2 ≤ s)
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational extra)
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer 2).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer 2).toSubmodule) :
    ∀ i α, coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ) (extra i)) α ∈ V := by
  intro i α
  have hP : ∀ β, coefficients P.coord β ∈ F.realification.layer 1 := by
    intro β
    rw [F.realification.one_eq_top]
    trivial
  have hY := congrArg (fun Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients Q α)
    (F.formal_horizontal_logDerivative b w hF (by omega) i P)
  have hAd := congrArg (fun Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients Q α)
    (F.polynomial_grade_adjoint_eq b w hF hs 1 P hP (rational i))
  simp only [coefficients_map, LinearMap.restrictScalars_apply] at hY hAd
  have herr := hV 1 _ (hsystem i α)
  simp only [map_sub, map_add, Finsupp.sub_apply, Finsupp.add_apply] at herr
  rw [hY, hAd] at herr
  have hS := F.realGradeProjection_mem_of_mem_sup_next b w hF V hV 1 _ (hsmall i α)
  have hR := F.realGradeProjection_mem_of_mem_sup_next b w hF V hV 1 _ (hrational i α)
  have h := V.add_mem herr (V.add_mem hS hR)
  simp only [map_sub, Finsupp.sub_apply, coefficients_map, LinearMap.restrictScalars_apply]
  convert h using 1
  abel

include hF in
theorem formal_extra_horizontal_equation (hs : 2 ≤ s)
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) (j : ℕ)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational extra)
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer 2).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer 2).toSubmodule)
    (hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ) (extra i)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  intro i α
  have hbalance := F.formal_derivative_horizontal_balance b w hF hs V hV P small rational extra
    hsystem hsmall hrational i α
  have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).sub_mem (hextra i α) (Submodule.mem_sup_left hbalance)
  simp only [map_sub, Finsupp.sub_apply] at h ⊢
  convert h using 1
  abel

include hF in
theorem formal_lift_nonhorizontal_remainder
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    {j : ℕ} (hj : 1 ≤ j) (X : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : ℝ ⊗[ℚ] L)
    (hk : basisGradeProjection (b.baseChange ℝ) w 1 k = k)
    (hX : ∀ α, coefficients (X - monomial 0 k) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    ∀ α, coefficients (X - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ) X) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  have hproj (x : ℝ ⊗[ℚ] L) (hx : x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule) :
      basisGradeProjection (b.baseChange ℝ) w 1 x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, F.realGradeProjection_eq_zero_of_mem_next_layer b w hF 1 z
      (F.realification.antitone (by omega) hz), add_zero]
    exact Submodule.mem_sup_left (hV 1 v hv)
  intro α
  have hkα : basisGradeProjection (b.baseChange ℝ) w 1 (coefficients (monomial 0 k : VectorPolynomial σ ℚ _) α) =
      coefficients (monomial 0 k : VectorPolynomial σ ℚ _) α := by
    rw [coefficients_monomial]
    by_cases hα : α = 0
    · subst α
      simpa only [Finsupp.single_eq_same] using hk
    · rw [Finsupp.single_eq_of_ne hα, map_zero]
  have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).sub_mem (hX α) (hproj _ (hX α))
  simp only [map_sub, Finsupp.sub_apply, hkα] at h
  simp only [map_sub, Finsupp.sub_apply, coefficients_map, LinearMap.restrictScalars_apply]
  convert h using 1
  abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

section General

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem formal_logDerivative_sub_pderiv_mem_two (hs : 1 ≤ s) (i : σ)
    (A : PolynomialGroup σ F.lowerCentralSeries_eq_bot) :
    ∀ α, coefficients (formalLogDerivative i A - (MvPolynomial.pderiv i).toLinearMap.rTensor L A.coord) α ∈ F.layer 2 := by
  have hA : ∀ α, coefficients A.coord α ∈ F.layer 1 := by intro α; rw [F.one_eq_top]; trivial
  have hD := pderiv_mem_submodule (F.layer 1) A.coord hA i
  have h := F.polynomialFiltration.dualLogDerivative_sub_tangent_mem_layer hs
    (i := 1) (j := 1) (formalPolynomialJetHom i A)
    (by rw [formalPolynomialJet_base]; exact hA) (by rw [formalPolynomialJet_tangent]; exact hD)
  rw [formalPolynomialJet_tangent] at h
  exact h

theorem formal_reabsorption_preserves_layer_two (hs : 2 ≤ s) (V : Submodule ℚ L) (i : σ)
    (A B : PolynomialGroup σ F.lowerCentralSeries_eq_bot)
    (small rational left right : VectorPolynomial σ ℚ L)
    (hsmall : ∀ α, coefficients small α ∈ V ⊔ F.layer 2)
    (hrational : ∀ α, coefficients rational α ∈ V ⊔ F.layer 2)
    (hleft : ∀ α, coefficients (left - (MvPolynomial.pderiv i).toLinearMap.rTensor L A.coord) α ∈ V ⊔ F.layer 2)
    (hright : ∀ α, coefficients (right - (MvPolynomial.pderiv i).toLinearMap.rTensor L B.coord) α ∈ V ⊔ F.layer 2) :
    (∀ α, coefficients (dualAdjoint A⁻¹ (small - formalLogDerivative i A) + left) α ∈ V ⊔ F.layer 2) ∧
      ∀ α, coefficients (dualAdjoint B rational - formalLogDerivative i B + right) α ∈ V ⊔ F.layer 2 := by
  let W := coefficientSubmodule (σ := σ) (V ⊔ F.layer 2)
  have hA : ∀ α, coefficients A⁻¹.coord α ∈ F.layer 1 := by intro α; rw [F.one_eq_top]; trivial
  have hB : ∀ α, coefficients B.coord α ∈ F.layer 1 := by intro α; rw [F.one_eq_top]; trivial
  have ha := F.polynomialFiltration.adjoint_correction_sub_mem_layer hs 1 A⁻¹ hA (small - formalLogDerivative i A)
  have hb := F.polynomialFiltration.adjoint_correction_sub_mem_layer hs 1 B hB rational
  have hYa := F.formal_logDerivative_sub_pderiv_mem_two (by omega) i A
  have hYb := F.formal_logDerivative_sub_pderiv_mem_two (by omega) i B
  have haW : dualAdjoint A⁻¹ (small - formalLogDerivative i A) - (small - formalLogDerivative i A) ∈ W :=
    fun α => Submodule.mem_sup_right (ha α)
  have hbW : dualAdjoint B rational - rational ∈ W := fun α => Submodule.mem_sup_right (hb α)
  have hYaW : formalLogDerivative i A - (MvPolynomial.pderiv i).toLinearMap.rTensor L A.coord ∈ W :=
    fun α => Submodule.mem_sup_right (hYa α)
  have hYbW : formalLogDerivative i B - (MvPolynomial.pderiv i).toLinearMap.rTensor L B.coord ∈ W :=
    fun α => Submodule.mem_sup_right (hYb α)
  constructor
  · have h : dualAdjoint A⁻¹ (small - formalLogDerivative i A) + left ∈ W := by
      convert W.add_mem (W.sub_mem (W.add_mem hsmall haW) hYaW) hleft using 1
      abel
    exact h
  · have h : dualAdjoint B rational - formalLogDerivative i B + right ∈ W := by
      convert W.add_mem (W.sub_mem (W.add_mem hrational hbW) hYbW) hright using 1
      abel
    exact h

end General

variable {μ σ K L : Type*} [AddCommGroup K] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hF in
theorem formal_degree_two_reabsorption (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (I : K →+ ℝ ⊗[ℚ] L) (hI : ∀ x, basisGradeProjection (b.baseChange ℝ) w 1 (I x) = I x)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hAU : ∀ α, coefficients A.coord α ∈ U)
    (hAhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ 1 → coefficients A.coord α = 0)
    (hBhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ 1 → coefficients B.coord α = 0)
    (S R : K →+ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k a c : σ → K)
    (ha : ∀ i, I (a i) = coefficients A.coord (Finsupp.single i 1))
    (hc : ∀ i, I (c i) = coefficients B.coord (Finsupp.single i 1))
    (hSR : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R)
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational (fun i => S (k i)))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer 2).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer 2).toSubmodule)
    (hS : ∀ x α, coefficients (dualAdjoint A⁻¹ (S x) - monomial 0 (I x)) α ∈ V ⊔ (F.realLayer 3).toSubmodule)
    (hR : ∀ x α, coefficients (dualAdjoint B (R x) - monomial 0 (I x)) α ∈ V ⊔ (F.realLayer 3).toSubmodule) :
    let P' := A⁻¹ * P * B⁻¹
    let S' := (dualAdjointAddEquiv A⁻¹).toAddMonoidHom.comp S
    let R' := (dualAdjointAddEquiv B).toAddMonoidHom.comp R
    let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A) + S' (a i)
    let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B + R' (c i)
    let extra' := fun i => S' (k i - a i - c i)
    PolynomialLiftSystemMod (V.restrictScalars ℚ) P' S' R' ∧
      PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P' small' rational' extra' ∧
      (∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer 2).toSubmodule ∧
        coefficients (rational' i) α ∈ V ⊔ (F.realLayer 2).toSubmodule) ∧
      ∀ i α, coefficients (extra' i - VectorPolynomial.map
        ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈ V ⊔ (F.realLayer 3).toSubmodule := by
  intro P' S' R' small' rational' extra'
  have hsystem' := formal_remove_and_absorb U (V.restrictScalars ℚ) hUV P A B hAU S R
    small rational k a c hSR hsystem
  have hWiff (d : ℕ) (x : ℝ ⊗[ℚ] L) :
      x ∈ V.restrictScalars ℚ ⊔ F.realification.layer d ↔ x ∈ V ⊔ (F.realLayer d).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer d).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have h32 : V.restrictScalars ℚ ⊔ F.realification.layer 3 ≤ V.restrictScalars ℚ ⊔ F.realification.layer 2 :=
    sup_le_sup_left (F.realification.antitone (by decide : 2 ≤ 3)) _
  have hlow (i : σ) := F.realification.formal_reabsorption_preserves_layer_two hs (V.restrictScalars ℚ) i A B
    (small i) (rational i) (S' (a i)) (R' (c i))
    (fun α => (hWiff 2 _).mpr (hsmall i α)) (fun α => (hWiff 2 _).mpr (hrational i α))
    (fun α => by
      rw [homogeneous_one_pderiv A.coord hAhom i, ← ha i]
      exact h32 ((hWiff 3 _).mpr (hS (a i) α)))
    (fun α => by
      rw [homogeneous_one_pderiv B.coord hBhom i, ← hc i]
      exact h32 ((hWiff 3 _).mpr (hR (c i) α)))
  have hsmall' : ∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer 2).toSubmodule :=
    fun i α => (hWiff 2 _).mp ((hlow i).1 α)
  have hrational' : ∀ i α, coefficients (rational' i) α ∈ V ⊔ (F.realLayer 2).toSubmodule :=
    fun i α => (hWiff 2 _).mp ((hlow i).2 α)
  refine ⟨hsystem'.1, hsystem'.2, (fun i α => ⟨hsmall' i α, hrational' i α⟩), ?_⟩
  apply F.formal_extra_horizontal_equation b w hF hs V hV 2 P' small' rational' extra'
    hsystem'.2 hsmall' hrational'
  intro i
  exact F.formal_lift_nonhorizontal_remainder b w hF V hV (by decide : 1 ≤ 2)
    (extra' i) (I (k i - a i - c i)) (hI _) (hS _)

end Erdos3.NilpotentLieFiltration

end

end OAI
