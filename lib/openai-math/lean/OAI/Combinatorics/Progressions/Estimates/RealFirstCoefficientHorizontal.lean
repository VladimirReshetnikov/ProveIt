/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.FastCoefficientImage
import OAI.Combinatorics.Progressions.Estimates.RealDirectionExtension
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDerivativeBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

noncomputable def realAdaptedDirectionalDerivative :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) →ₗ[ℝ]
      (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :=
  (F.adaptedDirectionalDerivative h).baseChange ℝ

theorem realAdaptedDirectionalDerivative_polynomial
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedPolynomialMap (fun _ => 1) (F.realAdaptedDirectionalDerivative h x) =
      directionalDerivative h (F.realAdaptedPolynomialMap (fun _ => 1) x) := by
  apply coefficients.injective
  ext α
  induction x using TensorProduct.inductionOn with
  | tmul r p =>
    change coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
      ((F.adaptedDirectionalDerivative h).baseChange ℝ (r ⊗ₜ[ℚ] p))) α = _
    rw [LinearMap.baseChange_tmul, F.realAdaptedPolynomialMap_coefficient_tmul,
      F.adaptedDirectionalDerivative_coe, coefficients_directionalDerivative,
      coefficients_directionalDerivative]
    simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      F.realAdaptedPolynomialMap_coefficient_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem realAdaptedDirectionalDerivative_tensor
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedPolynomialTensor (fun _ => 1) (F.realAdaptedDirectionalDerivative h x) =
      F.realification.adaptedDirectionalDerivative h (F.realAdaptedPolynomialTensor (fun _ => 1) x) := by
  apply Subtype.ext
  exact F.realAdaptedDirectionalDerivative_polynomial h x

theorem realAdaptedDirectionalDerivative_bound (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T M x)
    (hh : ∀ i, |(h i : ℝ)| ≤ T i) :
    F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T ((Fintype.card σ : ℝ) * s * M)
      (F.realAdaptedDirectionalDerivative h x) := by
  have hp := (F.realAdaptedCoefficientBound_polynomial_iff b ω hF (fun _ => 1) T hT hM
    (⟨x⟩ : F.RealAdaptedPolynomialGroup (fun _ => 1))).mp hx
  intro z
  rw [← F.realAdaptedPolynomialTensor_coordinates (fun _ => 1) b ω hF,
    F.realAdaptedDirectionalDerivative_polynomial]
  let f := ((b.baseChange ℝ).coord z.val.2).restrictScalars ℚ
  have hdegree : ∀ (β : σ →₀ ℕ) (j : σ), s < β j →
      f (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) β) = 0 := by
    intro β j hj
    have hβ := Finsupp.le_weight (fun _ : σ => 1) (s := j) (by decide) β
    have hi := F.adaptedBasis_weight_le_step b ω hF z.val.2
    have hni : ¬ Finsupp.weight (fun _ : σ => 1) β ≤ ω z.val.2 := by omega
    exact (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp
      ((F.realification.adapted_iff_coefficients (fun _ => 1) _).mp
        (F.realAdaptedPolynomialMap_adapted (fun _ => 1) x) β) z.val.2 hni
  exact directionalDerivative_scaled_coordinate_bound f
    (F.realAdaptedPolynomialMap (fun _ => 1) x) s hdegree T hT M hM
    (fun β => hp β z.val.2) h hh z.val.1

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

noncomputable def realAdaptedPolynomialJet
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    DualGroup (F.adaptedPolynomialFiltration (fun _ : σ => 1)).realification.lowerCentralSeries_eq_bot :=
  ⟨dualConstantLie x + dualInfinitesimal (F.realAdaptedDirectionalDerivative h x)⟩

@[simp] theorem realAdaptedPolynomialJet_base
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    dualBaseLinear (F.realAdaptedPolynomialJet h x).coord = x := by
  change dualBaseLinear (dualConstantLie x + dualInfinitesimal _) = x
  simp only [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

@[simp] theorem realAdaptedPolynomialJet_tangent
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    dualTangentLinear (F.realAdaptedPolynomialJet h x).coord = F.realAdaptedDirectionalDerivative h x := by
  change dualTangentLinear (dualConstantLie x + dualInfinitesimal _) = _
  simp only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]

noncomputable def realAdaptedLogDerivative
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1) :=
  dualLogDerivative (F.realAdaptedPolynomialJet h x)

theorem realAdaptedLogDerivative_tensor
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedPolynomialTensor (fun _ => 1) (F.realAdaptedLogDerivative h x) =
      F.realification.adaptedLogDerivative h (F.realAdaptedPolynomialTensor (fun _ => 1) x) := by
  let φ := F.realAdaptedPolynomialTensor (fun _ : σ => 1)
  apply dualLinearLift_logDerivative_eq
    (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot
    (⊤ : LieIdeal ℚ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))) φ φ.toLinearMap
    (fun u v _ => φ.map_lie u v) (F.realAdaptedPolynomialJet h x) (by trivial)
    (F.realification.adaptedPolynomialJet h (φ x))
  rw [dualLinearLift_apply, F.realAdaptedPolynomialJet_base, F.realAdaptedPolynomialJet_tangent]
  change dualConstantLie (φ x) + dualInfinitesimal (φ (F.realAdaptedDirectionalDerivative h x)) =
    dualConstantLie (φ x) + dualInfinitesimal (F.realification.adaptedDirectionalDerivative h (φ x))
  rw [F.realAdaptedDirectionalDerivative_tensor]

theorem exists_real_adapted_log_derivative_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1),
      F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp ((p + 2) ^ a)) x →
      ∀ h : σ → ℚ, (∀ i, |(h i : ℝ)| ≤ T i) →
      F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C))
        (F.realAdaptedLogDerivative h x) := by
  have hoperationsExists := exists_scaled_polynomial_dual_bound s 1
  obtain ⟨c, _, hoperations⟩ := hoperationsExists
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ a +
    Polynomial.C (s + 1) * (Polynomial.X + 1) + Polynomial.X + 2
  let B : Polynomial ℕ := (Q + Polynomial.C c) ^ c
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc T hT x hx h hh
  let t := (s + 1 : ℝ) * (p + 1)
  let q := (p + 2) ^ a + t + p + 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ha : 0 ≤ (p + 2) ^ a := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have haq : (p + 2) ^ a ≤ q + 2 := by dsimp [q]; linarith
  have hfinal : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [B, Q, q, t, Polynomial.eval₂_pow] using hbound p hp
  have hfactor : (Fintype.card σ : ℝ) * s ≤ Real.exp t := by
    have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
    have hmul := mul_le_mul_of_nonneg_right hσ hs
    have hsmall : (Fintype.card σ : ℝ) * s ≤ t := by dsimp [t]; nlinarith
    exact hsmall.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp t))
  have hgain : (Fintype.card σ : ℝ) * s * Real.exp ((p + 2) ^ a) ≤ Real.exp (q + 2) := by
    apply (mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [q]
    linarith
  have hvalue := F.realAdaptedCoefficientBound_mono b ω hF (fun _ => 1) T hT
    (Real.exp_le_exp.mpr haq) x hx
  have hderivative := F.realAdaptedCoefficientBound_mono b ω hF (fun _ => 1) T hT hgain
    (F.realAdaptedDirectionalDerivative h x)
    (F.realAdaptedDirectionalDerivative_bound h b ω hF T hT (Real.exp_nonneg _) x hx hh)
  have hdual := (hoperations F b ω hF (fun _ : σ => 1) (by simp) H q hH hq
    (hι.trans hpq) (hσ.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq)) hc T hT).1
    (F.realAdaptedPolynomialJet h x)
    (by simpa only [F.realAdaptedPolynomialJet_base, pow_one] using hvalue)
    (by simpa only [F.realAdaptedPolynomialJet_tangent, pow_one] using hderivative)
  exact F.realAdaptedCoefficientBound_mono b ω hF (fun _ => 1) T hT
    (Real.exp_le_exp.mpr hfinal) _ hdual

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

theorem directionalDerivative_single {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] (i : σ) (P : VectorPolynomial σ ℚ L) :
    directionalDerivative (Pi.single i 1) P = (MvPolynomial.pderiv i).toLinearMap.rTensor L P := by
  simp [directionalDerivative, Pi.single_apply]

end VectorPolynomial

namespace NilpotentLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adaptedLogDerivative_eq_formal (i : σ)
    (P : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (F.adaptedLogDerivative (Pi.single i 1) P : VectorPolynomial σ ℚ L) =
      formalLogDerivative (hnil := F.lowerCentralSeries_eq_bot) i ⟨P.val⟩ := by
  let φ := (F.adaptedLieSubalgebra (fun _ : σ => 1)).incl
  apply dualLinearLift_logDerivative_eq
    (VectorPolynomial.lowerCentralSeries_eq_bot (σ := σ) F.lowerCentralSeries_eq_bot)
    ⊤ φ φ.toLinearMap (fun a b _ => φ.map_lie a b)
    (F.adaptedPolynomialJet (Pi.single i 1) P) (by trivial)
    (formalPolynomialJetHom i (⟨P.val⟩ : PolynomialGroup σ F.lowerCentralSeries_eq_bot))
  rw [dualLinearLift_apply, F.adaptedPolynomialJet_base, F.adaptedPolynomialJet_tangent]
  change dualConstantLie P.val + dualInfinitesimal (directionalDerivative (Pi.single i 1) P.val) =
    dualConstantLie P.val + dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.val)
  rw [directionalDerivative_single]

theorem realAdaptedLogDerivative_eq_formal (i : σ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedPolynomialMap (fun _ => 1) (F.realAdaptedLogDerivative (Pi.single i 1) x) =
      formalLogDerivative (hnil := F.realification.lowerCentralSeries_eq_bot) i
        ⟨F.realAdaptedPolynomialMap (fun _ => 1) x⟩ := by
  have h := congrArg
    (fun P : F.realification.adaptedLieSubalgebra (fun _ : σ => 1) => P.val)
    (F.realAdaptedLogDerivative_tensor (Pi.single i 1) x)
  exact h.trans (F.realification.adaptedLogDerivative_eq_formal i
    (F.realAdaptedPolynomialTensor (fun _ => 1) x))

omit [Fintype σ] [DecidableEq σ] in
noncomputable def realFullPolynomialLie (v : σ → ℕ) :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra v) →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  (F.realification.adaptedLieSubalgebra v).incl.comp (F.realAdaptedPolynomialTensor v)

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem realFullPolynomialLie_apply (v : σ → ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra v) :
    F.realFullPolynomialLie v x = F.realAdaptedPolynomialMap v x := rfl

omit [Fintype σ] [DecidableEq σ] in
noncomputable def realFullPolynomialHom (v : σ → ℕ) :
    F.RealAdaptedPolynomialGroup v →* PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot :=
  NilpotentLieBCHGroup.map (F.realFullPolynomialLie v)

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem realFullPolynomialHom_coord (v : σ → ℕ) (P : F.RealAdaptedPolynomialGroup v) :
    (F.realFullPolynomialHom v P).coord = F.realAdaptedPolynomialMap v P.coord := rfl

omit [Fintype σ] [DecidableEq σ] in
theorem realAdaptedAdjoint_eq_formal (v : σ → ℕ) (P : F.RealAdaptedPolynomialGroup v)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra v) :
    F.realAdaptedPolynomialMap v (dualAdjoint P x) =
      dualAdjoint (F.realFullPolynomialHom v P) (F.realAdaptedPolynomialMap v x) :=
  map_dualAdjoint (F.realFullPolynomialLie v) P x

theorem realAdapted_derivative_system_to_formal (P : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (small rational extra : σ → ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hsystem : ∀ i, F.realAdaptedLogDerivative (Pi.single i 1) P.coord =
      small i + dualAdjoint P (rational i) + extra i) :
    PolynomialDerivativeSystem (F.realFullPolynomialHom (fun _ => 1) P)
      (fun i => F.realAdaptedPolynomialMap (fun _ => 1) (small i))
      (fun i => F.realAdaptedPolynomialMap (fun _ => 1) (rational i))
      (fun i => F.realAdaptedPolynomialMap (fun _ => 1) (extra i)) := by
  intro i
  have h := congrArg (F.realAdaptedPolynomialMap (fun _ => 1)) (hsystem i)
  rw [F.realAdaptedLogDerivative_eq_formal, map_add, map_add, F.realAdaptedAdjoint_eq_formal] at h
  exact h

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realAdaptedDirectionalTangent
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (σ → ℚ) →ₗ[ℚ] (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) where
  toFun h := F.realAdaptedDirectionalDerivative h x
  map_add' h k := by
    induction x using TensorProduct.inductionOn with
    | tmul r p =>
      change r ⊗ₜ[ℚ] (F.adaptedDirectionalTangent p (h + k)) =
        r ⊗ₜ[ℚ] (F.adaptedDirectionalTangent p h) + r ⊗ₜ[ℚ] (F.adaptedDirectionalTangent p k)
      rw [map_add, TensorProduct.tmul_add]
    | add x y hx hy => simp only [map_add, hx, hy]; abel
  map_smul' q h := by
    induction x using TensorProduct.inductionOn with
    | tmul r p =>
      change r ⊗ₜ[ℚ] (F.adaptedDirectionalTangent p (q • h)) =
        q • (r ⊗ₜ[ℚ] (F.adaptedDirectionalTangent p h))
      rw [map_smul, TensorProduct.tmul_smul]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]

noncomputable def realLogDerivativeDirectionMap
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (σ → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :=
  (dualRealLogarithmicDifferential
    (hnil := (F.adaptedPolynomialFiltration (fun _ : σ => 1)).realification.lowerCentralSeries_eq_bot)
      x).comp (realDirectionExtension (F.realAdaptedDirectionalTangent x))

theorem realLogDerivativeDirectionMap_rat
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) (h : σ → ℚ) :
    F.realLogDerivativeDirectionMap x (fun i => (h i : ℝ)) = F.realAdaptedLogDerivative h x := by
  change dualRealLogarithmicDifferential x
    (realDirectionExtension (F.realAdaptedDirectionalTangent x) (fun i => (h i : ℝ))) = _
  rw [realDirectionExtension_rat]
  rfl

theorem realLogDerivativeDirectionMap_polynomial
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) (h : σ → ℚ) :
    F.realAdaptedPolynomialTensor (fun _ => 1)
      (F.realLogDerivativeDirectionMap x (fun i => (h i : ℝ))) =
      F.realification.adaptedLogDerivative h (F.realAdaptedPolynomialTensor (fun _ => 1) x) := by
  rw [F.realLogDerivativeDirectionMap_rat, F.realAdaptedLogDerivative_tensor]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realShiftedCoefficientSubmodule (w : σ → ℕ) (k : ℕ) :
    Submodule ℝ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :=
  (F.shiftedPolynomialIdeal w k).toSubmodule.baseChange ℝ

theorem realShiftedCoefficient_lie_mem (w : σ → ℕ) (k : ℕ)
    (x y : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (hy : y ∈ F.realShiftedCoefficientSubmodule w k) :
    ⁅x, y⁆ ∈ F.realShiftedCoefficientSubmodule w k :=
  ((F.shiftedPolynomialIdeal w k).baseChange ℝ).lie_mem hy

abbrev RealFirstCoefficientModule (w : σ → ℕ) :=
  (F.realShiftedCoefficientSubmodule w 1) ⧸
    (F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype

noncomputable def realFirstCoefficientMap (w : σ → ℕ) :
    (F.realShiftedCoefficientSubmodule w 1) →ₗ[ℝ] F.RealFirstCoefficientModule w :=
  ((F.realShiftedCoefficientSubmodule w 2).comap
    (F.realShiftedCoefficientSubmodule w 1).subtype).mkQ

theorem realFirstCoefficientMap_eq_zero_iff (w : σ → ℕ)
    (x : F.realShiftedCoefficientSubmodule w 1) :
    F.realFirstCoefficientMap w x = 0 ↔ x.val ∈ F.realShiftedCoefficientSubmodule w 2 :=
  Submodule.Quotient.mk_eq_zero _

noncomputable def realFirstCoefficientAdjoint (w : σ → ℕ) (g : F.RealAdaptedPolynomialGroup w) :
    F.RealFirstCoefficientModule w ≃ₗ[ℝ] F.RealFirstCoefficientModule w :=
  invariantRealAdjointQuotient ⊤ (F.realShiftedCoefficientSubmodule w 1)
    (F.realShiftedCoefficientSubmodule w 2)
    (fun x _ y hy => F.realShiftedCoefficient_lie_mem w 1 x y hy)
    (fun x _ y hy => F.realShiftedCoefficient_lie_mem w 2 x y hy) g (by trivial)

@[simp] theorem realFirstCoefficientAdjoint_map (w : σ → ℕ) (g : F.RealAdaptedPolynomialGroup w)
    (x : F.realShiftedCoefficientSubmodule w 1) :
    F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientMap w x) =
      F.realFirstCoefficientMap w
        ⟨dualAdjoint g x.val, dualAdjoint_real_mem_of_invariant ⊤ _
          (fun a _ b hb => F.realShiftedCoefficient_lie_mem w 1 a b hb) g (by trivial) x.val x.property⟩ :=
  rfl

theorem realAdaptedDirectionalDerivative_mem_first [Fintype σ] (h : σ → ℚ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedDirectionalDerivative h x ∈ F.realShiftedCoefficientSubmodule (fun _ => 1) 1 := by
  induction x using TensorProduct.inductionOn with
  | tmul r p =>
    change r ⊗ₜ[ℚ] (F.adaptedDirectionalDerivative h p) ∈
      (F.shiftedPolynomialIdeal (fun _ => 1) 1).toSubmodule.baseChange ℝ
    exact Submodule.tmul_mem_baseChange_of_mem r (F.directionalDerivative_mem_next h p)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem realAdaptedLogDerivative_mem_first [Fintype σ] (h : σ → ℚ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedLogDerivative h x ∈ F.realShiftedCoefficientSubmodule (fun _ => 1) 1 := by
  apply dualLogDerivative_mem_of_invariant ⊤
    ((F.realShiftedCoefficientSubmodule (fun _ => 1) 1).restrictScalars ℚ)
    (fun a _ b hb => F.realShiftedCoefficient_lie_mem (fun _ => 1) 1 a b hb)
    (F.realAdaptedPolynomialJet h x) (by trivial)
  rw [F.realAdaptedPolynomialJet_tangent]
  exact F.realAdaptedDirectionalDerivative_mem_first h x

theorem realLogDerivativeDirectionMap_mem_first [Fintype σ]
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) (h : σ → ℝ) :
    F.realLogDerivativeDirectionMap x h ∈ F.realShiftedCoefficientSubmodule (fun _ => 1) 1 := by
  classical
  have he : h = ∑ i, h i • Pi.single i (1 : ℝ) := by ext j; simp [Pi.single_apply]
  rw [he, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  apply Submodule.smul_mem
  have hunit : (Pi.single i (1 : ℝ)) = (fun j => (((Pi.single i (1 : ℚ) : σ → ℚ) j) : ℝ)) := by
    ext j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  rw [hunit, F.realLogDerivativeDirectionMap_rat]
  exact F.realAdaptedLogDerivative_mem_first _ x

noncomputable def realFirstCoefficientDirectionMap [Fintype σ]
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (σ → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule (fun _ : σ => 1) :=
  (F.realFirstCoefficientMap (fun _ => 1)).comp
    ((F.realLogDerivativeDirectionMap x).codRestrict
      (F.realShiftedCoefficientSubmodule (fun _ => 1) 1) (F.realLogDerivativeDirectionMap_mem_first x))

theorem realFirstCoefficientDirectionMap_rat [Fintype σ]
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) (h : σ → ℚ) :
    F.realFirstCoefficientDirectionMap x (fun i => (h i : ℝ)) =
      F.realFirstCoefficientMap (fun _ => 1)
        ⟨F.realAdaptedLogDerivative h x, F.realAdaptedLogDerivative_mem_first h x⟩ := by
  apply congrArg (F.realFirstCoefficientMap (fun _ => 1))
  apply Subtype.ext
  exact F.realLogDerivativeDirectionMap_rat x h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def firstCoefficientRealEquiv :
    (ℝ ⊗[ℚ] F.FirstCoefficientModule w) ≃ₗ[ℝ] F.RealFirstCoefficientModule w :=
  realSubquotientEquiv (F.shiftedPolynomialIdeal w 1).toSubmodule (F.shiftedPolynomialIdeal w 2).toSubmodule

theorem firstCoefficientRealEquiv_map (x : ℝ ⊗[ℚ] (F.shiftedPolynomialIdeal w 1)) :
    F.firstCoefficientRealEquiv w ((F.firstCoefficientMap w).baseChange ℝ x) =
      F.realFirstCoefficientMap w (realificationSubmoduleEquiv (F.shiftedPolynomialIdeal w 1).toSubmodule x) :=
  realSubquotientEquiv_project _ _ x

noncomputable def realFirstCoefficientHorizontal :
    F.RealFirstCoefficientModule w →ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :=
  ((F.firstCoefficientHorizontal w).baseChange ℝ).comp (F.firstCoefficientRealEquiv w).symm.toLinearMap

noncomputable def realFirstCoefficientHorizontalSection :
    (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) →ₗ[ℝ] F.RealFirstCoefficientModule w :=
  (F.firstCoefficientRealEquiv w).toLinearMap.comp ((F.firstCoefficientHorizontalSection w).baseChange ℝ)

theorem realFirstCoefficientHorizontal_section (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    F.realFirstCoefficientHorizontal w (F.realFirstCoefficientHorizontalSection w x) = x := by
  change (F.firstCoefficientHorizontal w).baseChange ℝ
    ((F.firstCoefficientRealEquiv w).symm (F.firstCoefficientRealEquiv w
      ((F.firstCoefficientHorizontalSection w).baseChange ℝ x))) = x
  rw [LinearEquiv.symm_apply_apply]
  induction x using TensorProduct.inductionOn with
  | tmul r v => rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, F.firstCoefficientHorizontal_section]
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def realNormalizedFirstCoefficientMap :
    (ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) →ₗ[ℝ] F.RealFirstCoefficientModule w :=
  (F.firstCoefficientRealEquiv w).toLinearMap.comp ((F.normalizedFirstCoefficientMap w).baseChange ℝ)

theorem realNormalizedFirstCoefficientMap_range :
    LinearMap.range (F.realNormalizedFirstCoefficientMap w) = LinearMap.ker (F.realFirstCoefficientHorizontal w) := by
  have hr : LinearMap.range ((F.normalizedFirstCoefficientMap w).baseChange ℝ) =
      LinearMap.ker ((F.firstCoefficientHorizontal w).baseChange ℝ) := by
    rw [← realification_ker, ← F.normalizedFirstCoefficientMap_range w]
    have he := realification_map (⊤ : Submodule ℚ (F.normalizedRelativeSubmodule w))
      (F.normalizedFirstCoefficientMap w)
    simpa only [Submodule.map_top, Submodule.baseChange_top] using he.symm
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    change (F.firstCoefficientHorizontal w).baseChange ℝ
      ((F.firstCoefficientRealEquiv w).symm (F.firstCoefficientRealEquiv w
        ((F.normalizedFirstCoefficientMap w).baseChange ℝ p))) = 0
    rw [LinearEquiv.symm_apply_apply]
    exact hr.le ⟨p, rfl⟩
  · intro hx
    have hy : (F.firstCoefficientRealEquiv w).symm x ∈
        LinearMap.range ((F.normalizedFirstCoefficientMap w).baseChange ℝ) := hr.ge hx
    obtain ⟨p, hp⟩ := hy
    refine ⟨p, ?_⟩
    change F.firstCoefficientRealEquiv w ((F.normalizedFirstCoefficientMap w).baseChange ℝ p) = x
    rw [hp, LinearEquiv.apply_symm_apply]

end Erdos3.NilpotentLieFiltration

end

end OAI
