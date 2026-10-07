/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import Mathlib.Algebra.MvPolynomial.PDeriv
import OAI.Combinatorics.Progressions.Linear.DualDerivativeRemoval
import OAI.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution
import OAI.Combinatorics.Progressions.Polynomial.NormalizedRealPolynomialChart

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

variable {σ : Type*}

noncomputable def dualScalarEval (t h : σ → ℚ) : MvPolynomial σ ℚ →ₐ[ℚ] DualNumber ℚ :=
  MvPolynomial.aeval (fun i => algebraMap ℚ (DualNumber ℚ) (t i) + h i • DualNumber.eps)

@[simp] theorem dualScalarEval_X (t h : σ → ℚ) (i : σ) :
    dualScalarEval t h (MvPolynomial.X i) =
      algebraMap ℚ (DualNumber ℚ) (t i) + h i • DualNumber.eps := by
  simp only [dualScalarEval, MvPolynomial.aeval_X]

@[simp] theorem dualScalarEval_fst (t h : σ → ℚ) (p : MvPolynomial σ ℚ) :
    (dualScalarEval t h p).fst = MvPolynomial.aeval t p := by
  have he : (TrivSqZeroExt.fstHom ℚ ℚ ℚ).comp (dualScalarEval t h) = MvPolynomial.aeval t := by
    ext i
    simp [dualScalarEval, TrivSqZeroExt.algebraMap_eq_inl]
  exact congrArg (fun f : MvPolynomial σ ℚ →ₐ[ℚ] ℚ => f p) he

theorem dualScalarEval_snd [Fintype σ] (t h : σ → ℚ) (p : MvPolynomial σ ℚ) :
    (dualScalarEval t h p).snd = ∑ i, h i * MvPolynomial.aeval t (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [dualScalarEval, TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq =>
    simp only [map_add, TrivSqZeroExt.snd_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, DualNumber.snd_mul, dualScalarEval_fst, dualScalarEval_X,
      TrivSqZeroExt.snd_add, DualNumber.fst_eps, DualNumber.snd_eps,
      Algebra.smul_def, hp, MvPolynomial.pderiv_mul, map_add, map_mul,
      MvPolynomial.aeval_X, mul_add, Finset.sum_add_distrib]
    simp [MvPolynomial.pderiv_X, Pi.single_apply, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]
    simp only [Finset.mul_sum, mul_left_comm]

namespace VectorPolynomial

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def dualEvalLie (t h : σ → ℚ) : VectorPolynomial σ ℚ L →ₗ⁅ℚ⁆ DualLieAlgebra L :=
  LieAlgebra.ExtendScalars.map (dualScalarEval t h) (LieHom.id : L →ₗ⁅ℚ⁆ L)

@[simp] theorem dualEvalLie_tmul (t h : σ → ℚ) (p : MvPolynomial σ ℚ) (x : L) :
    dualEvalLie t h (p ⊗ₜ[ℚ] x) = dualScalarEval t h p ⊗ₜ[ℚ] x := rfl

theorem dualEvalLie_base (t h : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    dualBaseLinear (dualEvalLie t h p) = eval t p := by
  induction p using TensorProduct.inductionOn with
  | tmul q x => rw [dualEvalLie_tmul, dualBaseLinear_tmul, dualScalarEval_fst, eval_tmul]
  | add p q hp hq => simp only [map_add, hp, hq]

noncomputable def directionalDerivative [Fintype σ] (h : σ → ℚ) :
    VectorPolynomial σ ℚ L →ₗ[ℚ] VectorPolynomial σ ℚ L :=
  ∑ i, h i • (MvPolynomial.pderiv i).toLinearMap.rTensor L

@[simp] theorem directionalDerivative_tmul [Fintype σ]
    (h : σ → ℚ) (p : MvPolynomial σ ℚ) (x : L) :
    directionalDerivative h (p ⊗ₜ[ℚ] x) =
      ∑ i, h i • (MvPolynomial.pderiv i p ⊗ₜ[ℚ] x) := by
  simp [directionalDerivative]

theorem dualEvalLie_tangent [Fintype σ] (t h : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    dualTangentLinear (dualEvalLie t h p) = eval t (directionalDerivative h p) := by
  induction p using TensorProduct.inductionOn with
  | tmul q x =>
    rw [dualEvalLie_tmul, dualTangentLinear_tmul, dualScalarEval_snd, directionalDerivative_tmul]
    simp only [Finset.sum_smul, map_sum, map_smul, eval_tmul, smul_smul]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem dualEvalLie_eq_value_add_derivative [Fintype σ] (t h : σ → ℚ)
    (p : VectorPolynomial σ ℚ L) :
    dualEvalLie t h p = dualConstantLie (eval t p) +
      dualInfinitesimal (eval t (directionalDerivative h p)) := by
  have he := dualLie_decomposition (dualEvalLie t h p)
  rwa [dualEvalLie_base, dualEvalLie_tangent] at he

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem pderiv_lie (i : σ) (p q : VectorPolynomial σ ℚ L) :
    (MvPolynomial.pderiv i).toLinearMap.rTensor L ⁅p, q⁆ =
      ⁅(MvPolynomial.pderiv i).toLinearMap.rTensor L p, q⁆ +
        ⁅p, (MvPolynomial.pderiv i).toLinearMap.rTensor L q⁆ := by
  induction p using TensorProduct.inductionOn with
  | tmul a x =>
    induction q using TensorProduct.inductionOn with
    | tmul b y =>
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, LinearMap.rTensor_tmul]
      change MvPolynomial.pderiv i (a * b) ⊗ₜ[ℚ] ⁅x, y⁆ =
        (MvPolynomial.pderiv i a * b) ⊗ₜ[ℚ] ⁅x, y⁆ +
          (a * MvPolynomial.pderiv i b) ⊗ₜ[ℚ] ⁅x, y⁆
      rw [MvPolynomial.pderiv_mul, TensorProduct.add_tmul]
    | add q r hq hr =>
      simp only [LieRing.lie_add, map_add, hq, hr]
      abel
  | add p r hp hr =>
    simp only [LieRing.add_lie, map_add, hp, hr]
    abel

theorem directionalDerivative_lie [Fintype σ] (h : σ → ℚ) (p q : VectorPolynomial σ ℚ L) :
    directionalDerivative h ⁅p, q⁆ =
      ⁅directionalDerivative h p, q⁆ + ⁅p, directionalDerivative h q⁆ := by
  simp only [directionalDerivative, LinearMap.sum_apply, LinearMap.smul_apply,
    pderiv_lie, smul_add, Finset.sum_add_distrib,
    sum_lie (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L),
    lie_sum (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L),
    smul_lie (R := ℚ) (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L),
    lie_smul (R := ℚ) (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L)]

theorem directionalDerivative_direction_add [Fintype σ]
    (h k : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    directionalDerivative (h + k) p = directionalDerivative h p + directionalDerivative k p := by
  simp only [directionalDerivative, Pi.add_apply, add_smul, Finset.sum_add_distrib,
    LinearMap.add_apply]

theorem directionalDerivative_direction_smul [Fintype σ]
    (r : ℚ) (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    directionalDerivative (r • h) p = r • directionalDerivative h p := by
  simp only [directionalDerivative, Pi.smul_apply, smul_eq_mul, mul_smul,
    ← Finset.smul_sum, LinearMap.smul_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

abbrev PolynomialGroup (σ : Type*) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :=
  NilpotentLieBCHGroup (VectorPolynomial σ ℚ L) s (VectorPolynomial.lowerCentralSeries_eq_bot hnil)

noncomputable def polynomialValueHom (t : σ → ℚ) :
    PolynomialGroup σ hnil →* NilpotentLieBCHGroup L s hnil :=
  NilpotentLieBCHGroup.map (evalLie t)

noncomputable def polynomialFirstJetHom (t h : σ → ℚ) : PolynomialGroup σ hnil →* DualGroup hnil :=
  NilpotentLieBCHGroup.map (dualEvalLie t h)

@[simp] theorem polynomialFirstJet_base (t h : σ → ℚ) (P : PolynomialGroup σ hnil) :
    dualBaseHom (polynomialFirstJetHom t h P) = polynomialValueHom t P := by
  apply ext
  exact dualEvalLie_base t h P.coord

theorem polynomialFirstJet_coord [Fintype σ] (t h : σ → ℚ) (P : PolynomialGroup σ hnil) :
    (polynomialFirstJetHom t h P).coord = dualConstantLie (eval t P.coord) +
      dualInfinitesimal (eval t (directionalDerivative h P.coord)) :=
  dualEvalLie_eq_value_add_derivative t h P.coord

noncomputable def polynomialLogDerivative (t h : σ → ℚ) (P : PolynomialGroup σ hnil) : L :=
  dualLogDerivative (polynomialFirstJetHom t h P)

theorem polynomialLogDerivative_mul (t h : σ → ℚ) (P Q : PolynomialGroup σ hnil) :
    polynomialLogDerivative t h (P * Q) = polynomialLogDerivative t h P +
      dualAdjoint (polynomialValueHom t P) (polynomialLogDerivative t h Q) := by
  simp only [polynomialLogDerivative, map_mul, dualLogDerivative_mul, polynomialFirstJet_base]

theorem polynomialLogDerivative_triple (t h : σ → ℚ) (A B D : PolynomialGroup σ hnil) :
    polynomialLogDerivative t h (A * B * D) =
      polynomialLogDerivative t h A + dualAdjoint (polynomialValueHom t A) (polynomialLogDerivative t h B) +
        dualAdjoint (polynomialValueHom t A * polynomialValueHom t B) (polynomialLogDerivative t h D) := by
  rw [polynomialLogDerivative_mul, polynomialLogDerivative_mul, map_mul]

theorem polynomialFirstJet_insertion_identity (t h : σ → ℚ) (P : PolynomialGroup σ hnil) (e m : L) :
    dualTangentElement (-e) * polynomialFirstJetHom t h P * dualTangentElement (-m) *
        (dualConstantHom (polynomialValueHom t P))⁻¹ =
      dualTangentElement (polynomialLogDerivative t h P - e - dualAdjoint (polynomialValueHom t P) m) := by
  simpa only [polynomialFirstJet_base, polynomialLogDerivative] using
    dualBCH_insertion_identity (polynomialFirstJetHom t h P) e m

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def formalPolynomialJetLie (i : σ) :
    VectorPolynomial σ ℚ L →ₗ⁅ℚ⁆ DualLieAlgebra (VectorPolynomial σ ℚ L) where
  toLinearMap := dualConstantLie.toLinearMap +
    dualInfinitesimal.comp ((MvPolynomial.pderiv i).toLinearMap.rTensor L)
  map_lie' {P Q} := by
    change dualConstantLie ⁅P, Q⁆ +
      dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L ⁅P, Q⁆) =
      ⁅dualConstantLie P + dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L P),
        dualConstantLie Q + dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L Q)⁆
    apply dual_ext
    · simp only [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal,
        add_zero, dualBaseLinear_lie]
    · simp only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal,
        zero_add, dualTangentLinear_lie, dualBaseLinear_constant,
        dualBaseLinear_infinitesimal, add_zero]
      rw [pderiv_lie]
      exact add_comm _ _

noncomputable def formalPolynomialJetHom (i : σ) :
    PolynomialGroup σ hnil →* DualGroup (VectorPolynomial.lowerCentralSeries_eq_bot (σ := σ) hnil) :=
  NilpotentLieBCHGroup.map (formalPolynomialJetLie i)

@[simp] theorem formalPolynomialJet_base (i : σ) (P : PolynomialGroup σ hnil) :
    dualBaseLinear (formalPolynomialJetHom i P).coord = P.coord := by
  change dualBaseLinear (dualConstantLie P.coord +
    dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord)) = _
  rw [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

@[simp] theorem formalPolynomialJet_tangent (i : σ) (P : PolynomialGroup σ hnil) :
    dualTangentLinear (formalPolynomialJetHom i P).coord =
      (MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord := by
  change dualTangentLinear (dualConstantLie P.coord +
    dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord)) = _
  rw [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]

@[simp] theorem formalPolynomialJet_baseHom (i : σ) (P : PolynomialGroup σ hnil) :
    dualBaseHom (formalPolynomialJetHom i P) = P :=
  NilpotentLieBCHGroup.ext (formalPolynomialJet_base i P)

noncomputable def formalLogDerivative (i : σ) (P : PolynomialGroup σ hnil) :
    VectorPolynomial σ ℚ L := dualLogDerivative (formalPolynomialJetHom i P)

theorem formalLogDerivative_mul (i : σ) (P Q : PolynomialGroup σ hnil) :
    formalLogDerivative i (P * Q) = formalLogDerivative i P +
      dualAdjoint P (formalLogDerivative i Q) := by
  simp only [formalLogDerivative, map_mul, dualLogDerivative_mul, formalPolynomialJet_baseHom]

@[simp] theorem formalLogDerivative_one (i : σ) :
    formalLogDerivative i (1 : PolynomialGroup σ hnil) = 0 := by
  simp only [formalLogDerivative, map_one, dualLogDerivative_one]

theorem formalLogDerivative_inv (i : σ) (P : PolynomialGroup σ hnil) :
    formalLogDerivative i P⁻¹ = -dualAdjoint P⁻¹ (formalLogDerivative i P) := by
  simp only [formalLogDerivative, map_inv, dualLogDerivative_inv, formalPolynomialJet_baseHom]

theorem formalLogDerivative_remove (i : σ) (A P B : PolynomialGroup σ hnil) :
    formalLogDerivative i (A⁻¹ * P * B⁻¹) =
      dualAdjoint A⁻¹ (formalLogDerivative i P - formalLogDerivative i A) -
        dualAdjoint (A⁻¹ * P * B⁻¹) (formalLogDerivative i B) := by
  have h := dualLogDerivative_remove
    (formalPolynomialJetHom i A) (formalPolynomialJetHom i P) (formalPolynomialJetHom i B)
  simpa only [map_mul, map_inv, formalPolynomialJet_baseHom, formalLogDerivative] using h

theorem formalLogDerivative_mem_of_invariant
    (U : LieSubalgebra ℚ (VectorPolynomial σ ℚ L))
    (V : Submodule ℚ (VectorPolynomial σ ℚ L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (i : σ) (P : PolynomialGroup σ hnil) (hP : P.coord ∈ U)
    (hD : (MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord ∈ V) :
    formalLogDerivative i P ∈ V := by
  apply dualLogDerivative_mem_of_invariant U V hUV (formalPolynomialJetHom i P)
  · simpa only [formalPolynomialJet_base] using hP
  · simpa only [formalPolynomialJet_tangent] using hD

def PolynomialDerivativeSystem (P : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L) : Prop :=
  ∀ i, formalLogDerivative i P = small i + dualAdjoint P (rational i) + extra i

theorem PolynomialDerivativeSystem.remove (P A B : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L)
    (hsystem : PolynomialDerivativeSystem P small rational extra) :
    PolynomialDerivativeSystem (A⁻¹ * P * B⁻¹)
      (fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A))
      (fun i => dualAdjoint B (rational i) - formalLogDerivative i B)
      (fun i => dualAdjoint A⁻¹ (extra i)) := by
  intro i
  have h := dualDerivativeSystem_remove
    (formalPolynomialJetHom i A) (formalPolynomialJetHom i P) (formalPolynomialJetHom i B)
    (small i) (rational i) (extra i) (by
      simpa only [formalPolynomialJet_baseHom, formalLogDerivative] using hsystem i)
  simpa only [map_mul, map_inv, formalPolynomialJet_baseHom, formalLogDerivative] using h

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realPolynomialValueHom (t : σ → ℝ) :
    PolynomialGroup σ hnil →* NilpotentLieBCHGroup L s hnil :=
  NilpotentLieBCHGroup.map (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t)

@[simp] theorem realPolynomialValueHom_coord (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    (realPolynomialValueHom t P).coord = eval₂ t P.coord := rfl

noncomputable def realPolynomialJet (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    DualGroup hnil :=
  ⟨dualConstantLie (eval₂ t P.coord) +
    dualInfinitesimal (eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord))⟩

@[simp] theorem realPolynomialJet_base (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    dualBaseLinear (realPolynomialJet i t P).coord = eval₂ t P.coord := by
  change dualBaseLinear (dualConstantLie _ + dualInfinitesimal _) = _
  rw [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

@[simp] theorem realPolynomialJet_tangent (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    dualTangentLinear (realPolynomialJet i t P).coord =
      eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord) := by
  change dualTangentLinear (dualConstantLie _ + dualInfinitesimal _) = _
  rw [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]

@[simp] theorem realPolynomialJet_baseHom (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    dualBaseHom (realPolynomialJet i t P) = realPolynomialValueHom t P :=
  NilpotentLieBCHGroup.ext (realPolynomialJet_base i t P)

theorem eval₂_formalLogDerivative (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    eval₂ t (formalLogDerivative i P) = dualLogDerivative (realPolynomialJet i t P) := by
  have h := dualLinearLift_logDerivative hnil ⊤ (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t)
    (eval₂ t) (fun a b _ => (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t).map_lie a b)
    (formalPolynomialJetHom i P) (by trivial)
  simp only [dualLinearLift_apply, formalPolynomialJet_base, formalPolynomialJet_tangent,
    eval₂Lie_apply] at h
  exact h

theorem eval₂_dualAdjoint (t : σ → ℝ) (P : PolynomialGroup σ hnil)
    (Q : VectorPolynomial σ ℚ L) :
    eval₂ t (dualAdjoint P Q) = dualAdjoint (realPolynomialValueHom t P) (eval₂ t Q) := by
  have h := map_dualAdjoint (hM := hnil) (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t) P Q
  simp only [eval₂Lie_apply] at h
  exact h

theorem PolynomialDerivativeSystem.real_evaluation (P : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L)
    (hsystem : PolynomialDerivativeSystem P small rational extra) (i : σ) (t : σ → ℝ) :
    dualLogDerivative (realPolynomialJet i t P) = eval₂ t (small i) +
      dualAdjoint (realPolynomialValueHom t P) (eval₂ t (rational i)) + eval₂ t (extra i) := by
  have h := congrArg (eval₂ t) (hsystem i)
  simpa only [eval₂_formalLogDerivative, map_add, eval₂_dualAdjoint] using h

theorem PolynomialDerivativeSystem.of_real_evaluation (P : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L)
    (hsystem : ∀ i (t : σ → ℝ), dualLogDerivative (realPolynomialJet i t P) =
      eval₂ t (small i) + dualAdjoint (realPolynomialValueHom t P) (eval₂ t (rational i)) +
        eval₂ t (extra i)) : PolynomialDerivativeSystem P small rational extra := by
  intro i
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro t
  simp only [map_sub, map_add, eval₂_formalLogDerivative, eval₂_dualAdjoint]
  exact sub_eq_zero.mpr (hsystem i t)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ τ υ V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V]
  [IsScalarTower ℚ ℝ V]

noncomputable def realCoefficientEquiv :
    VectorPolynomial σ ℚ V ≃ₗ[ℚ] VectorPolynomial σ ℝ V :=
  (coefficients (σ := σ) (R := ℚ) (V := V)).trans
    ((coefficients (σ := σ) (R := ℝ) (V := V)).restrictScalars ℚ).symm

@[simp] theorem coefficients_realCoefficientEquiv (p : VectorPolynomial σ ℚ V) :
    coefficients (realCoefficientEquiv p) = coefficients p := by
  simp [realCoefficientEquiv]

@[simp] theorem coefficients_realCoefficientEquiv_symm (p : VectorPolynomial σ ℝ V) :
    coefficients (realCoefficientEquiv.symm p) = coefficients p := by
  simp [realCoefficientEquiv]

@[simp] theorem realCoefficientEquiv_monomial (α : σ →₀ ℕ) (v : V) :
    realCoefficientEquiv (monomial (R := ℚ) α v) = monomial (R := ℝ) α v := by
  apply coefficients.injective
  simp

theorem eval_realCoefficientEquiv (x : σ → ℝ) (p : VectorPolynomial σ ℚ V) :
    eval x (realCoefficientEquiv p) = eval₂ x p := by
  classical
  rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, realCoefficientEquiv_monomial, eval_monomial, eval₂_monomial]

theorem eval₂_realCoefficientEquiv_symm (x : σ → ℝ) (p : VectorPolynomial σ ℝ V) :
    eval₂ x (realCoefficientEquiv.symm p) = eval x p := by
  obtain ⟨q, rfl⟩ := realCoefficientEquiv.surjective p
  rw [LinearEquiv.symm_apply_apply, eval_realCoefficientEquiv]

noncomputable def realChartSubstitute (f : σ → MvPolynomial τ ℝ) :
    VectorPolynomial σ ℚ V →ₗ[ℚ] VectorPolynomial τ ℚ V :=
  realCoefficientEquiv.symm.toLinearMap.comp
    (((substitute f).restrictScalars ℚ).comp realCoefficientEquiv.toLinearMap)

theorem coefficients_realChartSubstitute (f : σ → MvPolynomial τ ℝ)
    (p : VectorPolynomial σ ℚ V) (α : τ →₀ ℕ) :
    coefficients (realChartSubstitute f p) α =
      ∑ β ∈ (coefficients p).support,
        (MvPolynomial.aeval f (MvPolynomial.monomial β (1 : ℝ))).coeff α •
          coefficients p β := by
  simp only [realChartSubstitute, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply, coefficients_realCoefficientEquiv_symm,
    coefficients_substitute, coefficients_realCoefficientEquiv]

theorem eval₂_realChartSubstitute (f : σ → MvPolynomial τ ℝ)
    (x : τ → ℝ) (p : VectorPolynomial σ ℚ V) :
    eval₂ x (realChartSubstitute f p) =
      eval₂ (fun i => MvPolynomial.eval x (f i)) p := by
  simp only [realChartSubstitute, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply, eval₂_realCoefficientEquiv_symm,
    eval_substitute, MvPolynomial.aeval_eq_eval, eval_realCoefficientEquiv]

theorem realChartSubstitute_comp (f : σ → MvPolynomial τ ℝ)
    (g : τ → MvPolynomial υ ℝ) (p : VectorPolynomial σ ℚ V) :
    realChartSubstitute g (realChartSubstitute f p) =
      realChartSubstitute (fun i => MvPolynomial.aeval g (f i)) p := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro x
  rw [map_sub, eval₂_realChartSubstitute, eval₂_realChartSubstitute,
    eval₂_realChartSubstitute]
  apply sub_eq_zero.mpr
  congr 2
  funext i
  change MvPolynomial.aeval (fun j => MvPolynomial.eval x (g j)) (f i) =
    MvPolynomial.aeval x (MvPolynomial.aeval g (f i))
  rw [MvPolynomial.comp_aeval_apply]
  rfl

theorem realChartSubstitute_X (p : VectorPolynomial σ ℚ V) :
    realChartSubstitute (fun i => MvPolynomial.X i) p = p := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro x
  simp only [map_sub, eval₂_realChartSubstitute, MvPolynomial.eval_X, sub_self]

theorem eval₂_normalizedRealPolynomialChart {U B : Type*}
    (H : U → ℝ) (A : B → MvPolynomial U ℝ)
    (u : U → ℝ) (b : B → ℝ) (p : VectorPolynomial (U ⊕ B) ℚ V) :
    eval₂ (Sum.elim u b) (realChartSubstitute (normalizedRealPolynomialChart H A) p) =
      eval₂ (Sum.elim (fun i => u i / H i) (fun j => b j - MvPolynomial.eval u (A j))) p := by
  rw [eval₂_realChartSubstitute]
  simp only [normalizedRealPolynomialChart_eval]

end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]

theorem realChartSubstitute_lie (f : σ → MvPolynomial τ ℝ)
    (p q : VectorPolynomial σ ℚ L) :
    realChartSubstitute f ⁅p, q⁆ = ⁅realChartSubstitute f p, realChartSubstitute f q⁆ := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro x
  rw [map_sub]
  apply sub_eq_zero.mpr
  rw [eval₂_realChartSubstitute]
  change eval₂Lie (R := ℚ) (fun i => MvPolynomial.eval x (f i)) ⁅p, q⁆ =
    eval₂Lie (R := ℚ) x ⁅realChartSubstitute f p, realChartSubstitute f q⁆
  rw [LieHom.map_lie, LieHom.map_lie]
  simp only [eval₂Lie_apply, eval₂_realChartSubstitute]

attribute [local irreducible] realChartSubstitute

private def lieHomOfLinearMap {A B : Type*} [LieRing A] [LieAlgebra ℚ A]
    [LieRing B] [LieAlgebra ℚ B] (g : A →ₗ[ℚ] B)
    (hg : ∀ x y, g ⁅x, y⁆ = ⁅g x, g y⁆) : A →ₗ⁅ℚ⁆ B :=
  ⟨g, fun {x y} => hg x y⟩

noncomputable def realChartSubstituteLie (f : σ → MvPolynomial τ ℝ) :
    VectorPolynomial σ ℚ L →ₗ⁅ℚ⁆ VectorPolynomial τ ℚ L :=
  lieHomOfLinearMap (realChartSubstitute f) (realChartSubstitute_lie f)

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ}
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def realPolynomialChartSubstitution (f : σ → MvPolynomial τ ℝ) :
    PolynomialGroup σ hnil →* PolynomialGroup τ hnil :=
  NilpotentLieBCHGroup.map (realChartSubstituteLie f)

@[simp] theorem realPolynomialChartSubstitution_coord (f : σ → MvPolynomial τ ℝ)
    (p : PolynomialGroup σ hnil) :
    (realPolynomialChartSubstitution hnil f p).coord = realChartSubstitute f p.coord := rfl

theorem realPolynomialChartSubstitution_mul (f : σ → MvPolynomial τ ℝ)
    (p q : PolynomialGroup σ hnil) :
    realPolynomialChartSubstitution hnil f (p * q) =
      realPolynomialChartSubstitution hnil f p * realPolynomialChartSubstitution hnil f q :=
  map_mul _ _ _

theorem realPolynomialChartSubstitution_list_prod (f : σ → MvPolynomial τ ℝ)
    (p : List (PolynomialGroup σ hnil)) :
    realPolynomialChartSubstitution hnil f p.prod =
      (p.map (realPolynomialChartSubstitution hnil f)).prod :=
  by apply map_list_prod

theorem realPolynomialChartSubstitution_foldl (f : σ → MvPolynomial τ ℝ)
    (p : List (PolynomialGroup σ hnil)) (E : PolynomialGroup σ hnil) :
    realPolynomialChartSubstitution hnil f (p.foldl (· * ·) E) =
      (p.map (realPolynomialChartSubstitution hnil f)).foldl (· * ·)
        (realPolynomialChartSubstitution hnil f E) := by
  induction p generalizing E with
  | nil => simp only [List.foldl_nil, List.map_nil]
  | cons a p ih =>
    simp only [List.foldl_cons, List.map_cons]
    simpa only [map_mul] using ih (E * a)

theorem realPolynomialChartSubstitution_value (f : σ → MvPolynomial τ ℝ)
    (x : τ → ℝ) (p : PolynomialGroup σ hnil) :
    realPolynomialValueHom x (realPolynomialChartSubstitution hnil f p) =
      realPolynomialValueHom (fun i => MvPolynomial.eval x (f i)) p := by
  apply NilpotentLieBCHGroup.ext
  exact eval₂_realChartSubstitute f x p.coord

end Erdos3.NilpotentLieBCHGroup

end

end OAI
