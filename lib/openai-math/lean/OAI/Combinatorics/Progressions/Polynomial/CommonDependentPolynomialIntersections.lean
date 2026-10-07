import OAI.Combinatorics.Progressions.Estimates.MarkedShiftGeneratorBounds

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {σ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def dependentPolynomialLayer (d k l : ℕ) :
    Submodule ℚ (VectorPolynomial σ ℚ D.CoefficientFreeLieAlgebra) :=
  markedPolynomialLayer D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent d k l

theorem coefficientFreeSpan_le_dependentWordLayer (d : Fin s) :
    D.coefficientFreeSpan d ≤ D.dependentWordLayer (d.val + 1) 0 1 :=
  sup_le (D.commonFreeSpan_le_dependentWordLayer d)
    ((D.dependentFreeSpan_le_dependentWordLayer d).trans
      (D.dependentWordLayer_antitone le_rfl (Nat.zero_le 1) le_rfl))

theorem dependentAffinePolynomial_mem [Fintype σ] (d : Fin s)
    {x : D.CoefficientFreeLieAlgebra} {y : σ → D.CoefficientFreeLieAlgebra}
    (hx : x ∈ D.coefficientFreeSpan d) (hy : ∀ i, y i ∈ D.dependentFreeSpan d) :
    markedAffinePolynomial x y ∈ D.dependentPolynomialLayer (d.val + 1) 0 1 :=
  markedAffinePolynomial_mem D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
    (D.coefficientFreeSpan_le_dependentWordLayer d hx)
    (fun i => D.dependentFreeSpan_le_dependentWordLayer d (hy i))

noncomputable def dependentShiftAlgebra (t : ℕ) :
    LieSubalgebra ℚ (D.coefficientFreeFiltration.associatedDegree.PolynomialShiftAlgebra t) :=
  markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t

variable {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.dependentPolynomial_top_frequency_zero
    {p : VectorPolynomial σ ℚ D.CoefficientFreeLieAlgebra}
    (hp : p ∈ D.dependentPolynomialLayer s 2 r) (t : σ → ℚ) :
    B.freeFrequency D (eval t p) = 0 :=
  markedPolynomialLayer_eval_frequency_zero D.coefficientFreeGenerator D.coefficientWeight
    D.coefficientIsDependent (B.freeFrequency D) (B.dependentWordLayer_top_le_ker D) hp t

theorem CoefficientBases.real_dependentPolynomial_top_frequency_zero
    (t : σ → ℚ) (x : ℝ ⊗[ℚ] VectorPolynomial σ ℚ D.CoefficientFreeLieAlgebra)
    (hx : x ∈ (D.dependentPolynomialLayer s 2 r).baseChange ℝ) :
    realifyFunctional ((B.freeFrequency D).comp (eval t)) x = 0 := by
  apply (mem_realified_frequency_kernel_iff ((B.freeFrequency D).comp (eval t)) x).mp
  apply Submodule.baseChange_mono ℝ _ hx
  intro p hp
  exact B.dependentPolynomial_top_frequency_zero D hp t

theorem CoefficientBases.dependentPolynomial_bracket_frequency_zero
    {d e l n : ℕ} (hde : d + e = s) (hln : l + n = r)
    {p q : VectorPolynomial σ ℚ D.CoefficientFreeLieAlgebra}
    (hp : p ∈ D.dependentPolynomialLayer d 1 l)
    (hq : q ∈ D.dependentPolynomialLayer e 1 n) (t : σ → ℚ) :
    B.freeFrequency D (eval t ⁅p, q⁆) = 0 := by
  apply B.dependentPolynomial_top_frequency_zero D _ t
  change ⁅p, q⁆ ∈ markedPolynomialLayer D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent s 2 r
  have h := markedPolynomialLayer_lie_mem D.coefficientFreeGenerator D.coefficientWeight
    D.coefficientIsDependent hp hq
  simpa only [hde, hln] using h

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {σ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem dependentPolynomialLayer_inf (d k l e m n : ℕ) :
    D.dependentPolynomialLayer (σ := σ) d k l ⊓ D.dependentPolynomialLayer e m n =
      D.dependentPolynomialLayer (max d e) (max k m) (max l n) := by
  ext p
  constructor
  · intro hp α
    let a := Finsupp.weight (fun _ : σ => 1) α
    have h : coefficients p α ∈ D.dependentWordLayer d (k + a) l ⊓
        D.dependentWordLayer e (m + a) n := ⟨hp.1 α, hp.2 α⟩
    rw [D.dependentWordLayer_inf] at h
    have he : max (k + a) (m + a) = max k m + a := by omega
    rw [he] at h
    exact h
  · intro hp
    constructor
    · intro α
      exact D.dependentWordLayer_antitone (Nat.le_max_left _ _)
        (Nat.add_le_add_right (Nat.le_max_left _ _) _) (Nat.le_max_left _ _) (hp α)
    · intro α
      exact D.dependentWordLayer_antitone (Nat.le_max_right _ _)
        (Nat.add_le_add_right (Nat.le_max_right _ _) _) (Nat.le_max_right _ _) (hp α)

theorem dependentPolynomialLayer_top_inter :
    D.dependentPolynomialLayer (σ := σ) s 1 r ⊓ D.dependentPolynomialLayer 0 2 0 =
      D.dependentPolynomialLayer s 2 r := by
  rw [D.dependentPolynomialLayer_inf]
  simp only [Nat.max_zero, show max 1 2 = 2 from rfl]

variable {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.dependentPolynomial_top_inter_le_ker (t : σ → ℚ) :
    D.dependentPolynomialLayer s 1 r ⊓ D.dependentPolynomialLayer 0 2 0 ≤
      ((B.freeFrequency D).comp (eval t)).ker := by
  rw [D.dependentPolynomialLayer_top_inter]
  intro p hp
  exact B.dependentPolynomial_top_frequency_zero D hp t

theorem CoefficientBases.exists_dependent_polynomial_quotient_frequency (t : σ → ℚ) :
    ∃ ξ : (VectorPolynomial σ ℚ D.CoefficientFreeLieAlgebra ⧸
        D.dependentPolynomialLayer 0 2 0) →ₗ[ℚ] ℚ,
      ∀ p ∈ D.dependentPolynomialLayer s 1 r,
        ξ ((D.dependentPolynomialLayer 0 2 0).mkQ p) = B.freeFrequency D (eval t p) :=
  exists_quotient_functional_preserving_subspace (D.dependentPolynomialLayer s 1 r)
    (D.dependentPolynomialLayer 0 2 0) ((B.freeFrequency D).comp (eval t))
    (B.dependentPolynomial_top_inter_le_ker D t)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
