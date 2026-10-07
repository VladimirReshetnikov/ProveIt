import OAI.Combinatorics.Progressions.Geometry.MultidegreeOrbitTransport
import OAI.Combinatorics.Progressions.Lattices.CommonAffineOrbitEvaluation

namespace OAI


namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N)

noncomputable def localAffineMarkedBase (j : Fin s) : (D.coefficientFreeSpan j).baseChange ℝ :=
  ⟨(x j).val + ∑ i, (-(h₀.val : ℝ) * u i - c i) • (y j i).val,
    Submodule.add_mem _ (x j).property (Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.baseChange_mono ℝ
        (D.dependentFreeSpan_le_coefficientFreeSpan j) (y j i).property)))⟩

noncomputable def localAffineMarkedOrbit :
    (D.markedQuotientMultidegree t).realification.PolynomialOrbit :=
  D.commonAffineMarkedOrbit t (D.localAffineMarkedBase t x y u c h₀) y u

noncomputable def localAffineMarkedLift (h : ZMod N) (n : ℤ) :
    ℝ ⊗[ℚ] markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t :=
  D.commonAffineMarkedLift t (D.localAffineMarkedBase t x y u c h₀) y u h.val n

theorem localAffineMarkedOrbit_eval (h : ZMod N) (n : ℤ) :
    ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localAffineMarkedOrbit t x y u c h₀)).coord =
        (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
            (D.localAffineMarkedLift t x y u c h₀ h n) :=
  D.commonAffineMarkedOrbit_eval t (D.localAffineMarkedBase t x y u c h₀) y u h.val n

theorem localAffineMarkedOrbit_at_zero (h : ℤ) :
    (D.markedQuotientMultidegree t).realification.polynomialOrbitEval (correlationInput h 0)
      (D.localAffineMarkedOrbit t x y u c h₀) = 1 :=
  D.commonAffineMarkedOrbit_at_zero t (D.localAffineMarkedBase t x y u c h₀) y u h

theorem localAffineMarkedLift_eval (h : ZMod N) (n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t
        (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ))).baseChange ℝ
          (D.localAffineMarkedLift t x y u c h₀ h n) =
            ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
              ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) := by
  apply (D.commonAffineMarkedLift_eval t (D.localAffineMarkedBase t x y u c h₀) y u
    (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ)) h.val n).trans
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra => (n : ℚ) ^ (j.val + 1) • z)
  change ((x j).val + ∑ i, (-(h₀.val : ℝ) * u i - c i) • (y j i).val) + _ = _
  rw [add_assoc, ← Finset.sum_add_distrib]
  apply congrArg ((x j).val + ·)
  apply Finset.sum_congr rfl
  intro i _
  rw [← add_smul]
  apply congrArg (fun a : ℝ => a • (y j i).val)
  simpa only [Int.cast_natCast, add_assoc] using affineCyclicTorusCarry_identity u c h₀ h i

theorem localAffineMarkedLift_eq_polynomial_eval
    (A : ZMod N → VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra))
    (h : ZMod N) (hA : A h = positiveUnivariate (fun j =>
      (x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val)) (n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t
        (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ))).baseChange ℝ
          (D.localAffineMarkedLift t x y u c h₀ h n) = eval (fun _ => (n : ℚ)) (A h) := by
  rw [D.localAffineMarkedLift_eval, hA]
  simp only [positiveUnivariate, map_sum, eval_monomial, Finsupp.prod_single_index, pow_zero]

end Erdos3.NativeRankRelation.CommonData


namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N)

noncomputable def localAffineConjugatedLift (h : ZMod N) (n : ℤ) :
    ℝ ⊗[ℚ] markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t :=
  (markedShiftTranslate D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ))).baseChange ℝ
      (D.localAffineMarkedLift t x y u c h₀ h n)

noncomputable def localAffineCorrectingElement (h : ZMod N) :
    (D.markedQuotientMultidegree t).realification.Group :=
  ⟨realMarkedDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ))⟩

theorem localAffineConjugatedLift_eval (h : ZMod N) (n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t 0).baseChange ℝ
        (D.localAffineConjugatedLift t x y u c h₀ h n) =
          ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
            ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) := by
  have he := realMarkedShiftEval_translate D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ)) 0
    (D.localAffineMarkedLift t x y u c h₀ h n)
  rw [zero_add] at he
  exact he.trans (D.localAffineMarkedLift_eval t x y u c h₀ h n)

theorem localAffineMarkedOrbit_conjugation (hs : 1 ≤ s) (h : ZMod N) (n : ℤ) :
    (D.localAffineCorrectingElement t u c h₀ h *
      (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
        (correlationInput (h.val : ℤ) n) (D.localAffineMarkedOrbit t x y u c h₀) *
      (D.localAffineCorrectingElement t u c h₀ h)⁻¹).coord =
        (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
            (D.localAffineConjugatedLift t x y u c h₀ h n) := by
  change conjugationCoord (D.localAffineCorrectingElement t u c h₀ h)
    (((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localAffineMarkedOrbit t x y u c h₀)).coord) = _
  exact (congrArg (conjugationCoord (D.localAffineCorrectingElement t u c h₀ h))
    (D.localAffineMarkedOrbit_eval t x y u c h₀ h n)).trans
      (realMarkedTranslate_conjugation_lift D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t hs
        (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ)) (D.localAffineMarkedLift t x y u c h₀ h n))

theorem localAffineConjugatedLift_eq_polynomial_eval
    (A : ZMod N → VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra))
    (h : ZMod N) (hA : A h = positiveUnivariate (fun j =>
      (x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val)) (n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t 0).baseChange ℝ
        (D.localAffineConjugatedLift t x y u c h₀ h n) = eval (fun _ => (n : ℚ)) (A h) := by
  rw [D.localAffineConjugatedLift_eval, hA]
  simp only [positiveUnivariate, map_sum, eval_monomial, Finsupp.prod_single_index, pow_zero]

end Erdos3.NativeRankRelation.CommonData


namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)

noncomputable def scaledLocalAffineMarkedOrbit :
    (D.markedQuotientMultidegree t).realification.PolynomialOrbit :=
  D.commonAffineMarkedOrbit t (D.localAffineMarkedBase t x y u c h₀)
    (fun j i => (m : ℝ)⁻¹ • y j i) (fun i => (m : ℝ) * u i)

noncomputable def scaledLocalAffineMarkedLift (h : ZMod N) (n : ℤ) :
    ℝ ⊗[ℚ] markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t :=
  D.commonAffineMarkedLift t (D.localAffineMarkedBase t x y u c h₀)
    (fun j i => (m : ℝ)⁻¹ • y j i) (fun i => (m : ℝ) * u i) h.val n

theorem scaledLocalAffineMarkedOrbit_eval (h : ZMod N) (n : ℤ) :
    ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.scaledLocalAffineMarkedOrbit t x y u c h₀ m)).coord =
        (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
            (D.scaledLocalAffineMarkedLift t x y u c h₀ m h n) :=
  D.commonAffineMarkedOrbit_eval t (D.localAffineMarkedBase t x y u c h₀)
    (fun j i => (m : ℝ)⁻¹ • y j i) (fun i => (m : ℝ) * u i) h.val n

theorem scaledLocalAffineMarkedOrbit_at_zero (h : ℤ) :
    (D.markedQuotientMultidegree t).realification.polynomialOrbitEval (correlationInput h 0)
      (D.scaledLocalAffineMarkedOrbit t x y u c h₀ m) = 1 :=
  D.commonAffineMarkedOrbit_at_zero t (D.localAffineMarkedBase t x y u c h₀)
    (fun j i => (m : ℝ)⁻¹ • y j i) (fun i => (m : ℝ) * u i) h

theorem scaledLocalAffineMarkedLift_eval (hm : 0 < m) (h : ZMod N) (n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t
        ((m : ℚ) • fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ))).baseChange ℝ
          (D.scaledLocalAffineMarkedLift t x y u c h₀ m h n) =
            ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
              ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  let a : Fin t → ℚ := (m : ℚ) • fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ)
  apply (D.commonAffineMarkedLift_eval t (D.localAffineMarkedBase t x y u c h₀)
    (fun j i => (m : ℝ)⁻¹ • y j i) (fun i => (m : ℝ) * u i)
    ((m : ℚ) • fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ)) h.val n).trans
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra => (n : ℚ) ^ (j.val + 1) • z)
  change ((x j).val + ∑ i, (-(h₀.val : ℝ) * u i - c i) • (y j i).val) +
    (∑ i, ((a i : ℝ) + (h.val : ℝ) * ((m : ℝ) * u i)) •
      ((m : ℝ)⁻¹ • (y j i).val)) = _
  rw [add_assoc, ← Finset.sum_add_distrib]
  apply congrArg ((x j).val + ·)
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, ← add_smul]
  apply congrArg (fun a : ℝ => a • (y j i).val)
  have hscale : (((a i : ℝ) + (h.val : ℝ) * ((m : ℝ) * u i)) * (m : ℝ)⁻¹) =
      ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ) + (h.val : ℝ) * u i := by
    dsimp only [a, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp [hm0]
  rw [hscale]
  simpa only [add_assoc] using affineCyclicTorusCarry_identity u c h₀ h i

end Erdos3.NativeRankRelation.CommonData


namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)

noncomputable def scaledLocalAffineConjugatedLift (h : ZMod N) (n : ℤ) :
    ℝ ⊗[ℚ] markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t :=
  (markedShiftTranslate D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t ((m : ℚ) • fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ))).baseChange ℝ
      (D.scaledLocalAffineMarkedLift t x y u c h₀ m h n)

noncomputable def scaledLocalAffineCorrectingElement (h : ZMod N) :
    (D.markedQuotientMultidegree t).realification.Group :=
  ⟨realMarkedDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t ((m : ℚ) • fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ))⟩

theorem scaledLocalAffineConjugatedLift_eval (hm : 0 < m) (h : ZMod N) (n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t 0).baseChange ℝ
        (D.scaledLocalAffineConjugatedLift t x y u c h₀ m h n) =
          ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
            ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) := by
  have he := realMarkedShiftEval_translate D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t ((m : ℚ) • fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ)) 0
    (D.scaledLocalAffineMarkedLift t x y u c h₀ m h n)
  rw [zero_add] at he
  exact he.trans (D.scaledLocalAffineMarkedLift_eval t x y u c h₀ m hm h n)

theorem scaledLocalAffineMarkedOrbit_conjugation (hs : 1 ≤ s) (h : ZMod N) (n : ℤ) :
    (D.scaledLocalAffineCorrectingElement t u c h₀ m h *
      (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
        (correlationInput (h.val : ℤ) n) (D.scaledLocalAffineMarkedOrbit t x y u c h₀ m) *
      (D.scaledLocalAffineCorrectingElement t u c h₀ m h)⁻¹).coord =
        (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
            (D.scaledLocalAffineConjugatedLift t x y u c h₀ m h n) := by
  change conjugationCoord (D.scaledLocalAffineCorrectingElement t u c h₀ m h)
    (((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.scaledLocalAffineMarkedOrbit t x y u c h₀ m)).coord) = _
  exact (congrArg (conjugationCoord (D.scaledLocalAffineCorrectingElement t u c h₀ m h))
    (D.scaledLocalAffineMarkedOrbit_eval t x y u c h₀ m h n)).trans
      (realMarkedTranslate_conjugation_lift D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t hs
        ((m : ℚ) • fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ)) (D.scaledLocalAffineMarkedLift t x y u c h₀ m h n))

theorem scaledLocalAffineConjugatedLift_eq_polynomial_eval (hm : 0 < m)
    (A : ZMod N → VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra))
    (h : ZMod N) (hA : A h = positiveUnivariate (fun j =>
      (x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val)) (n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t 0).baseChange ℝ
        (D.scaledLocalAffineConjugatedLift t x y u c h₀ m h n) = eval (fun _ => (n : ℚ)) (A h) := by
  rw [D.scaledLocalAffineConjugatedLift_eval t x y u c h₀ m hm, hA]
  simp only [positiveUnivariate, map_sum, eval_monomial, Finsupp.prod_single_index, pow_zero]

end Erdos3.NativeRankRelation.CommonData


namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) {d : ℕ}
  (E : RationalFilteredNilmanifold
    (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
  (T : E.MultidegreeStructure (mixedCorrelationDegree s))
  (hT : T.filtration = D.markedQuotientMultidegree t)

variable [TopologicalSpace (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
  D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]
  [T2Space (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]

include hT in
theorem exists_scaled_marked_nilcharacter {B : ℝ} (hB : T.ComplexityLE B) {k : ℕ}
    (V : E.UnitVerticalObservable (E.filtration.realification.subgroup (s + 1)) (Fin k) B)
    (hk : (k : ℝ) ≤ Real.exp B)
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) :
    ∃ A : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) B,
      ∃ e : Fin k ≃ Fin A.outputDim, A.dim = d ∧
        ∀ i (h n : ℤ), A.eval (e i) (correlationInput h n) =
          V.observable i (QuotientGroup.mk
            ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval (correlationInput h n)
              (D.scaledLocalAffineMarkedOrbit t x y u c h₀ m))) := by
  let F := (D.markedQuotientMultidegree t).realification
  have hF : F = T.filtration.realification := congrArg MultidegreeLieFiltration.realification hT.symm
  let g := F.orbitEquivOfEq hF (D.scaledLocalAffineMarkedOrbit t x y u c h₀ m)
  classical
  let result := NativeMultidegreeNilcharacter.exists_of_unit_data E T
    (mixedCorrelationDegree_sum s).symm hB g V (by simpa only [Fintype.card_fin] using hk)
  let A := result.choose
  let equivalence := result.choose_spec
  let e := equivalence.choose
  have hdim := equivalence.choose_spec.1
  have heval := equivalence.choose_spec.2
  refine ⟨A, e, hdim, ?_⟩
  intro i h n
  exact (heval i (correlationInput h n)).trans (congrArg (fun z : E.RealGroup =>
    V.observable i (QuotientGroup.mk z)) (F.orbitEquivOfEq_eval hF
      (D.scaledLocalAffineMarkedOrbit t x y u c h₀ m) (correlationInput h n)))

end Erdos3.NativeRankRelation.CommonData

end OAI
