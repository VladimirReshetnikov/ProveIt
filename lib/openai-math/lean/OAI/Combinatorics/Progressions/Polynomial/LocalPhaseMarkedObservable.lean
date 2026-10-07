/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.MarkedParameterOrbit
import OAI.Combinatorics.Progressions.Estimates.MarkedUnitOrbit
import OAI.Combinatorics.Progressions.Fourier.MarkedRealFrequencyCompatibility
import OAI.Combinatorics.Progressions.Lattices.RealMarkedAffineShift

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

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
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)

noncomputable def localPhaseMarkedOrbit :
    (D.markedQuotientMultidegree t).realification.PolynomialOrbit :=
  Mul.mul (α := (D.markedQuotientMultidegree t).realification.PolynomialOrbit)
    (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0)
    (realMarkedParameterOrbit D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t
        (fun i => (m : ℝ) * ((h₀.val : ℝ) * u i + c i)) (fun i => -(m : ℝ) * u i) :
      (D.markedQuotientMultidegree t).realification.PolynomialOrbit)

noncomputable def localPhaseMarkedSmallElement (h : ZMod N) :
    (D.markedQuotientMultidegree t).realification.Group :=
  realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t
      (fun i => -(m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i)

theorem localPhaseMarkedOrbit_eval (h : ZMod N) (n : ℤ) :
    (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m) =
        (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
          (correlationInput (h.val : ℤ) n)
          (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0) *
        realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
          D.coefficientFreeGenerator_mem_layer t
            (fun i => -(m : ℝ) * (((h.val : ℝ) - h₀.val) * u i - c i)) := by
  let E := (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
    (correlationInput (h.val : ℤ) n)
  let g := D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0
  let a₀ : Fin t → ℝ := fun i => (m : ℝ) * ((h₀.val : ℝ) * u i + c i)
  let a₁ : Fin t → ℝ := fun i => -(m : ℝ) * u i
  let phase : (D.markedQuotientMultidegree t).realification.PolynomialOrbit :=
    realMarkedParameterOrbit D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t a₀ a₁
  have hm : E (D.localPhaseMarkedOrbit t x y u c h₀ m) = E g * E phase := E.map_mul g phase
  apply hm.trans
  apply congrArg (fun z : (D.markedQuotientMultidegree t).realification.Group => E g * z)
  apply (realMarkedParameterOrbit_eval D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t a₀ a₁ (h.val : ℤ) n).trans
  apply congrArg (realMarkedParameterElement D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
    D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t)
  funext i
  simp only [a₀, a₁, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_natCast]
  ring

theorem scaledLocalAffineCorrectingElement_eq_parameter (h : ZMod N) :
    D.scaledLocalAffineCorrectingElement t u c h₀ m h =
      realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t
          (fun i => -(m : ℝ) * (affineCyclicTorusCarry u c h₀ h i : ℝ)) := by
  apply NilpotentLieBCHGroup.ext
  have he := realMarkedParameterDirection_rat D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t
      ((m : ℚ) • fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ))
  change realMarkedDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t _ =
      realMarkedParameterDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t _
  simpa only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, Rat.cast_neg, Rat.cast_natCast,
    Rat.cast_intCast, Int.cast_neg, mul_neg, neg_mul] using he.symm

theorem localPhaseMarkedOrbit_right_normalization (h : ZMod N) (n : ℤ) :
    (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m) *
        (D.scaledLocalAffineCorrectingElement t u c h₀ m h)⁻¹ =
      (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
        (correlationInput (h.val : ℤ) n)
        (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0) *
          D.localPhaseMarkedSmallElement t u c h₀ m h := by
  let par : (Fin t → ℝ) → (D.markedQuotientMultidegree t).realification.Group :=
    realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t
  let a : Fin t → ℝ := fun i => -(m : ℝ) * (((h.val : ℝ) - h₀.val) * u i - c i)
  let b : Fin t → ℝ := fun i => -(m : ℝ) * (affineCyclicTorusCarry u c h₀ h i : ℝ)
  let g := (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
    (correlationInput (h.val : ℤ) n)
    (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0)
  have hi : (par b)⁻¹ = par (-b) :=
    realMarkedParameterElement_inv D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t b
  have hab : par a * par (-b) = D.localPhaseMarkedSmallElement t u c h₀ m h := by
    apply (realMarkedParameterElement_mul D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t a (-b)).trans
    apply congrArg par
    funext i
    simp only [a, b, Pi.add_apply, Pi.neg_apply, affineCyclicTorusLocalLift_eq_sub_carry]
    ring
  calc
    _ = (g * par a) * (par b)⁻¹ :=
      congrArg₂ (fun z w : (D.markedQuotientMultidegree t).realification.Group => z * w⁻¹)
        (D.localPhaseMarkedOrbit_eval t x y u c h₀ m h n)
        (D.scaledLocalAffineCorrectingElement_eq_parameter t u c h₀ m h)
    _ = (g * par a) * par (-b) := congrArg (fun z => (g * par a) * z) hi
    _ = g * (par a * par (-b)) := mul_assoc _ _ _
    _ = _ := congrArg (g * ·) hab

theorem localPhaseMarkedOrbit_quotient
    (Γ : Subgroup (D.markedQuotientMultidegree t).realification.Group)
    (h : ZMod N) (hΓ : D.scaledLocalAffineCorrectingElement t u c h₀ m h ∈ Γ) (n : ℤ) :
    (QuotientGroup.mk ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m)) :
        (D.markedQuotientMultidegree t).realification.Group ⧸ Γ) =
      QuotientGroup.mk ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
        (correlationInput (h.val : ℤ) n)
        (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0) *
          D.localPhaseMarkedSmallElement t u c h₀ m h) := by
  calc
    _ = QuotientGroup.mk ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
        (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m) *
          (D.scaledLocalAffineCorrectingElement t u c h₀ m h)⁻¹) :=
      (quotient_mk_mul_mem Γ _ ⟨_, Γ.inv_mem hΓ⟩).symm
    _ = _ := congrArg QuotientGroup.mk (D.localPhaseMarkedOrbit_right_normalization t x y u c h₀ m h n)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ) (e : Basis (Fin d) ℚ (MarkedShiftQuotient F v w marked t))

theorem realMarkedParameterDirection_coordinate (a : Fin t → ℝ) (j : Fin d) :
    (e.baseChange ℝ).repr (realMarkedParameterDirection F v w marked t a) j =
      ∑ i, a i * (e.repr (markedQuotientDirection F v w marked t (Pi.single i 1)) j : ℝ) := by
  apply (congrArg (fun z => (e.baseChange ℝ).repr z j)
    (realMarkedParameterDirection_apply F v w marked t a)).trans
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    realMarkedDirection, rationalLieInclusion_coordinates]

theorem realMarkedParameterDirection_coordinate_le (a : Fin t → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (ha : ∀ i, |a i| ≤ A)
    (he : ∀ i j, |(e.repr (markedQuotientDirection F v w marked t (Pi.single i 1)) j : ℝ)| ≤ B)
    (j : Fin d) :
    |(e.baseChange ℝ).repr (realMarkedParameterDirection F v w marked t a) j| ≤ (t : ℝ) * A * B := by
  rw [realMarkedParameterDirection_coordinate]
  calc
    _ ≤ ∑ i, |a i * (e.repr (markedQuotientDirection F v w marked t (Pi.single i 1)) j : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin t, A * B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (ha i) (he i j) (abs_nonneg _) hA
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem realMarkedParameterDirection_coordinateL2Norm_le (a : Fin t → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : ∀ i, |a i| ≤ A)
    (he : ∀ i j, |(e.repr (markedQuotientDirection F v w marked t (Pi.single i 1)) j : ℝ)| ≤ B) :
    coordinateL2Norm ((e.baseChange ℝ).equivFun (realMarkedParameterDirection F v w marked t a)) ≤
      ((d : ℝ) + 1) * ((t : ℝ) * A * B) := by
  apply (coordinateL2Norm_le_card_bound _ (by positivity)
    (fun j => realMarkedParameterDirection_coordinate_le F v w marked t e a hA ha he j)).trans_eq
  simp only [Fintype.card_fin]

namespace NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N d : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)
  (e : Basis (Fin d) ℚ (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t))

theorem localPhaseMarkedSmallElement_coordinateL2Norm_le {Q : ℝ}
    (hd : (d : ℝ) ≤ Q) (ht : (t : ℝ) ≤ Q) (hm : (m : ℝ) ≤ Real.exp Q)
    (he : ∀ i j, rationalLogHeight
      (e.repr (markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t (RationalTorus.basis t i)) j) ≤ Q)
    (h : ZMod N) (hL : ∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1) :
    coordinateL2Norm ((e.baseChange ℝ).equivFun
      (D.localPhaseMarkedSmallElement t u c h₀ m h).coord) ≤ Real.exp (4 * Q) := by
  have ha (i : Fin t) : |-(m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i| ≤ (m : ℝ) := by
    rw [abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg m)]
    exact (mul_le_mul_of_nonneg_left (hL i) (Nat.cast_nonneg m)).trans_eq (mul_one _)
  have he' (i : Fin t) (j : Fin d) :
      |(e.repr (markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t (Pi.single i 1)) j : ℝ)| ≤ Real.exp Q := by
    have hi : (RationalTorus.basis t i : Fin t → ℚ) = Pi.single i 1 := Pi.basisFun_apply ℚ (Fin t) i
    have hh := he i j
    rw [hi] at hh
    exact (rational_abs_real_le_numerator _).trans ((rationalLogHeight_le_iff _ _).mp hh).1
  have hnorm := realMarkedParameterDirection_coordinateL2Norm_le
    D.coefficientFreeFiltration D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
    t e (fun i => -(m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i)
    (Nat.cast_nonneg m) (Real.exp_nonneg Q) ha he'
  have hd' : (d : ℝ) + 1 ≤ Real.exp Q :=
    (add_le_add hd (le_refl (1 : ℝ))).trans (Real.add_one_le_exp Q)
  have ht' : (t : ℝ) ≤ Real.exp Q :=
    ht.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp Q))
  apply hnorm.trans
  calc
    ((d : ℝ) + 1) * ((t : ℝ) * (m : ℝ) * Real.exp Q) ≤
        Real.exp Q * (Real.exp Q * Real.exp Q * Real.exp Q) := by gcongr
    _ = _ := by simp only [← Real.exp_add]; congr 1; ring

variable [TopologicalSpace (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]
  [T2Space (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]

theorem localPhaseMarkedSmallElement_dist_le {Q : ℝ}
    (hd : (d : ℝ) ≤ Q) (ht : (t : ℝ) ≤ Q) (hm : (m : ℝ) ≤ Real.exp Q)
    (he : ∀ i j, rationalLogHeight
      (e.repr (markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t (RationalTorus.basis t i)) j) ≤ Q)
    (h : ZMod N) (hL : ∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1) :
    letI := rightMetricSpace
      (hnil := (D.markedQuotientMultidegree t).realification.ordinary.lowerCentralSeries_eq_bot) (e.baseChange ℝ)
    dist 1 (D.localPhaseMarkedSmallElement t u c h₀ m h) ≤ Real.exp (4 * Q) := by
  let := rightMetricSpace
    (hnil := (D.markedQuotientMultidegree t).realification.ordinary.lowerCentralSeries_eq_bot) (e.baseChange ℝ)
  exact (dist_one_le_coordinateL2Norm (e.baseChange ℝ) _).trans
    (D.localPhaseMarkedSmallElement_coordinateL2Norm_le t u c h₀ m e hd ht hm he h hL)

end NativeRankRelation.CommonData

end Erdos3

end

section

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

theorem realAffineMarkedSlope_zero (j : Fin s) : D.realAffineMarkedSlope t y 0 j = 0 := by
  apply Subtype.ext
  change (monomialLinearMap (0 : Fin t →₀ ℕ)).baseChange ℝ
    (∑ i, (0 : ℝ) • (y j i).val) = 0
  simp

theorem realAffineMarkedBase_shift_eval (a : Fin t → ℝ) (j : Fin s) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t 0).baseChange ℝ
        (realMarkedAffineShift D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
          D.coefficientFreeGenerator_mem_layer t a
          (realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
            D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
            D.coefficientFreeGenerator_mem_layer t (j.val + 1) 0 1 (D.realAffineMarkedBase t x y j))) =
      (x j).val + ∑ i, a i • (y j i).val := by
  apply realMarkedAffineShift_eval_affine
  intro b
  simpa only [← Rat.cast_smul_eq_qsmul ℝ] using D.realAffineMarkedBase_eval t x y j b

theorem commonAffineMarkedLift_shift_eval (a : Fin t → ℝ) (h n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t 0).baseChange ℝ
        (realMarkedAffineShift D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
          D.coefficientFreeGenerator_mem_layer t a (D.commonAffineMarkedLift t x y 0 h n)) =
      ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) • ((x j).val + ∑ i, a i • (y j i).val) := by
  have hz (j : Fin s) :
      realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1 (D.realAffineMarkedSlope t y 0 j) = 0 := by
    rw [D.realAffineMarkedSlope_zero t y j]
    exact (realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1).map_zero
  simp only [commonAffineMarkedLift, hz, smul_zero, add_zero,
    map_sum, LinearMap.map_smul_of_tower]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra => (n : ℚ) ^ (j.val + 1) • z)
    (D.realAffineMarkedBase_shift_eval t x y a j)

variable (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)

noncomputable def localPhaseMarkedLift (h : ZMod N) (n : ℤ) :
    ℝ ⊗[ℚ] markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t :=
  realMarkedAffineShift D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t
      (fun i => (m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i)
      (D.commonAffineMarkedLift t x (fun j i => (m : ℝ)⁻¹ • y j i) 0 h.val n)

theorem localPhaseMarkedLift_eval (hm : 0 < m) (h : ZMod N) (n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t 0).baseChange ℝ
        (D.localPhaseMarkedLift t x y u c h₀ m h n) =
      ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
        ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  apply (D.commonAffineMarkedLift_shift_eval t x (fun j i => (m : ℝ)⁻¹ • y j i)
    (fun i => (m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i) h.val n).trans
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra => (n : ℚ) ^ (j.val + 1) • z)
  apply congrArg ((x j).val + ·)
  apply Finset.sum_congr rfl
  intro i _
  change ((m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i) •
    ((m : ℝ)⁻¹ • (y j i).val) = _
  rw [smul_smul]
  apply congrArg (fun z : ℝ => z • (y j i).val)
  field_simp [hm0]

theorem localPhaseMarkedSmallElement_inv (h : ZMod N) :
    (D.localPhaseMarkedSmallElement t u c h₀ m h)⁻¹ =
      realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t
          (fun i => (m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i) := by
  apply (realMarkedParameterElement_inv D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t
      (fun i => -(m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i)).trans
  apply congrArg (realMarkedParameterElement D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
    D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t)
  funext i
  simp only [Pi.neg_apply, neg_mul, neg_neg]

theorem localPhaseMarkedLift_conjugation (hs : 1 ≤ s) (h : ZMod N) (n : ℤ) :
    conjugationCoord (D.localPhaseMarkedSmallElement t u c h₀ m h)⁻¹
      (((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
        (correlationInput (h.val : ℤ) n)
        (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0)).coord) =
      (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
          (D.localPhaseMarkedLift t x y u c h₀ m h n) := by
  apply (congrArg (fun z => conjugationCoord z _)
    (D.localPhaseMarkedSmallElement_inv t u c h₀ m h)).trans
  apply (congrArg (conjugationCoord _)
    (D.commonAffineMarkedOrbit_eval t x (fun j i => (m : ℝ)⁻¹ • y j i) 0 h.val n)).trans
  exact realMarkedAffineShift_conjugation D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t hs
      (fun i => (m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i)
      (D.commonAffineMarkedLift t x (fun j i => (m : ℝ)⁻¹ • y j i) 0 h.val n)

theorem localPhaseMarkedOrbit_lift_factorization (hs : 1 ≤ s) (h : ZMod N) (n : ℤ) :
    (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m) *
        (D.scaledLocalAffineCorrectingElement t u c h₀ m h)⁻¹ =
      D.localPhaseMarkedSmallElement t u c h₀ m h *
        ⟨(lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
            (D.localPhaseMarkedLift t x y u c h₀ m h n)⟩ := by
  let ε := D.localPhaseMarkedSmallElement t u c h₀ m h
  let g := (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
    (correlationInput (h.val : ℤ) n)
    (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0)
  have hg : ε⁻¹ * g * ε =
      ⟨(lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
          (D.localPhaseMarkedLift t x y u c h₀ m h n)⟩ := by
    apply NilpotentLieBCHGroup.ext
    simpa only [conjugationCoord, inv_inv] using D.localPhaseMarkedLift_conjugation t x y u c h₀ m hs h n
  apply (D.localPhaseMarkedOrbit_right_normalization t x y u c h₀ m h n).trans
  calc
    g * ε = ε * (ε⁻¹ * g * ε) := by simp only [mul_assoc, mul_inv_cancel_left]
    _ = _ := congrArg (ε * ·) hg

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

theorem markedQuotientPhase_real_map (z : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedQuotientPhase F v w marked t).toLinearMap.baseChange ℝ
        ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ z) =
      (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ z := by
  induction z using TensorProduct.inductionOn with
  | tmul c z => simp only [LinearMap.baseChange_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realMarkedShiftTranslate_phase (a : Fin t → ℚ)
    (z : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ
        ((markedShiftTranslate F v w marked hw hv t a).baseChange ℝ z) =
      (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ z := by
  induction z using TensorProduct.inductionOn with
  | tmul c z => simp only [LinearMap.baseChange_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realMarkedAffineShift_phase (a : Fin t → ℝ)
    (z : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ
        (realMarkedAffineShift F v w marked hw hv t a z) =
      (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ z := by
  rw [realMarkedAffineShift_apply F v w marked hw hv t a z]
  simp only [map_add, map_sum, map_smul, map_sub, realMarkedShiftTranslate_phase,
    sub_self, smul_zero, Finset.sum_const_zero, add_zero]

theorem realMarkedPolynomialLift_phase (d k l : ℕ) (hd : d ≠ 0)
    (z : (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ) :
    (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ
      (realMarkedPolynomialLift F v w marked hw hv t d k l z) = 0 := by
  have hker : markedShiftBiLayer F v w marked t k d ≤
      LinearMap.ker (markedShiftPhase F v w marked t).toLinearMap := by
    intro p hp
    exact hp.2 (Or.inl hd)
  have hz := Submodule.baseChange_mono ℝ hker (realMarkedPolynomialLift_mem F v w marked hw hv t d k l z)
  rwa [realification_ker, LinearMap.mem_ker] at hz

end Erdos3

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
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P) (t : ℕ)

noncomputable def markedDependentEvaluation (a : Fin t → ℚ) :
    MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t →ₗ[ℚ] D.DependentQuotient :=
  markedBaseEvaluation D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t (D.dependentWordIdeal 0 2 0) le_rfl a

noncomputable def markedDependentEvaluationLie (a : Fin t → ℚ) :
    markedQuotientPolynomialAlgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t →ₗ⁅ℚ⁆ D.DependentQuotient :=
  markedBaseEvaluationLie D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t (D.dependentWordIdeal 0 2 0) le_rfl a

theorem markedDependentEvaluation_map (a : Fin t → ℚ)
    (z : markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t) :
    D.markedDependentEvaluation t a
        (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t) z) =
      D.dependentQuotientMap (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t a z) := rfl

theorem markedDependentEvaluation_real_map (a : Fin t → ℚ)
    (z : ℝ ⊗[ℚ] markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t) :
    (D.markedDependentEvaluation t a).baseChange ℝ
        ((lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ z) =
      D.dependentQuotientMap.toLinearMap.baseChange ℝ
        ((markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t a).baseChange ℝ z) :=
  markedBaseEvaluation_real_map D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t (D.dependentWordIdeal 0 2 0) le_rfl a z

theorem localPhaseMarkedLift_base_projection
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) (hm : 0 < m) (h : ZMod N) (n : ℤ) :
    (D.markedDependentEvaluation t 0).baseChange ℝ
        ((lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
            (D.localPhaseMarkedLift t x y u c h₀ m h n)) =
      D.dependentQuotientMap.toLinearMap.baseChange ℝ
        (∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
          ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val)) :=
  (D.markedDependentEvaluation_real_map t 0 _).trans
    (congrArg (D.dependentQuotientMap.toLinearMap.baseChange ℝ)
      (D.localPhaseMarkedLift_eval t x y u c h₀ m hm h n))

theorem markedDependentEvaluation_top_mem (a : Fin t → ℚ)
    (z : markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t)
    (hz : z ∈ markedShiftPolynomialSubmodule D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t s 0 r) :
    D.markedDependentEvaluation t a
        (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t) z) ∈ D.dependentQuotientFiltration.layer s r :=
  D.dependentQuotientMap_mem_layer
    (D.dependentWordLayer_le_degreeRank s 0 r
      (markedPolynomialLayer_eval_mem D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent hz.2 a))

theorem markedDependentEvaluation_top_frequency (a : Fin t → ℚ)
    (ξ : D.DependentQuotient →ₗ[ℚ] ℚ) (η : D.CoefficientFreeLieAlgebra →ₗ[ℚ] ℚ)
    (hξ : ∀ z ∈ D.coefficientFreeFiltration.layer s r, ξ (D.dependentQuotientMap z) = η z)
    (z : markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t)
    (hz : z ∈ markedShiftPolynomialSubmodule D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t s 0 r) :
    ξ (D.markedDependentEvaluation t a
      (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t) z)) =
      η (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t a z) :=
  hξ _ (D.dependentWordLayer_le_degreeRank s 0 r
    (markedPolynomialLayer_eval_mem D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent hz.2 a))

theorem markedDependentEvaluation_real_top_frequency (a : Fin t → ℚ)
    (ξ : D.DependentQuotient →ₗ[ℚ] ℚ) (η : D.CoefficientFreeLieAlgebra →ₗ[ℚ] ℚ)
    (hξ : ∀ z ∈ D.coefficientFreeFiltration.layer s r, ξ (D.dependentQuotientMap z) = η z)
    (z : ℝ ⊗[ℚ] markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t)
    (hz : z ∈ (markedShiftPolynomialSubmodule D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t s 0 r).baseChange ℝ) :
    realifyFunctional ξ ((D.markedDependentEvaluation t a).baseChange ℝ
      ((lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ z)) =
      realifyFunctional η ((markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t a).baseChange ℝ z) := by
  have he := marked_frequency_realification D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t a s 0 r
    (ξ.comp (D.markedDependentEvaluation t a)) η
    (D.markedDependentEvaluation_top_frequency t a ξ η hξ) z hz
  simpa only [realifyFunctional_comp] using he

theorem commonAffineMarkedLift_phase
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u : Fin t → ℝ) (h n : ℤ) :
    (markedShiftPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t).toLinearMap.baseChange ℝ
        (D.commonAffineMarkedLift t x y u h n) = 0 := by
  simp only [commonAffineMarkedLift, map_sum, LinearMap.map_smul_of_tower, map_add]
  apply Finset.sum_eq_zero
  intro j _
  have hb := realMarkedPolynomialLift_phase D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t (j.val + 1) 0 1 (by omega) (D.realAffineMarkedBase t x y j)
  have hs := realMarkedPolynomialLift_phase D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1 (by omega) (D.realAffineMarkedSlope t y u j)
  apply (congrArg₂ (fun a b : ℝ ⊗[ℚ] RationalTorus.Algebra t =>
    (n : ℚ) ^ (j.val + 1) • (a + (h : ℚ) • b)) hb hs).trans
  simp only [smul_zero, add_zero]

theorem localPhaseMarkedLift_pure
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) (h : ZMod N) (n : ℤ) :
    (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
        (D.localPhaseMarkedLift t x y u c h₀ m h n) ∈
      (markedQuotientPolynomialAlgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t).toSubmodule.baseChange ℝ := by
  change _ ∈ (LinearMap.ker (markedQuotientPhase D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t).toLinearMap).baseChange ℝ
  rw [realification_ker, LinearMap.mem_ker]
  apply (markedQuotientPhase_real_map D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t _).trans
  apply (realMarkedAffineShift_phase D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t _ _).trans
  exact D.commonAffineMarkedLift_phase t x (fun j i => (m : ℝ)⁻¹ • y j i) 0 h.val n

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped BigOperators TensorProduct NNReal

namespace RationalFilteredNilmanifold

theorem exists_bounded_left_translated_unit (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (E : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → E.GeometryComplexityLE p → ∀ {κ : Type*} [Fintype κ]
      (V : E.UnitVerticalObservable (E.filtration.realification.subgroup s) κ p)
      (ε : E.RealGroup),
      (∀ i, |(E.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp (4 * p)) →
      ∃ U : E.UnitVerticalObservable (E.filtration.realification.subgroup s) κ ((p + C) ^ C),
        U.frequency = V.frequency ∧ ∀ i x, U.observable i x = V.observable i (ε • x) := by
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz s 2
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (X + 2 + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro L _ _ d _ _ _ _ E p hp hE κ _ V ε hε
  let := E.metricSpace
  let l := normalizedSquareLeftBudget 2 b p
  have hl : 0 ≤ l := normalizedSquareLeftBudget_nonneg 2 b hp
  have hb : p + l ≤ (p + C) ^ C := by
    simpa [X, l, normalizedSquareLeftBudget, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := (le_add_of_nonneg_right hl).trans hb
  obtain ⟨A, _, hA, hLip⟩ := hleft E p hp hE
  have hε' : ∀ i, |(E.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + 2) ^ 2) := by
    intro i
    exact (hε i).trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p]))
  have hK : ((V.lipBound * A : ℝ≥0) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ Real.exp p * Real.exp l :=
        mul_le_mul V.lip_bound hA A.coe_nonneg (Real.exp_nonneg p)
      _ = Real.exp (p + l) := (Real.exp_add p l).symm
      _ ≤ _ := Real.exp_le_exp.mpr hb
  let U : E.UnitVerticalObservable (E.filtration.realification.subgroup s) κ ((p + C) ^ C) :=
    { observable := fun i x => V.observable i (ε • x)
      unit := fun x => V.unit (ε • x)
      norm := fun i x => V.norm i (ε • x)
      lipBound := V.lipBound * A
      lip_bound := hK
      lipschitz := fun i => (V.lipschitz i).comp (hLip ε hε')
      frequency := V.frequency
      height := fun i => (V.height i).trans hpC
      vertical := fun i z hz x => E.vertical_left_translate (V.observable i) V.frequency
        (V.vertical i) ε z hz x
      integral := V.integral }
  exact ⟨U, rfl, fun _ _ => rfl⟩

end RationalFilteredNilmanifold

namespace NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N d : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)
  (e : Basis (Fin d) ℚ (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t))

theorem localPhaseMarkedSmallElement_coordinate_le {Q : ℝ}
    (hd : (d : ℝ) ≤ Q) (ht : (t : ℝ) ≤ Q) (hm : (m : ℝ) ≤ Real.exp Q)
    (he : ∀ i j, rationalLogHeight
      (e.repr (markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t (RationalTorus.basis t i)) j) ≤ Q)
    (h : ZMod N) (hL : ∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1) (j : Fin d) :
    |(e.baseChange ℝ).repr (D.localPhaseMarkedSmallElement t u c h₀ m h).coord j| ≤ Real.exp (4 * Q) :=
  (abs_coordinate_le_coordinateL2Norm _ j).trans
    (D.localPhaseMarkedSmallElement_coordinateL2Norm_le t u c h₀ m e hd ht hm he h hL)

theorem localPhaseMarkedObservable_factorization
    (Γ : Subgroup (D.markedQuotientMultidegree t).realification.Group)
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (hs : 1 ≤ s) (h : ZMod N)
    (hΓ : D.scaledLocalAffineCorrectingElement t u c h₀ m h ∈ Γ)
    (F : (D.markedQuotientMultidegree t).realification.Group ⧸ Γ → ℂ) (n : ℤ) :
    F (QuotientGroup.mk ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m))) =
      F (D.localPhaseMarkedSmallElement t u c h₀ m h • QuotientGroup.mk
        (⟨(lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
            (D.localPhaseMarkedLift t x y u c h₀ m h n)⟩ :
              (D.markedQuotientMultidegree t).realification.Group)) := by
  let g := (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
    (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m)
  have hq : (QuotientGroup.mk g : (D.markedQuotientMultidegree t).realification.Group ⧸ Γ) =
      QuotientGroup.mk (g * (D.scaledLocalAffineCorrectingElement t u c h₀ m h)⁻¹) :=
    (quotient_mk_mul_mem Γ g ⟨_, Γ.inv_mem hΓ⟩).symm
  apply (congrArg F hq).trans
  exact congrArg (fun z : (D.markedQuotientMultidegree t).realification.Group => F (QuotientGroup.mk z))
    (D.localPhaseMarkedOrbit_lift_factorization t x y u c h₀ m hs h n)

end NativeRankRelation.CommonData

end Erdos3

end

end OAI
