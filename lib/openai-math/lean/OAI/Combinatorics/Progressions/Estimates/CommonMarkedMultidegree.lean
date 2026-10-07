/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Fourier.CommonShiftQuotientFrequency
import OAI.Combinatorics.Progressions.Geometry.MarkedDirectionCoordinates

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mixedCorrelationDegree_sum (s : ℕ) : (∑ i, mixedCorrelationDegree s i) = s + 1 := by
  rw [Fin.sum_univ_two]
  change 1 + s = s + 1
  omega

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)

noncomputable def markedShiftMultidegree (t : ℕ) :
    MultidegreeLieFiltration (Fin 2) (MarkedShiftQuotient F v w marked t) (s + 1)
      (mixedCorrelationDegree s) :=
  MultidegreeLieFiltration.ofLayers (markedShiftQuotientLayer F v w marked t)
    (markedShiftQuotientLayer_antitone F v w marked t) (markedShiftQuotientLayer_zero F v w marked t)
    (markedShiftQuotientLayer_lie_mem F v w marked t) (markedShiftQuotientLayer_total_one F v w marked hw t)
    (mixedCorrelationDegree s) (markedShiftQuotientLayer_terminal F v w marked hv t) (s + 1)
    (by rw [mixedCorrelationDegree_sum])

@[simp] theorem markedShiftMultidegree_layer (t : ℕ) (a : Fin 2 → ℕ) :
    (markedShiftMultidegree F v w marked hw hv t).layer a = markedShiftQuotientLayer F v w marked t a := rfl

include hw hv in
theorem markedShiftMultidegree_lowerCentralSeries_eq_bot (t : ℕ) :
    LieModule.lowerCentralSeries ℚ (MarkedShiftQuotient F v w marked t)
      (MarkedShiftQuotient F v w marked t) (s + 1) = ⊥ :=
  (markedShiftMultidegree F v w marked hw hv t).ordinary.lowerCentralSeries_eq_bot

abbrev MarkedMixedGroup (t : ℕ) := (markedShiftMultidegree F v w marked hw hv t).Group

theorem markedMixedGroup_nilpotencyClass_le (t : ℕ) :
    _root_.Group.nilpotencyClass (MarkedMixedGroup F v w marked hw hv t) ≤ s + 1 :=
  (markedShiftMultidegree F v w marked hw hv t).ordinary.nilpotencyClass_le

theorem markedShiftMultidegree_top_central (t : ℕ)
    (x y : MarkedShiftQuotient F v w marked t)
    (hy : y ∈ (markedShiftMultidegree F v w marked hw hv t).layer (mixedCorrelationDegree s)) :
    ⁅x, y⁆ = 0 := by
  let M := markedShiftMultidegree F v w marked hw hv t
  have hx : x ∈ M.ordinary.layer 1 := by rw [M.ordinary.one_eq_top]; trivial
  have hy' : y ∈ M.ordinary.layer (s + 1) := by
    have h := M.layer_le_ordinary (mixedCorrelationDegree s) hy
    simpa only [mixedCorrelationDegree_sum] using h
  have h := M.ordinary.lie_mem hx hy'
  have he : 1 + (s + 1) = (s + 1) + 1 := by omega
  rw [he, M.ordinary.terminal, Submodule.mem_bot] at h
  exact h

theorem markedShiftMultidegree_top_rank_mem (t : ℕ)
    {x : markedShiftSubalgebra F v w marked t}
    (hx : x ∈ markedShiftPolynomialSubmodule F v w marked t s 1 r) :
    lieQuotientMap (markedShiftSecondIdeal F v w marked t) x ∈
      (markedShiftMultidegree F v w marked hw hv t).layer (mixedCorrelationDegree s) := by
  refine ⟨x, ?_, rfl⟩
  constructor
  · exact markedPolynomialLayer_antitone v w marked le_rfl le_rfl (Nat.zero_le r) hx.2
  · intro _
    exact hx.1

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

noncomputable def realMarkedDirection (h : Fin t → ℚ) : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t :=
  rationalLieInclusion (markedQuotientDirection F v w marked t h)

theorem realMarkedDirection_double_lie (h : Fin t → ℚ) (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    ⁅realMarkedDirection F v w marked t h, ⁅realMarkedDirection F v w marked t h, x⁆⁆ = 0 := by
  change ⁅(1 : ℝ) ⊗ₜ[ℚ] markedQuotientDirection F v w marked t h,
    ⁅(1 : ℝ) ⊗ₜ[ℚ] markedQuotientDirection F v w marked t h, x⁆⁆ = 0
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [LieAlgebra.ExtendScalars.bracket_tmul, LieAlgebra.ExtendScalars.bracket_tmul,
      markedQuotientDirection_double_lie, TensorProduct.tmul_zero]
  | add x y hx hy => rw [LieRing.lie_add, LieRing.lie_add, hx, hy, add_zero]

theorem realMarkedTranslate_first_order (h : Fin t → ℚ) (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    (markedQuotientTranslate F v w marked hw hv t h).baseChange ℝ x =
      x + ⁅realMarkedDirection F v w marked t h, x⁆ := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, markedQuotientTranslate_first_order, TensorProduct.tmul_add]
    change a ⊗ₜ[ℚ] x + a ⊗ₜ[ℚ] ⁅markedQuotientDirection F v w marked t h, x⁆ =
      a ⊗ₜ[ℚ] x + ⁅(1 : ℝ) ⊗ₜ[ℚ] markedQuotientDirection F v w marked t h, a ⊗ₜ[ℚ] x⁆
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
  | add x y hx hy =>
    rw [map_add, hx, hy, LieRing.lie_add]
    abel

theorem realMarkedTranslate_conjugation (hs : 1 ≤ s) (h : Fin t → ℚ)
    (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    conjugationCoord (⟨realMarkedDirection F v w marked t h⟩ :
      (markedShiftMultidegree F v w marked hw hv t).realification.Group) x =
        (markedQuotientTranslate F v w marked hw hv t h).baseChange ℝ x := by
  exact (conjugationCoord_eq_add_lie (by omega)
    (⟨realMarkedDirection F v w marked t h⟩ :
      (markedShiftMultidegree F v w marked hw hv t).realification.Group) x
        (realMarkedDirection_double_lie F v w marked t h x)).trans
          (realMarkedTranslate_first_order F v w marked hw hv t h x).symm

theorem realMarkedTranslate_quotient (h : Fin t → ℚ)
    (x : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ
        ((markedShiftTranslate F v w marked hw hv t h).baseChange ℝ x) =
      (markedQuotientTranslate F v w marked hw hv t h).baseChange ℝ
        ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [LinearMap.baseChange_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realMarkedShiftEval_translate (h a : Fin t → ℚ)
    (x : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedShiftEval F v w marked t a).baseChange ℝ
        ((markedShiftTranslate F v w marked hw hv t h).baseChange ℝ x) =
      (markedShiftEval F v w marked t (a + h)).baseChange ℝ x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      LinearMap.baseChange_tmul, markedShiftEval_translate]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realMarkedTranslate_conjugation_lift (hs : 1 ≤ s) (h : Fin t → ℚ)
    (x : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    conjugationCoord (⟨realMarkedDirection F v w marked t h⟩ :
      (markedShiftMultidegree F v w marked hw hv t).realification.Group)
        ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ x) =
      (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ
        ((markedShiftTranslate F v w marked hw hv t h).baseChange ℝ x) := by
  rw [realMarkedTranslate_conjugation F v w marked hw hv t hs]
  exact (realMarkedTranslate_quotient F v w marked hw hv t h x).symm

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ)

theorem markedQuotientDirection_smul (q : ℚ) (a : Fin t → ℚ) :
    markedQuotientDirection F v w marked t (q • a) =
      q • markedQuotientDirection F v w marked t a :=
  (markedQuotientDirectionLinear F v w marked t).map_smul q a

theorem realMarkedDirection_smul (q : ℚ) (a : Fin t → ℚ) :
    realMarkedDirection F v w marked t (q • a) =
      q • realMarkedDirection F v w marked t a := by
  exact (congrArg rationalLieInclusion (markedQuotientDirection_smul F v w marked t q a)).trans
    (rationalLieInclusion.map_smul q (markedQuotientDirection F v w marked t a))

theorem markedDirection_mem_realLattice_of_smul {k d : ℕ}
    (E : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) k d)
    (q : ℚ) (a : Fin t → ℚ)
    (ha : (⟨q • markedQuotientDirection F v w marked t a⟩ : E.filtration.Group) ∈ E.lattice) :
    (⟨realMarkedDirection F v w marked t (q • a)⟩ : E.RealGroup) ∈ E.realLattice := by
  refine Subgroup.mem_map.mpr ⟨⟨q • markedQuotientDirection F v w marked t a⟩, ha, ?_⟩
  apply NilpotentLieBCHGroup.ext
  exact congrArg rationalLieInclusion (markedQuotientDirection_smul F v w marked t q a).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

noncomputable def rationalMarkedDirectionMap :
    (Fin t → ℚ) →ₗ[ℚ] (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
  rationalLieInclusion.toLinearMap.comp (markedQuotientDirectionLinear F v w marked t)

theorem rationalMarkedDirectionMap_apply (a : Fin t → ℚ) :
    rationalMarkedDirectionMap F v w marked t a = realMarkedDirection F v w marked t a := rfl

noncomputable def realMarkedParameterDirection :
    (Fin t → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
  realDirectionExtension (rationalMarkedDirectionMap F v w marked t)

theorem realMarkedParameterDirection_apply (a : Fin t → ℝ) :
    realMarkedParameterDirection F v w marked t a =
      ∑ i, a i • realMarkedDirection F v w marked t (Pi.single i 1) := by
  rw [realMarkedParameterDirection, realDirectionExtension_apply]
  simp only [rationalMarkedDirectionMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun h : Fin t → ℚ => a i • realMarkedDirection F v w marked t h)
  funext j
  by_cases hij : i = j <;> simp [hij, eq_comm]

theorem realMarkedParameterDirection_rat (a : Fin t → ℚ) :
    realMarkedParameterDirection F v w marked t (fun i => (a i : ℝ)) =
      realMarkedDirection F v w marked t a :=
  realDirectionExtension_rat (rationalMarkedDirectionMap F v w marked t) a

theorem markedQuotientDirection_mem_first (a : Fin t → ℚ) :
    markedQuotientDirection F v w marked t a ∈
      markedShiftQuotientLayer F v w marked t (correlationInput 1 0) := by
  refine ⟨markedShiftDirection F v w marked t a, ?_, rfl⟩
  refine ⟨(markedPolynomialLayer v w marked 0 1 0).zero_mem, ?_⟩
  intro h
  change 0 ≠ 0 ∨ 1 < 1 at h
  omega

theorem realMarkedDirection_mem_first (a : Fin t → ℚ) :
    realMarkedDirection F v w marked t a ∈
      (markedShiftMultidegree F v w marked hw hv t).realification.layer (correlationInput 1 0) :=
  Submodule.tmul_mem_baseChange_of_mem 1 (markedQuotientDirection_mem_first F v w marked t a)

theorem realMarkedParameterDirection_mem_first (a : Fin t → ℝ) :
    realMarkedParameterDirection F v w marked t a ∈
      (markedShiftMultidegree F v w marked hw hv t).realification.layer (correlationInput 1 0) := by
  change realMarkedParameterDirection F v w marked t a ∈
    (markedShiftQuotientLayer F v w marked t (correlationInput 1 0)).baseChange ℝ
  rw [realMarkedParameterDirection_apply]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (realMarkedDirection_mem_first F v w marked hw hv t (Pi.single i 1))

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

theorem marked_first_layer_bracket_zero
    {x y : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t}
    (hx : x ∈ (markedShiftMultidegree F v w marked hw hv t).realification.layer (correlationInput 1 0))
    (hy : y ∈ (markedShiftMultidegree F v w marked hw hv t).realification.layer (correlationInput 1 0)) :
    ⁅x, y⁆ = 0 := by
  let M := (markedShiftMultidegree F v w marked hw hv t).realification
  have h := M.lie_mem hx hy
  have he : correlationInput (1 : ℕ) 0 + correlationInput 1 0 = correlationInput 2 0 := by
    funext i
    fin_cases i <;> rfl
  have ht : M.layer (correlationInput 2 0) = ⊥ := M.terminal _ (by
    intro hle
    have hh := hle 0
    exact Nat.not_succ_le_self 1 hh)
  rw [he, ht] at h
  exact h

include hw hv in
theorem realMarkedParameterDirection_lie (a b : Fin t → ℝ) :
    ⁅realMarkedParameterDirection F v w marked t a, realMarkedParameterDirection F v w marked t b⁆ = 0 :=
  marked_first_layer_bracket_zero F v w marked hw hv t
    (realMarkedParameterDirection_mem_first F v w marked hw hv t a)
    (realMarkedParameterDirection_mem_first F v w marked hw hv t b)

include hw hv in
theorem realMarkedParameterDirection_double_lie (a : Fin t → ℝ)
    (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    ⁅realMarkedParameterDirection F v w marked t a,
      ⁅realMarkedParameterDirection F v w marked t a, x⁆⁆ = 0 := by
  let M := (markedShiftMultidegree F v w marked hw hv t).realification
  have ha := realMarkedParameterDirection_mem_first F v w marked hw hv t a
  have hx : x ∈ M.layer 0 := by rw [M.zero_eq_top]; trivial
  have hb := M.lie_mem ha hx
  rw [add_zero] at hb
  exact marked_first_layer_bracket_zero F v w marked hw hv t ha hb

noncomputable def realMarkedParameterElement (a : Fin t → ℝ) :
    (markedShiftMultidegree F v w marked hw hv t).realification.Group :=
  ⟨realMarkedParameterDirection F v w marked t a⟩

theorem realMarkedParameterElement_mul (a b : Fin t → ℝ) :
    realMarkedParameterElement F v w marked hw hv t a *
      realMarkedParameterElement F v w marked hw hv t b =
        realMarkedParameterElement F v w marked hw hv t (a + b) := by
  apply NilpotentLieBCHGroup.ext
  change lieBCH (s + 1) (realMarkedParameterDirection F v w marked t a)
    (realMarkedParameterDirection F v w marked t b) = _
  rw [lieBCH_eq_add_of_lie_eq_zero
    (markedShiftMultidegree F v w marked hw hv t).realification.ordinary.lowerCentralSeries_eq_bot
    (realMarkedParameterDirection_lie F v w marked hw hv t a b)]
  exact ((realMarkedParameterDirection F v w marked t).map_add a b).symm

theorem realMarkedParameterElement_inv (a : Fin t → ℝ) :
    (realMarkedParameterElement F v w marked hw hv t a)⁻¹ =
      realMarkedParameterElement F v w marked hw hv t (-a) := by
  apply NilpotentLieBCHGroup.ext
  exact ((realMarkedParameterDirection F v w marked t).map_neg a).symm

theorem realMarkedParameterElement_conjugation (hs : 1 ≤ s) (a : Fin t → ℝ)
    (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    conjugationCoord (realMarkedParameterElement F v w marked hw hv t a) x =
      x + ⁅realMarkedParameterDirection F v w marked t a, x⁆ :=
  conjugationCoord_eq_add_lie (by omega) _ x
    (realMarkedParameterDirection_double_lie F v w marked hw hv t a x)

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def markedQuotientMultidegree (t : ℕ) :
    MultidegreeLieFiltration (Fin 2)
      (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t) (s + 1) (mixedCorrelationDegree s) :=
  markedShiftMultidegree D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t

abbrev MarkedQuotientGroup (t : ℕ) := (D.markedQuotientMultidegree t).Group

theorem markedQuotientGroup_nilpotencyClass_le (t : ℕ) :
    _root_.Group.nilpotencyClass (D.MarkedQuotientGroup t) ≤ s + 1 :=
  (D.markedQuotientMultidegree t).ordinary.nilpotencyClass_le

variable {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.exists_marked_multidegree_top_frequency (t : ℕ) (a : Fin t → ℚ) :
    ∃ ξ : MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t →ₗ[ℚ] ℚ,
      ∀ x ∈ markedShiftPolynomialSubmodule D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t s 1 r,
        let qx := lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration
          D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) x
        qx ∈ (D.markedQuotientMultidegree t).layer (mixedCorrelationDegree s) ∧
          (∀ y : MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
              D.coefficientWeight D.coefficientIsDependent t, ⁅y, qx⁆ = 0) ∧
          ξ qx = B.freeFrequency D (markedShiftEval D.coefficientFreeFiltration
            D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t a x) := by
  obtain ⟨ξ, hξ⟩ := B.exists_markedShift_quotient_frequency D t a
  refine ⟨ξ, ?_⟩
  intro x hx
  have htop := markedShiftMultidegree_top_rank_mem D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
    D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t hx
  refine ⟨htop, ?_, hξ x hx⟩
  intro y
  exact markedShiftMultidegree_top_central D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
    D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t y _ htop

end Erdos3.NativeRankRelation.CommonData

end

end OAI
