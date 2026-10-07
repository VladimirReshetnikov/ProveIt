/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Geometry.BoundedDependentCoordinates
import OAI.Combinatorics.Progressions.Lattices.FourAffineRefinement
import OAI.Combinatorics.Progressions.Linear.CommonRealDependentProjection

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

theorem real_horizontal_frequency (n : ℕ) (d : Fin n → Fin (s + 1)) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun j => (d j).val) a = s) (hr : a.length = r)
    (v : ∀ j, ℝ ⊗[ℚ] (Fin 4 → W.rank.filtration.HigherHorizontal (d j).val))
    (hv : ∀ j, v j ∈ (D.horizontal (d j)).baseChange ℝ) :
    realifyFunctional W.vertical.frequency (W.rank.filtration.realHorizontalTreeValue
      (fun j => (d j).val) a (fun j => (LinearMap.proj (0 : Fin 4)).baseChange ℝ (v j))) +
    realifyFunctional W.vertical.frequency (W.rank.filtration.realHorizontalTreeValue
      (fun j => (d j).val) a (fun j => (LinearMap.proj (1 : Fin 4)).baseChange ℝ (v j))) -
    realifyFunctional W.vertical.frequency (W.rank.filtration.realHorizontalTreeValue
      (fun j => (d j).val) a (fun j => (LinearMap.proj (2 : Fin 4)).baseChange ℝ (v j))) -
    realifyFunctional W.vertical.frequency (W.rank.filtration.realHorizontalTreeValue
      (fun j => (d j).val) a (fun j => (LinearMap.proj (3 : Fin 4)).baseChange ℝ (v j))) = 0 := by
  obtain ⟨t, ht⟩ := D.nonempty
  apply (R.interval ⟨t, D.subset ht⟩).real_refilteredHorizontalImage_frequency
    (D.witness t ht).index (D.witness t ht).subalgebra (fun j => (d j).val) a hd hr
    ((D.witness t ht).bracket n (fun j => (d j).val) a hd hr) v
  intro j
  rw [D.horizontalImage_eq t ht (d j)]
  exact hv j

theorem real_sunflower_bracket (n : ℕ) (d : Fin n → Fin (s + 1)) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun j => (d j).val) a = s) (hr : a.length = r)
    (v : ∀ j, ℝ ⊗[ℚ] W.rank.filtration.HigherHorizontal (d j).val)
    (hv : ∀ j, v j ∈ (fourFirstProjection (D.horizontal (d j))).baseChange ℝ)
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ (fourDependentProjection (D.horizontal (d j))).baseChange ℝ)
    (hvk : v k ∈ (fourDependentProjection (D.horizontal (d k))).baseChange ℝ) :
    realifyFunctional W.vertical.frequency
      (W.rank.filtration.realHorizontalTreeValue (fun j => (d j).val) a v) = 0 :=
  real_four_dependent_inputs_vanish (lieTreeSupport a)
    (W.rank.filtration.realHorizontalTreeValue (fun j => (d j).val) a)
    (fun u j hj hu => W.rank.filtration.realHorizontalTreeValue_zero_of_leaf
      (fun j => (d j).val) a u (i := j) hj hu)
    (realifyFunctional W.vertical.frequency) (map_zero _) (fun j => D.horizontal (d j))
    (D.real_horizontal_frequency n d a hd hr) v hv j k hjk hj hk hvj hvk

theorem real_sunflower_representatives (n : ℕ) (d : Fin n → Fin (s + 1)) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun j => (d j).val) a = s) (hr : a.length = r)
    (v : ∀ j, (W.rank.filtration.layer (d j).val 1).baseChange ℝ)
    (hv : ∀ j, W.rank.filtration.realHorizontalMap (d j).val (v j) ∈
      (fourFirstProjection (D.horizontal (d j))).baseChange ℝ)
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : W.rank.filtration.realHorizontalMap (d j).val (v j) ∈
      (fourDependentProjection (D.horizontal (d j))).baseChange ℝ)
    (hvk : W.rank.filtration.realHorizontalMap (d k).val (v k) ∈
      (fourDependentProjection (D.horizontal (d k))).baseChange ℝ) :
    realifyFunctional W.vertical.frequency (lieTreeEval (fun j => (v j).val) a) = 0 := by
  have h := D.real_sunflower_bracket n d a hd hr
    (fun j => W.rank.filtration.realHorizontalMap (d j).val (v j)) hv j k hjk hj hk hvj hvk
  rwa [W.rank.filtration.realHorizontalTreeValue_map (fun j => (d j).val) a hd hr v] at h

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

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def commonCoefficientSpace (d : Fin (s + 1)) : Submodule ℚ W.L :=
  W.rank.filtration.horizontalPreimage d.val (fourFirstProjection (D.horizontal d))

noncomputable def dependentCoefficientSpace (d : Fin (s + 1)) : Submodule ℚ W.L :=
  W.rank.filtration.horizontalPreimage d.val (fourDependentProjection (D.horizontal d))

theorem commonCoefficientSpace_le (d : Fin (s + 1)) :
    D.commonCoefficientSpace d ≤ W.rank.filtration.layer d.val 1 :=
  W.rank.filtration.horizontalPreimage_le d.val _

theorem dependentCoefficientSpace_le_common (d : Fin (s + 1)) :
    D.dependentCoefficientSpace d ≤ D.commonCoefficientSpace d :=
  W.rank.filtration.horizontalPreimage_mono d.val (fourDependentProjection_le _)

theorem native_coefficient_mem_common {σ ι : Type*} (hs : 1 ≤ s)
    (c : Basis ι ℚ W.L) (τ : ι → ℕ)
    (hF : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) (hα : Finsupp.weight w α ≤ s)
    (g : W.model.filtration.realification.PolynomialOrbit w) :
    coefficients g.log α ∈
        (D.commonCoefficientSpace ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩).baseChange ℝ ↔
      Multiplicative.toAdd (W.rank.filtration.nativeHorizontalCoefficientHom
        hs c τ hF w α (W.rank.orbitEquiv w g)) ∈
        (fourFirstProjection (D.horizontal
          ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩)).baseChange ℝ := by
  unfold commonCoefficientSpace
  rw [← W.rank.orbitEquiv_log w g]
  exact W.rank.filtration.native_coefficient_mem_horizontalPreimage hs c τ hF w α
    (W.rank.orbitEquiv w g) (fourFirstProjection (D.horizontal
      ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩))

theorem native_coefficient_mem_dependent {σ ι : Type*} (hs : 1 ≤ s)
    (c : Basis ι ℚ W.L) (τ : ι → ℕ)
    (hF : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) (hα : Finsupp.weight w α ≤ s)
    (g : W.model.filtration.realification.PolynomialOrbit w) :
    coefficients g.log α ∈
        (D.dependentCoefficientSpace ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩).baseChange ℝ ↔
      Multiplicative.toAdd (W.rank.filtration.nativeHorizontalCoefficientHom
        hs c τ hF w α (W.rank.orbitEquiv w g)) ∈
        (fourDependentProjection (D.horizontal
          ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩)).baseChange ℝ := by
  unfold dependentCoefficientSpace
  rw [← W.rank.orbitEquiv_log w g]
  exact W.rank.filtration.native_coefficient_mem_horizontalPreimage hs c τ hF w α
    (W.rank.orbitEquiv w g) (fourDependentProjection (D.horizontal
      ⟨Finsupp.weight w α, Nat.lt_succ_of_le hα⟩))

theorem coefficient_sunflower (n : ℕ) (d : Fin n → Fin (s + 1)) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun j => (d j).val) a = s) (hr : a.length = r)
    (v : Fin n → W.L) (hv : ∀ j, v j ∈ D.commonCoefficientSpace (d j))
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ D.dependentCoefficientSpace (d j))
    (hvk : v k ∈ D.dependentCoefficientSpace (d k)) :
    W.vertical.frequency (lieTreeEval v a) = 0 := by
  let u (i : Fin n) : W.rank.filtration.layer (d i).val 1 :=
    ⟨v i, D.commonCoefficientSpace_le (d i) (hv i)⟩
  exact D.sunflower_representatives n d a hd hr u
    (fun i => (W.rank.filtration.mem_horizontalPreimage _ _ (u i)).mp (hv i))
    j k hjk hj hk
    ((W.rank.filtration.mem_horizontalPreimage _ _ (u j)).mp hvj)
    ((W.rank.filtration.mem_horizontalPreimage _ _ (u k)).mp hvk)

theorem real_coefficient_sunflower (n : ℕ) (d : Fin n → Fin (s + 1)) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun j => (d j).val) a = s) (hr : a.length = r)
    (v : Fin n → ℝ ⊗[ℚ] W.L)
    (hv : ∀ j, v j ∈ (D.commonCoefficientSpace (d j)).baseChange ℝ)
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ (D.dependentCoefficientSpace (d j)).baseChange ℝ)
    (hvk : v k ∈ (D.dependentCoefficientSpace (d k)).baseChange ℝ) :
    realifyFunctional W.vertical.frequency (lieTreeEval v a) = 0 := by
  let u (i : Fin n) : (W.rank.filtration.layer (d i).val 1).baseChange ℝ :=
    ⟨v i, Submodule.baseChange_mono ℝ (D.commonCoefficientSpace_le (d i)) (hv i)⟩
  exact D.real_sunflower_representatives n d a hd hr u
    (fun i => (W.rank.filtration.mem_real_horizontalPreimage _ _ (u i)).mp (hv i))
    j k hjk hj hk
    ((W.rank.filtration.mem_real_horizontalPreimage _ _ (u j)).mp hvj)
    ((W.rank.filtration.mem_real_horizontalPreimage _ _ (u k)).mp hvk)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

structure CoefficientBases (Q : ℝ) where
  common : ∀ d : Fin s, Basis
    (Fin (finrank ℚ (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩))) ℚ
    (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩)
  dependent : ∀ d : Fin s, Basis
    (Fin (finrank ℚ (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩))) ℚ
    (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩)
  common_height : ∀ d i j, rationalLogHeight (W.model.basis.repr (common d i : W.L) j) ≤ Q
  dependent_height : ∀ d i j, rationalLogHeight (W.model.basis.repr (dependent d i : W.L) j) ≤ Q

def CoefficientBases.mono {Q Q' : ℝ} (B : D.CoefficientBases Q) (h : Q ≤ Q') :
    D.CoefficientBases Q' where
  common := B.common
  dependent := B.dependent
  common_height d i j := (B.common_height d i j).trans h
  dependent_height d i j := (B.dependent_height d i j).trans h

def CoefficientAlphabet : Type :=
  (Σ d : Fin s, Fin (finrank ℚ (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩))) ⊕
    (Σ d : Fin s, Fin (finrank ℚ (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩)))

noncomputable instance coefficientAlphabetFintype : Fintype D.CoefficientAlphabet := by
  unfold CoefficientAlphabet
  infer_instance

def coefficientDegree : D.CoefficientAlphabet → Fin (s + 1) :=
  Sum.elim (fun x => ⟨x.1.val + 1, by omega⟩) (fun x => ⟨x.1.val + 1, by omega⟩)

def coefficientWeight (x : D.CoefficientAlphabet) : ℕ := (D.coefficientDegree x).val

theorem coefficientWeight_pos (x : D.CoefficientAlphabet) : 0 < D.coefficientWeight x := by
  cases x with
  | inl x => exact Nat.zero_lt_succ _
  | inr x => exact Nat.zero_lt_succ _

theorem coefficientAlphabet_card : Fintype.card D.CoefficientAlphabet ≤ 2 * s * W.dim := by
  classical
  let : FiniteDimensional ℚ W.L := W.model.basis.finiteDimensional_of_finite
  have hdim (U : Submodule ℚ W.L) : finrank ℚ U ≤ W.dim := by
    simpa only [finrank_eq_card_basis W.model.basis, Fintype.card_fin] using U.finrank_le
  change Fintype.card
    ((Σ d : Fin s, Fin (finrank ℚ (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩))) ⊕
      (Σ d : Fin s, Fin (finrank ℚ (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩)))) ≤ _
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  calc
    _ ≤ (∑ _ : Fin s, W.dim) + ∑ _ : Fin s, W.dim :=
      Nat.add_le_add (Finset.sum_le_sum (fun _ _ => hdim _))
        (Finset.sum_le_sum (fun _ _ => hdim _))
    _ = 2 * s * W.dim := by simp; ring

noncomputable def CoefficientBases.generator {Q : ℝ} (B : D.CoefficientBases Q) :
    D.CoefficientAlphabet → W.L :=
  Sum.elim (fun x => (B.common x.1 x.2 : W.L)) (fun x => (B.dependent x.1 x.2 : W.L))

theorem CoefficientBases.generator_mem_common {Q : ℝ} (B : D.CoefficientBases Q)
    (x : D.CoefficientAlphabet) :
    B.generator D x ∈ D.commonCoefficientSpace (D.coefficientDegree x) := by
  cases x with
  | inl x => exact (B.common x.1 x.2).property
  | inr x => exact D.dependentCoefficientSpace_le_common _ (B.dependent x.1 x.2).property

theorem CoefficientBases.generator_mem_layer {Q : ℝ} (B : D.CoefficientBases Q)
    (x : D.CoefficientAlphabet) :
    B.generator D x ∈ W.rank.filtration.layer (D.coefficientWeight x) 0 := by
  rw [W.rank.filtration.rank_zero_eq_one]
  exact D.commonCoefficientSpace_le _ (B.generator_mem_common D x)

theorem CoefficientBases.generator_height {Q : ℝ} (B : D.CoefficientBases Q)
    (x : D.CoefficientAlphabet) (i : Fin W.dim) :
    rationalLogHeight (W.model.basis.repr (B.generator D x) i) ≤ Q := by
  cases x with
  | inl x => exact B.common_height x.1 x.2 i
  | inr x => exact B.dependent_height x.1 x.2 i

theorem CoefficientBases.generator_common_span {Q : ℝ} (B : D.CoefficientBases Q) (d : Fin s) :
    Submodule.span ℚ (Set.range (fun i => B.generator D (Sum.inl ⟨d, i⟩))) =
      D.commonCoefficientSpace ⟨d.val + 1, by omega⟩ :=
  span_submodule_basis _ (B.common d)

theorem CoefficientBases.generator_dependent_span {Q : ℝ} (B : D.CoefficientBases Q) (d : Fin s) :
    Submodule.span ℚ (Set.range (fun i => B.generator D (Sum.inr ⟨d, i⟩))) =
      D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩ :=
  span_submodule_basis _ (B.dependent d)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

noncomputable def coefficientSpaceInputBudget (p : ℝ) : ℝ :=
  p + 4 * p + horizontalCoordinateBudget p + (p + 3) ^ 7 + 1

noncomputable def coefficientSpaceBasisBudget (p : ℝ) : ℝ :=
  let a := coefficientSpaceInputBudget p
  preimageBasisBudget (a + (a + 2) ^ 4 + dependentCoordinateBudget a)

namespace NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem exists_coefficient_space_bases (hP : 0 ≤ P) (hbP : b ≤ P)
    (d : Fin (s + 1)) (hd : 1 ≤ d.val) :
    ∃ c : Basis (Fin (finrank ℚ (D.commonCoefficientSpace d))) ℚ (D.commonCoefficientSpace d),
      (∀ i j, rationalLogHeight (W.model.basis.repr (c i : W.L) j) ≤ coefficientSpaceBasisBudget P) ∧
      ∃ e : Basis (Fin (finrank ℚ (D.dependentCoefficientSpace d))) ℚ (D.dependentCoefficientSpace d),
        ∀ i j, rationalLogHeight (W.model.basis.repr (e i : W.L) j) ≤ coefficientSpaceBasisBudget P := by
  classical
  let : FiniteDimensional ℚ W.L := W.model.basis.finiteDimensional_of_finite
  have hR := W.complexity.mono W.rank hbP
  have hdim : (W.dim : ℝ) ≤ P := hR.1.1
  obtain ⟨m, hm, f, hf, v, hv, hvH⟩ := D.exists_bounded_coordinate_generators hP hbP d hd
  let J := D.coordinateSpace d f
  let a := coefficientSpaceInputBudget P
  have hhor := horizontalCoordinateBudget_nonneg hP
  have hpow : 0 ≤ (P + 3) ^ 7 := by positivity
  have hPa : P ≤ a := by dsimp only [a, coefficientSpaceInputBudget]; linarith
  have h4Pa : 4 * P ≤ a := by dsimp only [a, coefficientSpaceInputBudget]; linarith
  have hhora : horizontalCoordinateBudget P ≤ a := by
    dsimp only [a, coefficientSpaceInputBudget]; linarith
  have hpowa : (P + 3) ^ 7 ≤ a := by dsimp only [a, coefficientSpaceInputBudget]; linarith
  have ha : 0 ≤ a := hP.trans hPa
  have hma : (m : ℝ) ≤ a := (Nat.cast_le.mpr hm).trans (hdim.trans hPa)
  have hcols : Fintype.card (Fin (Fintype.card (Σ _ : Fin 4, Fin W.dim))) = 4 * W.dim := by simp
  have hcolsa : (Fintype.card (Fin (Fintype.card (Σ _ : Fin 4, Fin W.dim))) : ℝ) ≤ a := by
    rw [hcols, Nat.cast_mul, Nat.cast_ofNat]
    exact (mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4)).trans h4Pa
  obtain ⟨eD, heD⟩ := exists_dependent_coordinate_basis J v hv ha
    (by simpa only [Fintype.card_fin] using hma) hcolsa
    (fun i k j => (hvH i k j).trans hhora)
  have hdepdim : finrank ℚ (fourDependentProjection J) ≤ m := by
    simpa using (fourDependentProjection J).finrank_le
  let a₁ := W.rank.basis d ⟨1, by omega⟩
  let u : Fin (finrank ℚ (W.rank.filtration.layer d.val 1)) → W.L := fun i => a₁ i
  have hu : Submodule.span ℚ (Set.range u) = W.rank.filtration.layer d.val 1 :=
    span_submodule_basis _ a₁
  have hudim : finrank ℚ (W.rank.filtration.layer d.val 1) ≤ W.dim := by
    simpa only [finrank_eq_card_basis W.model.basis, Fintype.card_fin] using
      (W.rank.filtration.layer d.val 1).finrank_le
  have huH (i) (j) : rationalLogHeight (W.model.basis.repr (u i) j) ≤ P :=
    hR.2 d ⟨1, by omega⟩ i j
  let T := W.rank.filtration.ambientHorizontalCoordinates d.val f
  have hTu (i) (j) : rationalLogHeight ((Pi.basisFun ℚ (Fin m)).repr (T (u i)) j) ≤
      (a + 2) ^ 4 := by
    change rationalLogHeight (f.repr ((W.rank.filtration.layer d.val 2).mkQ (u i)) j) ≤ _
    exact linearMap_coordinate_logHeight W.model.basis f
      (W.rank.filtration.layer d.val 2).mkQ ha
      (by simpa only [Fintype.card_fin] using hdim.trans hPa)
      (fun k l => (hf l k).trans hpowa) (u i) (fun k => (huH i k).trans hPa) j
  let Q := a + (a + 2) ^ 4 + dependentCoordinateBudget a
  have hdep := dependentCoordinateBudget_nonneg ha
  have hpower : 0 ≤ (a + 2) ^ 4 := by positivity
  have haQ : a ≤ Q := by dsimp only [Q]; linarith
  have hpQ : (a + 2) ^ 4 ≤ Q := by dsimp only [Q]; linarith
  have hdQ : dependentCoordinateBudget a ≤ Q := by dsimp only [Q]; linarith
  have hQ : 0 ≤ Q := ha.trans haQ
  have huQ : (Fintype.card (Fin (finrank ℚ (W.rank.filtration.layer d.val 1))) : ℝ) ≤ Q := by
    simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hudim).trans (hdim.trans (hPa.trans haQ))
  have hv₀ : Submodule.span ℚ (Set.range (fun i => v i 0)) = fourFirstProjection J := by
    change _ = (D.coordinateSpace d f).map (LinearMap.proj 0)
    rw [← hv, Submodule.map_span, ← Set.range_comp]
    rfl
  have hdepSpan : Submodule.span ℚ (Set.range (fun i => (eD i : Fin m → ℚ))) =
      fourDependentProjection J := by
    change Submodule.span ℚ (Set.range ((fourDependentProjection J).subtype ∘ eD)) = _
    rw [Set.range_comp, ← Submodule.map_span, eD.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hc := exists_preimage_basis_logHeight W.model.basis (Pi.basisFun ℚ (Fin m))
    (W.rank.filtration.layer d.val 1) (fourFirstProjection J) T u (fun i => v i 0)
    hu hv₀ hQ (by simpa only [Fintype.card_fin] using hma.trans haQ) huQ (hcolsa.trans haQ)
    (fun i j => (huH i j).trans (hPa.trans haQ))
    (by simpa only [Pi.basisFun_repr] using fun i j => (hvH i 0 j).trans (hhora.trans haQ))
    (fun i j => (hTu i j).trans hpQ)
  have he := exists_preimage_basis_logHeight W.model.basis (Pi.basisFun ℚ (Fin m))
    (W.rank.filtration.layer d.val 1) (fourDependentProjection J) T u (fun i => (eD i : Fin m → ℚ))
    hu hdepSpan hQ (by simpa only [Fintype.card_fin] using hma.trans haQ) huQ
    (by simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hdepdim).trans (hma.trans haQ))
    (fun i j => (huH i j).trans (hPa.trans haQ))
    (by simpa only [Pi.basisFun_repr] using fun i j => (heD i j).trans hdQ)
    (fun i j => (hTu i j).trans hpQ)
  have hcspace : D.commonCoefficientSpace d =
      W.rank.filtration.layer d.val 1 ⊓ (fourFirstProjection J).comap T := by
    unfold commonCoefficientSpace
    rw [W.rank.filtration.horizontalPreimage_coordinates d.val f,
      ← D.coordinateSpace_first d f]
  have hespace : D.dependentCoefficientSpace d =
      W.rank.filtration.layer d.val 1 ⊓ (fourDependentProjection J).comap T := by
    unfold dependentCoefficientSpace
    rw [W.rank.filtration.horizontalPreimage_coordinates d.val f,
      ← D.coordinateSpace_dependent d f]
  rw [← hcspace] at hc
  rw [← hespace] at he
  obtain ⟨c, hc⟩ := hc
  obtain ⟨e, he⟩ := he
  exact ⟨c, hc, e, he⟩

end NativeRankRelation.CommonData
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

noncomputable def coefficientFourSpace (d : Fin (s + 1)) : Submodule ℚ (Fin 4 → W.L) :=
  ((D.horizontal d).comap (W.rank.filtration.fourHorizontalMap d.val)).map
    (W.rank.filtration.fourHorizontalLayer d.val).subtype

theorem coefficientFourSpace_le (d : Fin (s + 1)) :
    D.coefficientFourSpace d ≤ W.rank.filtration.fourHorizontalLayer d.val := by
  rintro v ⟨w, _, rfl⟩
  exact w.property

theorem mem_coefficientFourSpace (d : Fin (s + 1))
    (v : W.rank.filtration.fourHorizontalLayer d.val) :
    v.val ∈ D.coefficientFourSpace d ↔
      W.rank.filtration.fourHorizontalMap d.val v ∈ D.horizontal d := by
  constructor
  · rintro ⟨w, hw, he⟩
    have h : w = v := Subtype.ext he
    exact h ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem coefficient_four_frequency (n : ℕ) (d : Fin n → Fin (s + 1))
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun j => (d j).val) a = s)
    (hr : a.length = r) (v : Fin n → Fin 4 → W.L)
    (hv : ∀ j, v j ∈ D.coefficientFourSpace (d j)) :
    fourFunctionDifference (fun x => W.vertical.frequency (lieTreeEval x a)) v = 0 := by
  classical
  have hlift (j : Fin n) : ∃ w : W.rank.filtration.fourHorizontalLayer (d j).val,
      W.rank.filtration.fourHorizontalMap (d j).val w ∈ D.horizontal (d j) ∧ w.val = v j :=
    hv j
  choose w hw he using hlift
  have hvalue (k : Fin 4) :
      W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
          (fun j => W.rank.filtration.fourHorizontalMap (d j).val (w j) k) =
        lieTreeEval (fun j => v j k) a := by
    let u (j : Fin n) : W.rank.filtration.layer (d j).val 1 :=
      ⟨(w j).val k, (W.rank.filtration.mem_fourHorizontalLayer _ _).mp (w j).property k⟩
    change W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
      (fun j => W.rank.filtration.higherHorizontalMk (d j).val (u j)) = _
    rw [W.rank.filtration.horizontalTreeValue_mk _ a hd hr u]
    congr 1
    funext j
    exact congrFun (he j) k
  have h := D.horizontal_frequency n d a hd hr
    (fun j => W.rank.filtration.fourHorizontalMap (d j).val (w j)) hw
  simpa only [fourFunctionDifference, hvalue] using h

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

abbrev CoefficientFreeLieAlgebra :=
  FreeDegreeRankLieAlgebra D.CoefficientAlphabet s r D.coefficientWeight D.coefficientWeight_pos

noncomputable def coefficientFreeFiltration : DegreeRankLieFiltration D.CoefficientFreeLieAlgebra s r :=
  FreeDegreeRankLieAlgebra.filtration D.CoefficientAlphabet s r D.coefficientWeight
    D.coefficientWeight_pos W.rank.filtration.rank_le_degree

noncomputable def coefficientFreeGenerator (x : D.CoefficientAlphabet) : D.CoefficientFreeLieAlgebra :=
  FreeDegreeRankLieAlgebra.of D.CoefficientAlphabet s r D.coefficientWeight D.coefficientWeight_pos x

theorem coefficientFreeGenerator_mem_layer (x : D.CoefficientAlphabet) :
    D.coefficientFreeGenerator x ∈ D.coefficientFreeFiltration.layer (D.coefficientWeight x) 1 :=
  FreeDegreeRankLieAlgebra.of_mem_layer _ _ _ _ _ W.rank.filtration.rank_le_degree x

noncomputable def commonFreeSpan (d : Fin s) : Submodule ℚ D.CoefficientFreeLieAlgebra :=
  Submodule.span ℚ (Set.range (fun i => D.coefficientFreeGenerator (Sum.inl ⟨d, i⟩)))

noncomputable def dependentFreeSpan (d : Fin s) : Submodule ℚ D.CoefficientFreeLieAlgebra :=
  Submodule.span ℚ (Set.range (fun i => D.coefficientFreeGenerator (Sum.inr ⟨d, i⟩)))

theorem commonFreeSpan_le_layer (d : Fin s) :
    D.commonFreeSpan d ≤ D.coefficientFreeFiltration.layer (d.val + 1) 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact D.coefficientFreeGenerator_mem_layer (Sum.inl ⟨d, i⟩)

theorem dependentFreeSpan_le_layer (d : Fin s) :
    D.dependentFreeSpan d ≤ D.coefficientFreeFiltration.layer (d.val + 1) 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact D.coefficientFreeGenerator_mem_layer (Sum.inr ⟨d, i⟩)

variable {Q : ℝ} (B : D.CoefficientBases Q)

noncomputable def CoefficientBases.freeEvaluation : D.CoefficientFreeLieAlgebra →ₗ⁅ℚ⁆ W.L :=
  FreeDegreeRankLieAlgebra.lift W.rank.filtration D.coefficientWeight D.coefficientWeight_pos
    (B.generator D) (B.generator_mem_layer D)

theorem CoefficientBases.freeEvaluation_generator (x : D.CoefficientAlphabet) :
    B.freeEvaluation D (D.coefficientFreeGenerator x) = B.generator D x :=
  FreeDegreeRankLieAlgebra.lift_of _ _ _ _ _ x

noncomputable def CoefficientBases.commonFreeLift (d : Fin s) :
    D.commonCoefficientSpace ⟨d.val + 1, by omega⟩ →ₗ[ℚ] D.CoefficientFreeLieAlgebra :=
  (B.common d).constr ℚ (fun i => D.coefficientFreeGenerator (Sum.inl ⟨d, i⟩))

noncomputable def CoefficientBases.dependentFreeLift (d : Fin s) :
    D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩ →ₗ[ℚ] D.CoefficientFreeLieAlgebra :=
  (B.dependent d).constr ℚ (fun i => D.coefficientFreeGenerator (Sum.inr ⟨d, i⟩))

theorem CoefficientBases.commonFreeLift_range (d : Fin s) :
    LinearMap.range (B.commonFreeLift D d) = D.commonFreeSpan d :=
  (B.common d).constr_range ℚ

theorem CoefficientBases.dependentFreeLift_range (d : Fin s) :
    LinearMap.range (B.dependentFreeLift D d) = D.dependentFreeSpan d :=
  (B.dependent d).constr_range ℚ

theorem CoefficientBases.freeEvaluation_commonFreeLift (d : Fin s)
    (x : D.commonCoefficientSpace ⟨d.val + 1, by omega⟩) :
    B.freeEvaluation D (B.commonFreeLift D d x) = x.val := by
  have h : (B.freeEvaluation D).toLinearMap.comp (B.commonFreeLift D d) =
      (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).subtype := by
    apply (B.common d).ext
    intro i
    change B.freeEvaluation D ((B.common d).constr ℚ _ (B.common d i)) = _
    rw [Basis.constr_basis]
    exact B.freeEvaluation_generator D (Sum.inl ⟨d, i⟩)
  exact LinearMap.congr_fun h x

theorem CoefficientBases.freeEvaluation_dependentFreeLift (d : Fin s)
    (x : D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩) :
    B.freeEvaluation D (B.dependentFreeLift D d x) = x.val := by
  have h : (B.freeEvaluation D).toLinearMap.comp (B.dependentFreeLift D d) =
      (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).subtype := by
    apply (B.dependent d).ext
    intro i
    change B.freeEvaluation D ((B.dependent d).constr ℚ _ (B.dependent d i)) = _
    rw [Basis.constr_basis]
    exact B.freeEvaluation_generator D (Sum.inr ⟨d, i⟩)
  exact LinearMap.congr_fun h x

end Erdos3.NativeRankRelation.CommonData

end

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
  {Q : ℝ} (B : D.CoefficientBases Q)

noncomputable def CoefficientBases.realCommonFreeLift (d : Fin s) :
    (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ →ₗ[ℝ]
      ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra :=
  ((B.commonFreeLift D d).baseChange ℝ).comp
    (realificationSubmoduleEquiv (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩)).symm.toLinearMap

noncomputable def CoefficientBases.realDependentFreeLift (d : Fin s) :
    (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ →ₗ[ℝ]
      ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra :=
  ((B.dependentFreeLift D d).baseChange ℝ).comp
    (realificationSubmoduleEquiv (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩)).symm.toLinearMap

theorem CoefficientBases.realCommonFreeLift_baseChange (d : Fin s)
    (x : ℝ ⊗[ℚ] D.commonCoefficientSpace ⟨d.val + 1, by omega⟩) :
    B.realCommonFreeLift D d (realificationSubmoduleEquiv _ x) =
      (B.commonFreeLift D d).baseChange ℝ x :=
  congrArg ((B.commonFreeLift D d).baseChange ℝ)
    ((realificationSubmoduleEquiv _).symm_apply_apply x)

theorem CoefficientBases.realDependentFreeLift_baseChange (d : Fin s)
    (x : ℝ ⊗[ℚ] D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩) :
    B.realDependentFreeLift D d (realificationSubmoduleEquiv _ x) =
      (B.dependentFreeLift D d).baseChange ℝ x :=
  congrArg ((B.dependentFreeLift D d).baseChange ℝ)
    ((realificationSubmoduleEquiv _).symm_apply_apply x)

theorem CoefficientBases.realCommonFreeLift_mem (d : Fin s)
    (x : (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    B.realCommonFreeLift D d x ∈ (D.commonFreeSpan d).baseChange ℝ := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [B.realCommonFreeLift_baseChange]
  induction v using TensorProduct.inductionOn with
  | tmul a v =>
    rw [LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem a
      ((B.commonFreeLift_range D d).le ⟨v, rfl⟩)
  | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw

theorem CoefficientBases.realDependentFreeLift_mem (d : Fin s)
    (x : (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    B.realDependentFreeLift D d x ∈ (D.dependentFreeSpan d).baseChange ℝ := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [B.realDependentFreeLift_baseChange]
  induction v using TensorProduct.inductionOn with
  | tmul a v =>
    rw [LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem a
      ((B.dependentFreeLift_range D d).le ⟨v, rfl⟩)
  | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw

theorem CoefficientBases.realEvaluation_commonFreeLift (d : Fin s)
    (x : (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    realificationLieHom (B.freeEvaluation D) (B.realCommonFreeLift D d x) = x.val := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [B.realCommonFreeLift_baseChange, realificationSubmoduleEquiv_coe]
  change (B.freeEvaluation D).toLinearMap.baseChange ℝ
    ((B.commonFreeLift D d).baseChange ℝ v) = _
  induction v using TensorProduct.inductionOn with
  | tmul a v =>
    change a ⊗ₜ[ℚ] B.freeEvaluation D (B.commonFreeLift D d v) = a ⊗ₜ[ℚ] v.val
    rw [B.freeEvaluation_commonFreeLift]
  | add v w hv hw => simp only [map_add, hv, hw]

theorem CoefficientBases.realEvaluation_dependentFreeLift (d : Fin s)
    (x : (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    realificationLieHom (B.freeEvaluation D) (B.realDependentFreeLift D d x) = x.val := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [B.realDependentFreeLift_baseChange, realificationSubmoduleEquiv_coe]
  change (B.freeEvaluation D).toLinearMap.baseChange ℝ
    ((B.dependentFreeLift D d).baseChange ℝ v) = _
  induction v using TensorProduct.inductionOn with
  | tmul a v =>
    change a ⊗ₜ[ℚ] B.freeEvaluation D (B.dependentFreeLift D d v) = a ⊗ₜ[ℚ] v.val
    rw [B.freeEvaluation_dependentFreeLift]
  | add v w hv hw => simp only [map_add, hv, hw]

end Erdos3.NativeRankRelation.CommonData

end

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
  {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.freeEvaluation_commonFreeSpan (d : Fin s) :
    (D.commonFreeSpan d).map (B.freeEvaluation D).toLinearMap =
      D.commonCoefficientSpace ⟨d.val + 1, by omega⟩ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := (B.commonFreeLift_range D d).ge hy
    change B.freeEvaluation D (B.commonFreeLift D d z) ∈ _
    rw [B.freeEvaluation_commonFreeLift]
    exact z.property
  · intro hx
    refine ⟨B.commonFreeLift D d ⟨x, hx⟩,
      (B.commonFreeLift_range D d).le ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    exact B.freeEvaluation_commonFreeLift D d ⟨x, hx⟩

theorem CoefficientBases.freeEvaluation_dependentFreeSpan (d : Fin s) :
    (D.dependentFreeSpan d).map (B.freeEvaluation D).toLinearMap =
      D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := (B.dependentFreeLift_range D d).ge hy
    change B.freeEvaluation D (B.dependentFreeLift D d z) ∈ _
    rw [B.freeEvaluation_dependentFreeLift]
    exact z.property
  · intro hx
    refine ⟨B.dependentFreeLift D d ⟨x, hx⟩,
      (B.dependentFreeLift_range D d).le ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    exact B.freeEvaluation_dependentFreeLift D d ⟨x, hx⟩

theorem CoefficientBases.realEvaluation_commonFreeSpan (d : Fin s)
    {x : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra} (hx : x ∈ (D.commonFreeSpan d).baseChange ℝ) :
    realificationLieHom (B.freeEvaluation D) x ∈
      (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ := by
  rw [← B.freeEvaluation_commonFreeSpan D d, realification_map]
  exact ⟨x, hx, rfl⟩

theorem CoefficientBases.realEvaluation_dependentFreeSpan (d : Fin s)
    {x : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra} (hx : x ∈ (D.dependentFreeSpan d).baseChange ℝ) :
    realificationLieHom (B.freeEvaluation D) x ∈
      (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ := by
  rw [← B.freeEvaluation_dependentFreeSpan D d, realification_map]
  exact ⟨x, hx, rfl⟩

noncomputable def CoefficientBases.freeFrequency : D.CoefficientFreeLieAlgebra →ₗ[ℚ] ℚ :=
  W.vertical.frequency.comp (B.freeEvaluation D).toLinearMap

theorem CoefficientBases.free_sunflower (n : ℕ) (d : Fin n → Fin s) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (v : Fin n → D.CoefficientFreeLieAlgebra) (hv : ∀ i, v i ∈ D.commonFreeSpan (d i))
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ D.dependentFreeSpan (d j)) (hvk : v k ∈ D.dependentFreeSpan (d k)) :
    B.freeFrequency D (lieTreeEval v a) = 0 := by
  have h := D.coefficient_sunflower n (fun i => ⟨(d i).val + 1, by omega⟩) a hd hr
    (fun i => B.freeEvaluation D (v i))
    (fun i => (B.freeEvaluation_commonFreeSpan D (d i)).le ⟨v i, hv i, rfl⟩)
    j k hjk hj hk
    ((B.freeEvaluation_dependentFreeSpan D (d j)).le ⟨v j, hvj, rfl⟩)
    ((B.freeEvaluation_dependentFreeSpan D (d k)).le ⟨v k, hvk, rfl⟩)
  change W.vertical.frequency (B.freeEvaluation D (lieTreeEval v a)) = 0
  rw [map_lieTreeEval]
  exact h

theorem CoefficientBases.real_free_sunflower (n : ℕ) (d : Fin n → Fin s) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (v : Fin n → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ (D.commonFreeSpan (d i)).baseChange ℝ)
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ (D.dependentFreeSpan (d j)).baseChange ℝ)
    (hvk : v k ∈ (D.dependentFreeSpan (d k)).baseChange ℝ) :
    realifyFunctional (B.freeFrequency D) (lieTreeEval v a) = 0 := by
  have h := D.real_coefficient_sunflower n (fun i => ⟨(d i).val + 1, by omega⟩) a hd hr
    (fun i => realificationLieHom (B.freeEvaluation D) (v i))
    (fun i => B.realEvaluation_commonFreeSpan D (d i) (hv i))
    j k hjk hj hk
    (B.realEvaluation_dependentFreeSpan D (d j) hvj)
    (B.realEvaluation_dependentFreeSpan D (d k) hvk)
  change realifyFunctional (W.vertical.frequency.comp (B.freeEvaluation D).toLinearMap)
    (lieTreeEval v a) = 0
  rw [realifyFunctional_comp]
  exact (congrArg (realifyFunctional W.vertical.frequency)
    (map_lieTreeEval (realLieHomToRat (realificationLieHom (B.freeEvaluation D))) v a)).trans h

end Erdos3.NativeRankRelation.CommonData

end

end OAI
