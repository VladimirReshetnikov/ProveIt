import OAI.Combinatorics.Progressions.Estimates.AdaptedDiagramNativeExternalNet
import OAI.Combinatorics.Progressions.Geometry.AntisymmetricBoxPrecision
import OAI.Combinatorics.Progressions.Linear.BiasedChosenBasisStepDrop

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d e : ℕ}
  (D : RationalFilteredNilmanifold L s d)
  (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra U) s e)
  (hEF : E.filtration = D.filtration.gradedRefiltration U)
  (u : D.Space → ℂ)
  (hu : ∀ z : D.RealGroup,
    z.coord ∈ D.filtration.realGradedRefiltrationLayer U s → ∀ x, u (z • x) = u x)

include hEF hu in
theorem frozen_refiltered_top_invariant (a r : D.RealGroup)
    (z : E.RealGroup) (hz : z ∈ E.filtration.realification.subgroup s) (x : E.RealGroup) :
    u (QuotientGroup.mk (a * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra U).incl (z * x) * r)) =
    u (QuotientGroup.mk (a * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra U).incl x * r)) := by
  let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot)
    (D.filtration.gradedRefiltrationSubalgebra U).incl
  have hz' : (φ z).coord ∈ D.filtration.realGradedRefiltrationLayer U s := by
    apply (D.filtration.mem_native_refiltration_layer U s z.coord).mp
    have h : z.coord ∈ E.filtration.realification.layer s := hz
    simpa only [hEF] using h
  have hcomm := D.filtration.realification.top_commutes (φ z)
    (D.filtration.realGradedRefiltrationLayer_le U s hz') a
  have heq : a * φ (z * x) * r = φ z * (a * φ x * r) := by
    calc
      a * φ (z * x) * r = (a * φ z) * φ x * r := by simp only [map_mul, mul_assoc]
      _ = (φ z * a) * φ x * r := by rw [← hcomm.eq]
      _ = φ z * (a * φ x * r) := by simp only [mul_assoc]
  change u (QuotientGroup.mk (a * φ (z * x) * r)) = _
  rw [heq]
  exact hu (φ z) hz' (QuotientGroup.mk (a * φ x * r))

include hEF hu in
theorem frozen_refiltered_coset_invariant (a r : D.RealGroup)
    (h : ∀ γ ∈ E.realLattice,
      r⁻¹ * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra U).incl γ * r ∈ D.realLattice)
    (z : E.RealGroup) (hz : z ∈ E.filtration.realification.subgroup s) (x : E.Space) :
    (u ∘ frozenCosetMap E.realLattice D.realLattice
      (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra U).incl) a r h) (z • x) =
    (u ∘ frozenCosetMap E.realLattice D.realLattice
      (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra U).incl) a r h) x := by
  induction x using Quotient.inductionOn with
  | h x => exact D.frozen_refiltered_top_invariant U E hEF u hu a r z hz x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_real_module_topology {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V] (b : Basis ι ℚ V) :
    ∃ τ : TopologicalSpace (ℝ ⊗[ℚ] V),
      letI := τ
      IsTopologicalAddGroup (ℝ ⊗[ℚ] V) ∧ ContinuousSMul ℝ (ℝ ⊗[ℚ] V) ∧ T2Space (ℝ ⊗[ℚ] V) := by
  let τ := moduleTopology ℝ (ℝ ⊗[ℚ] V)
  let : TopologicalSpace (ℝ ⊗[ℚ] V) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] V) := (b.baseChange ℝ).finiteDimensional_of_finite
  have hc : Continuous (b.baseChange ℝ).equivFun :=
    IsModuleTopology.continuous_of_linearMap (b.baseChange ℝ).equivFun.toLinearMap
  let : T2Space (ℝ ⊗[ℚ] V) := T2Space.of_injective_continuous (b.baseChange ℝ).equivFun.injective hc
  exact ⟨τ, inferInstance, inferInstance, inferInstance⟩

namespace RationalFilteredNilmanifold.Niltest

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem symbol_of_native (T : D.Niltest w) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (g : D.filtration.RealAdaptedPolynomialGroup w) (hg : D.filtration.nativePolynomialOrbit w g = T.orbit) :
    T.symbol b ω hF = D.filtration.realPolynomialSymbolHom b ω hF w
      (D.filtration.realAdaptedPolynomialGroupHom w g) := by
  have he := congrArg (fun a : D.filtration.realification.PolynomialOrbit w =>
    D.filtration.realPolynomialSymbolHom b ω hF w ⟨⟨a.log, a.property⟩⟩) hg
  exact he.symm

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3.NativeAntisymmetricOrbitFactors

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p q : ℝ} {N e : ℕ}
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
  (V : NativeAntisymmetricOrbitFactors W N q)
  [TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))] [T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]

theorem frozen_coset_top_invariant
    (E : RationalFilteredNilmanifold
      ((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra)
      (∑ k, mixedCorrelationDegree 1 k) e)
    (hEF : E.filtration = (pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltration V.subalgebra)
    (hp : 0 ≤ p) (a r : (pi (fun _ : Fin 8 => W.model)).RealGroup)
    (h : ∀ γ ∈ E.realLattice,
      r⁻¹ * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := (pi (fun _ : Fin 8 => W.model)).filtration.lowerCentralSeries_eq_bot)
        ((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra).incl
        γ * r ∈ (pi (fun _ : Fin 8 => W.model)).realLattice)
    (z : E.RealGroup) (hz : z ∈ E.filtration.realification.subgroup (∑ k, mixedCorrelationDegree 1 k))
    (x : E.Space) :
    ((W.antisymmetricBoxNiltest hp V.leftIndex V.rightIndex).observable ∘
      frozenCosetMap E.realLattice (pi (fun _ : Fin 8 => W.model)).realLattice
        (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
          (hM := (pi (fun _ : Fin 8 => W.model)).filtration.lowerCentralSeries_eq_bot)
          ((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra).incl)
        a r h) (z • x) =
    ((W.antisymmetricBoxNiltest hp V.leftIndex V.rightIndex).observable ∘
      frozenCosetMap E.realLattice (pi (fun _ : Fin 8 => W.model)).realLattice
        (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
          (hM := (pi (fun _ : Fin 8 => W.model)).filtration.lowerCentralSeries_eq_bot)
          ((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra).incl)
        a r h) x := by
  exact (pi (fun _ : Fin 8 => W.model)).frozen_refiltered_coset_invariant V.subalgebra E hEF
    (W.antisymmetricBoxNiltest hp V.leftIndex V.rightIndex).observable
    (fun z hz x => V.top_layer_invariant hp z hz x) a r h z hz x

end Erdos3.NativeAntisymmetricOrbitFactors

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem NativeAntisymmetricOrbitFactors.frozen_group_invariant {p : ℝ}
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {N e : ℕ}
    (V : NativeAntisymmetricOrbitFactors W N p)
    [TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))] [T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]
    (E : RationalFilteredNilmanifold
      ((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra) 2 e)
    (hEF : E.filtration = (pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltration V.subalgebra)
    (hp : 0 ≤ p) (a r : (pi (fun _ : Fin 8 => W.model)).RealGroup)
    (z : E.RealGroup) (hz : z ∈ E.filtration.realification.subgroup 2) (x : E.RealGroup) :
    (W.antisymmetricBoxNiltest hp V.leftIndex V.rightIndex).observable (QuotientGroup.mk
      (a * NilpotentLieBCHGroup.realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := (pi (fun _ : Fin 8 => W.model)).filtration.lowerCentralSeries_eq_bot)
        ((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra).incl
        (z * x) * r)) =
    (W.antisymmetricBoxNiltest hp V.leftIndex V.rightIndex).observable (QuotientGroup.mk
      (a * NilpotentLieBCHGroup.realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := (pi (fun _ : Fin 8 => W.model)).filtration.lowerCentralSeries_eq_bot)
        ((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra).incl
        x * r)) := by
  exact (pi (fun _ : Fin 8 => W.model)).frozen_refiltered_top_invariant V.subalgebra E hEF
    (W.antisymmetricBoxNiltest hp V.leftIndex V.rightIndex).observable
    (fun z hz x => V.top_layer_invariant hp z hz x) a r z hz x

theorem exists_prepared_antisymmetric_descent :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      {N : ℕ} (V : NativeAntisymmetricOrbitFactors W N p)
      [TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))] [T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]
      [TopologicalSpace (ℝ ⊗[ℚ]
        (pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ]
        (pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ]
        (pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra)]
      [T2Space (ℝ ⊗[ℚ]
        (pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra)]
      {e : ℕ} (E : RationalFilteredNilmanifold
        ((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra) 2 e)
      (g : E.filtration.realification.PolynomialOrbit (fun _ : Fin 4 => 1)),
      E.filtration = (pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltration V.subalgebra →
      (∀ x : Fin 4 → ℤ,
        NilpotentLieBCHGroup.realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
          (hM := (pi (fun _ : Fin 8 => W.model)).filtration.lowerCentralSeries_eq_bot)
          ((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra).incl
          (E.filtration.realification.polynomialOrbitEval (fun _ => 1) x g) =
        (pi (fun _ : Fin 8 => W.model)).filtration.adaptedPolynomialRealValueHom
          (fun _ : Fin 4 => 1) (fun i => (x i : ℝ)) V.middle) →
      ∀ (hp : 0 ≤ p) {t : ℝ}, 0 ≤ t → E.GeometryComplexityLE t →
      (W.antisymmetricBoxNiltest hp V.leftIndex V.rightIndex).ComplexityLE t →
      (∀ i j, rationalLogHeight ((pi (fun _ : Fin 8 => W.model)).basis.repr
        (E.basis j : Fin 8 → W.L) i) ≤ t) →
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp t →
      (∀ x : Fin 4 → ℤ, ((pi (fun _ : Fin 8 => W.model)).basis.baseChange ℝ).equivFun
        ((pi (fun _ : Fin 8 => W.model)).filtration.adaptedPolynomialRealValueHom
          (fun _ : Fin 4 => 1) (fun i => (x i : ℝ)) V.rational).coord ∈ realDenominatorGrid m) →
      (∀ x : Fin 4 → ℤ, (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → ∀ i,
        |((pi (fun _ : Fin 8 => W.model)).basis.baseChange ℝ).repr
          ((pi (fun _ : Fin 8 => W.model)).filtration.adaptedPolynomialRealValueHom
            (fun _ : Fin 4 => 1) (fun j => (x j : ℝ)) V.slow).coord i| ≤ Real.exp t) →
      Nonempty (NativeAntisymmetricFrozenDescent V ((t + K) ^ K)) := by
  obtain ⟨K, hK, hdesc⟩ := exists_uniform_frozen_descent 1 1
  refine ⟨K, hK, ?_⟩
  intro p W N V _ _ _ _ _ _ _ _ e E g hEF hg hp t ht hE hT hinc m hm hmb hrat hslow
  let D := pi (fun _ : Fin 8 => W.model)
  let T := W.antisymmetricBoxNiltest hp V.leftIndex V.rightIndex
  have htK : t ≤ (t + K) ^ K := by
    have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
    apply (le_add_of_nonneg_right (Nat.cast_nonneg K) : t ≤ t + K).trans
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ t + K)
      (show 1 ≤ K by omega)
  obtain ⟨_Λ, _hΛ, _hchar, _hnormal, _hfinite, _hindex, n, _hn, Q, hQF, _hQL, hQ, hfamily⟩ :=
    hdesc E D (D.filtration.gradedRefiltrationSubalgebra V.subalgebra).incl T g ht hE hT hinc m hm hmb
  let : TopologicalSpace (ℝ ⊗[ℚ]
      (D.filtration.gradedRefiltrationSubalgebra V.subalgebra ⧸ E.filtration.layerIdeal 2)) :=
    moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      (D.filtration.gradedRefiltrationSubalgebra V.subalgebra ⧸ E.filtration.layerIdeal 2)) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  refine ⟨{
    nonnegative := hp
    productTopology := inferInstance
    productTopologicalAdd := inferInstance
    productContinuousSMul := inferInstance
    productHausdorff := inferInstance
    outerBudget := t
    outer_nonnegative := ht
    outer_bound := htK
    denominator := m
    denominator_pos := hm
    denominator_bound := hmb
    rational_values := hrat
    slow_values := hslow
    L := D.filtration.gradedRefiltrationSubalgebra V.subalgebra ⧸ E.filtration.layerIdeal 2
    lie := inferInstance
    algebra := inferInstance
    dim := n
    topology := moduleTopology ℝ _
    topologicalAdd := IsModuleTopology.isTopologicalAddGroup ℝ _
    continuousSMul := inferInstance
    hausdorff := realification_moduleTopology_t2 Q.basis
    model := Q
    model_complexity := hQ
    orbit := E.topQuotientOrbit Q hQF g
    descend := ?_ }⟩
  intro a r ha hr
  have ha' : ∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((t + 2) ^ 1) :=
    fun i => (ha i).trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  have hinv := V.frozen_group_invariant E hEF hp a r
  have hS := hfamily a r ha' hr hinv
  obtain ⟨S, hSo, hSn, hSc, hSe⟩ := hS
  refine ⟨S, hSo, hSn, hSc, ?_⟩
  intro x
  exact (hSe x).trans (congrArg
    (fun z : D.RealGroup => T.observable (QuotientGroup.mk (a * z * r))) (hg x))

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_antisymmetric_frozen_descent :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      {N : ℕ} [NeZero N] (V : NativeAntisymmetricOrbitFactors W N p), 0 ≤ p →
      Nonempty (NativeAntisymmetricFrozenDescent V ((p + C) ^ C)) := by
  obtain ⟨A, _, hmodel⟩ := exists_antisymmetric_middle_model
  obtain ⟨B, _, houter⟩ := exists_antisymmetric_outer_bounds
  obtain ⟨K, _, hprepare⟩ := exists_prepared_antisymmetric_descent
  let X : Polynomial ℕ := Polynomial.X
  let Y := X + 8
  let P := (Y + 2) ^ 2 + Y + (Y + (Y ^ 2 + Y + 3) ^ 2) + Y ^ 2 + 4
  let T := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B + P + X + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro p W N _ V hp
  let D := pi (fun _ : Fin 8 => W.model)
  obtain ⟨E, hEF, _hEL, hE, hinc, g, hg⟩ := hmodel W V hp
  obtain ⟨m, hm, hmb, hrat, hslow⟩ := houter W V hp
  obtain ⟨τ, htA, htM, htT⟩ := exists_real_module_topology D.basis
  let : TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L)) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L)) := htA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L)) := htM
  let : T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L)) := htT
  obtain ⟨σ, hsA, hsM, hsT⟩ := exists_real_module_topology E.basis
  let : TopologicalSpace
      (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra V.subalgebra) := σ
  let : IsTopologicalAddGroup
      (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra V.subalgebra) := hsA
  let : ContinuousSMul ℝ
      (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra V.subalgebra) := hsM
  let : T2Space
      (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra V.subalgebra) := hsT
  let T₀ := W.antisymmetricBoxNiltest hp V.leftIndex V.rightIndex
  let t := (p + A) ^ A + (p + B) ^ B + productNiltestBudget (p + 8) + p + 4
  have hprod : 0 ≤ productNiltestBudget (p + 8) := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hA : 0 ≤ (p + A) ^ A := by positivity
  have hB : 0 ≤ (p + B) ^ B := by positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := by dsimp [t]; linarith
  have hBt : (p + B) ^ B ≤ t := by dsimp [t]; linarith
  have hPt : productNiltestBudget (p + 8) ≤ t := by dsimp [t]; linarith
  have hT₀ : T₀.ComplexityLE t :=
    (W.antisymmetricBoxNiltest_complexity hp V.leftIndex V.rightIndex).mono hPt
  have hsum : t + (t + K) ^ K ≤ (p + C) ^ C := by
    simpa [T, P, Y, X, t, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget p hp
  have hcost : (t + K) ^ K ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  obtain ⟨R⟩ := hprepare W V E g hEF hg hp ht (hE.mono E hAt) hT₀
    (fun i j => (hinc j i).trans hAt) m hm (hmb.trans (Real.exp_le_exp.mpr hBt))
    hrat (fun x hx i => (hslow x hx i).trans (Real.exp_le_exp.mpr hBt))
  exact ⟨R.mono hcost⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

namespace NativePolynomialOrbitFactors

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}
  {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
  {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}

noncomputable def frozenMiddleValue (R : NativePolynomialOrbitFactors D g eta A p)
    (a r : D.RealGroup) (x : σ → ℤ) : D.RealGroup :=
  a * D.filtration.adaptedPolynomialRealValueHom
    (fun _ : σ => 1) (fun i => (x i : ℝ)) R.middle * r

end NativePolynomialOrbitFactors

theorem exists_native_frozen_middle_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      {g : (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p)
      (T : D.Niltest (fun _ : σ => 1)), 0 ≤ p → T.ComplexityLE p →
      (∀ z : D.RealGroup,
        z.coord ∈ D.filtration.realGradedRefiltrationLayer R.subalgebra (s + 1) →
        ∀ x, T.observable (z • x) = T.observable x) →
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp p → ∀ a r : D.RealGroup,
        (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp p) →
        (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m →
        Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C)
          (fun x => T.observable (QuotientGroup.mk (R.frozenMiddleValue a r x)))) := by
  obtain ⟨B, _, hmodel⟩ := exists_native_middle_model
  obtain ⟨K, _, hdesc⟩ := exists_uniform_frozen_descent s 1
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + Polynomial.C B) ^ B + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ d D g eta A p R T hp hT hinv m hm hmb a r ha hr
  obtain ⟨E, hEF, _hEL, hE, hinc, h, hh⟩ := hmodel D R hp hT.1
  let : TopologicalSpace (ℝ ⊗[ℚ]
      D.filtration.gradedRefiltrationSubalgebra R.subalgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      D.filtration.gradedRefiltrationSubalgebra R.subalgebra) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  let t := p + (p + B) ^ B + 4
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith [pow_nonneg (by positivity : 0 ≤ p + B) B]
  have hEt : (p + B) ^ B ≤ t := by dsimp [t]; linarith
  obtain ⟨_Λ, _hΛ, _hchar, _hnormal, _hfinite, _hindex,
      n, _hn, Q, hQF, _hQL, _hQ, hfamily⟩ :=
    hdesc E D (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl T h ht
      (hE.mono E hEt) (hT.mono hpt) (fun i j => (hinc j i).trans hEt)
      m hm (hmb.trans (Real.exp_le_exp.mpr hpt))
  let : TopologicalSpace (ℝ ⊗[ℚ]
      (D.filtration.gradedRefiltrationSubalgebra R.subalgebra ⧸
        E.filtration.layerIdeal (s + 1))) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      (D.filtration.gradedRefiltrationSubalgebra R.subalgebra ⧸
        E.filtration.layerIdeal (s + 1))) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  have ha' : ∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((t + 2) ^ 1) :=
    fun i => (ha i).trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  obtain ⟨S, _hSo, _hSn, hSc, hSe⟩ := hfamily a r ha' hr
    (D.frozen_refiltered_top_invariant R.subalgebra E hEF T.observable hinv a r)
  have hcost : (t + K) ^ K ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨NativeIntegerExpansion.ofTest S (hSc.mono hcost) ?_⟩
  intro x
  exact ((hSe x).trans (congrArg
    (fun z : D.RealGroup => T.observable (QuotientGroup.mk (a * z * r))) (hh x))).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_antisymmetric_orbit_approximation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p r : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      (V : NativeAntisymmetricOrbitFactors W N p),
      0 ≤ p → 0 ≤ r → Real.exp ((p + r + C) ^ C) ≤ (N : ℝ) →
      ∃ F : (Fin 4 → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Fin 4 => 1) 1 ((p + r + C) ^ C) F) ∧
        (𝔼 x : Fin 4 → ZMod N,
          ‖W.antisymmetricBoxValue V.leftIndex V.rightIndex (fun i => ((x i).val : ℤ)) -
            F (fun i => ((x i).val : ℤ))‖) ≤ Real.exp (-r) := by
  obtain ⟨A, _, hdescent⟩ := exists_antisymmetric_frozen_descent
  obtain ⟨B, _, hlocal⟩ := exists_antisymmetric_local_models
  obtain ⟨C, _, hprecise⟩ := exists_antisymmetric_box_approximation
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + X + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro N _ p r W V hp hr hN
  let t := (p + A) ^ A + (p + B) ^ B
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpr : p ≤ p + r := le_add_of_nonneg_right hr
  have htbound : t ≤ (p + r + A) ^ A + (p + r + B) ^ B := by
    dsimp [t]
    gcongr
  have hbig : ((p + r + A) ^ A + (p + r + B) ^ B + (p + r) + C) ^ C ≤
      (p + r + D) ^ D := by
    simpa [T, X, Polynomial.eval₂_pow] using hbudget (p + r) (add_nonneg hp hr)
  have hcost : (t + r + C) ^ C ≤ (p + r + D) ^ D :=
    (pow_le_pow_left₀ (by positivity) (by linarith) C).trans hbig
  obtain ⟨R⟩ := hdescent W V hp
  obtain ⟨P, hP, hPb, hmodels⟩ := hlocal R
  let L : NativeAntisymmetricLocalModels R ((p + B) ^ B) := {
    period := P
    period_pos := hP
    period_bound := hPb
    local_model := hmodels }
  have hqt : (p + A) ^ A ≤ t := le_add_of_nonneg_right (by positivity)
  have hbt : (p + B) ^ B ≤ t := le_add_of_nonneg_left (by positivity)
  obtain ⟨F, ⟨E⟩, herr⟩ := hprecise R L ht hr hqt hbt
    ((Real.exp_le_exp.mpr hcost).trans hN)
  exact ⟨F, ⟨E.mono hcost⟩, herr⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

universe uσ uL

theorem exists_translated_step_drop_succ (s c : ℕ) (hs : 1 ≤ s)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ TranslatedStepDropSpec.{uσ, uL} (s + 1) C := by
  obtain ⟨a, _, hchosen⟩ := exists_biased_chosen_basis_step_drop s c hI
  obtain ⟨b, _, hchange⟩ := exists_controlled_symbol_basis_change (s + 1)
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let U : Polynomial ℕ := B + Polynomial.X + 3
  let P : Polynomial ℕ := B + U + (U + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d _ _ _ _ D ν hD p hp hσ T hT η _hη hvertical origin lengths hlengths hlarge hbias
  let k : ℝ := (p + a) ^ a
  let u : ℝ := k + p + 3
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hku : k ≤ u := by dsimp [u]; linarith
  have hpu : p ≤ u := by dsimp [u]; linarith
  have hp2u : p + 2 ≤ u := by dsimp [u]; linarith
  have hlast : 0 ≤ (u + b) ^ b := by positivity
  have hbound : k + u + (u + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, U, B, k, u, Polynomial.eval₂_pow] using hfinal p hp
  have hkC : k ≤ (p + C) ^ C := by linarith
  have hbC : (u + b) ^ b ≤ (p + C) ^ C := by linarith
  obtain ⟨τS, hSA, hSM, hST⟩ := exists_real_module_topology
    (D.filtration.squareFinBasis D.basis ν (hD 2))
  let : TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := τS
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hSA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hSM
  let : T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hST
  obtain ⟨τQ, hQA, hQM, hQT⟩ := exists_real_module_topology
    (D.filtration.reducedSquareBasis D.basis ν hD)
  let : TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1))) := τQ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1))) := hQA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1))) := hQM
  let : T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1))) := hQT
  obtain ⟨e, ω, hF, _N, _hN, _hin, _hout, he, _hgeometry, hconstruct⟩ := hchosen hs D p hp T hT
  obtain ⟨g, hg⟩ := D.filtration.nativePolynomialOrbit_surjective (fun _ : σ => 1) D.basis ν hD T.orbit
  have hTpos : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  have hfactor := hconstruct g hg η hvertical origin lengths hlengths hσ
    (fun i => (Real.exp_le_exp.mpr hkC).trans (hlarge i)) hbias
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp (p + 1)
  have hHp : (H : ℝ) ≤ Real.exp u := by
    have he := ceil_exp_le_exp_add_one (show 0 ≤ p + 1 by linarith)
    exact he.trans (Real.exp_le_exp.mpr (by linarith))
  have hdim : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ u := by
    rw [Fintype.card_fin, finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hT.1.1.trans hpu
  have hd : (Fintype.card (Fin d) : ℝ) ≤ u := by
    simpa only [Fintype.card_fin] using hT.1.1.trans hpu
  have hentries : ∀ i j, RationalHeightLE (D.basis.repr (e i) j) H :=
    fun i j => rationalHeightLE_ceil_exp (he i j)
  have hfactor' := ControlledSymbolFactorization.mono D.filtration e ω hF hfactor hku hTpos
  have hdeclared := hchange D.filtration e ω hF D.basis ν hD H u hH hu hdim hd (hσ.trans hpu)
    hHp hentries (fun i => (lengths i : ℝ)) hTpos η _ hfactor'
  have hsym : D.filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
      (D.filtration.realAdaptedPolynomialGroupHom (fun _ => 1) g) = T.symbol D.basis ν hD := by
    exact (D.filtration.native_symbol_basis_independent e ω hF D.basis ν hD (fun _ => 1) g).symm.trans
      (T.symbol_of_native D.basis ν hD g hg).symm
  rw [hsym] at hdeclared
  exact ControlledSymbolFactorization.mono D.filtration D.basis ν hD hdeclared hbC hTpos

theorem exists_translated_step_drop (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ TranslatedStepDropSpec.{uσ, uL} s C := by
  have h : ∀ n : ℕ, ∃ C : ℕ, 2 ≤ C ∧ TranslatedStepDropSpec.{uσ, uL} (n + 1) C := by
    intro n
    induction n with
    | zero => exact ⟨4, by decide, translatedStepDropSpec_one⟩
    | succ n ih =>
      obtain ⟨C, _hC, hI⟩ := ih
      exact exists_translated_step_drop_succ (n + 1) C (by omega) hI
  cases s with
  | zero => omega
  | succ n => exact h n

end Erdos3

end

end OAI
