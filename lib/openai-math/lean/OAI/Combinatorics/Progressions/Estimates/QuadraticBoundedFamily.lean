/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.NativeCorrelationCoordinates
import OAI.Combinatorics.Progressions.Lattices.QuadraticMarkedAffine

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {ι σ : Type*} [Fintype ι] [Fintype σ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ} {bound : σ → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (M : ∀ i, (D i).MultidegreeStructure bound)

noncomputable def productMultidegreeLayerBasis (a : ∀ j, Fin (bound j + 1)) :
    Basis (Σ i, Fin (finrank ℚ ((M i).filtration.layer (fun j => (a j).val)))) ℚ
      ((MultidegreeLieFiltration.pi (fun i => (M i).filtration)).layer (fun j => (a j).val)) :=
  (Pi.basis (fun i => (M i).basis a)).map
    (MultidegreeLieFiltration.piLayerEquiv (fun i => (M i).filtration) (fun j => (a j).val))

noncomputable def productMultidegreeLayerFinBasis (a : ∀ j, Fin (bound j + 1)) :
    Basis (Fin (finrank ℚ
      ((MultidegreeLieFiltration.pi (fun i => (M i).filtration)).layer (fun j => (a j).val)))) ℚ
      ((MultidegreeLieFiltration.pi (fun i => (M i).filtration)).layer (fun j => (a j).val)) :=
  (productMultidegreeLayerBasis D M a).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis (productMultidegreeLayerBasis D M a)).symm)

noncomputable def piMultidegree : (pi D).MultidegreeStructure bound where
  filtration := MultidegreeLieFiltration.pi (fun i => (M i).filtration)
  ordinary := congrArg NilpotentLieFiltration.pi (funext (fun i => (M i).ordinary))
  basis := productMultidegreeLayerFinBasis D M

theorem productMultidegreeLayerBasis_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hM : ∀ i, (M i).ComplexityLE p) (a : ∀ j, Fin (bound j + 1))
    (j : Σ i, Fin (finrank ℚ ((M i).filtration.layer (fun k => (a k).val))))
    (k : Σ i, Fin (d i)) :
    rationalLogHeight ((Pi.basis (fun i => (D i).basis)).repr
      ((productMultidegreeLayerBasis D M a j).val) k) ≤ p := by
  classical
  rcases j with ⟨j, m⟩
  rcases k with ⟨k, n⟩
  simp only [productMultidegreeLayerBasis, Basis.map_apply, Pi.basis_repr]
  change rationalLogHeight ((D k).basis.repr
    (((Pi.basis (fun i => (M i).basis a)) ⟨j, m⟩ k).val) n) ≤ p
  rw [Pi.basis_apply]
  by_cases hjk : j = k
  · subst k
    rw [Pi.single_eq_same]
    exact (hM j).2 a m n
  · rw [Pi.single_eq_of_ne (Ne.symm hjk)]
    simpa [rationalLogHeight] using hp

theorem piMultidegree_complexity {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hM : ∀ i, (M i).ComplexityLE p) :
    (piMultidegree D M).ComplexityLE ((p + 2) ^ 2) := by
  refine ⟨pi_geometry D hp hι (fun i => (hM i).1), ?_⟩
  intro a j k
  change Fin (finrank ℚ
    ((MultidegreeLieFiltration.pi (fun i => (M i).filtration)).layer (fun i => (a i).val))) at j
  change rationalLogHeight ((productFinBasis D).repr
    ((productMultidegreeLayerFinBasis D M a j).val) k) ≤ (p + 2) ^ 2
  rw [productFinBasis, Basis.repr_reindex_apply, productMultidegreeLayerFinBasis, Basis.reindex_apply]
  exact (productMultidegreeLayerBasis_logHeight D M hp hM a _ _).trans (by nlinarith [sq_nonneg p])

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

theorem exists_bounded_multidegree_product_family
    {ι σ : Type*} [Fintype ι] [Fintype σ] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ} {bound : σ → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (M : ∀ i, (D i).MultidegreeStructure bound)
    (g : ∀ i, (M i).filtration.realification.PolynomialOrbit)
    {I : ι → Type*} (V : ∀ i, I i → (D i).Space → ℂ) {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hM : ∀ i, (M i).ComplexityLE p)
    (hV : ∀ i j x, ‖V i j x‖ ≤ 1)
    (hLip : ∀ i, letI := (D i).metricSpace;
      ∀ j, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V i j)) :
    (piMultidegree D M).ComplexityLE (productNiltestBudget (p + 4)) ∧
    ∃ T : (∀ i, I i) → (pi D).Niltest (fun _ : σ => 1),
      (∀ j, (T j).orbit = (piMultidegree D M).orbitToOrdinary
        (MultidegreeLieFiltration.piRealOrbit (fun i => (M i).filtration) g)) ∧
      (∀ j, (T j).normBound = 1) ∧
      (∀ j, (T j).ComplexityLE (productNiltestBudget (p + 4))) ∧
      (∀ j x, (T j).observable x = ∏ i, V i (j i) (productProjection D i x)) ∧
      ∀ j x, (T j).eval x =
        ∏ i, V i (j i) (QuotientGroup.mk ((M i).filtration.realification.polynomialOrbitEval x (g i))) := by
  classical
  have hpq : p ≤ p + 4 := by linarith
  have hq : 0 ≤ p + 4 := by linarith
  let K (i : ι) (j : I i) : (D i).Niltest (fun _ : σ => 1) := {
    orbit := (M i).orbitToOrdinary (g i)
    observable := V i j
    normBound := 1
    lipBound := ⟨Real.exp p, Real.exp_nonneg _⟩
    norm_le := hV i j
    lipschitz := hLip i j
  }
  have hK (i : ι) (j : I i) : (K i j).ComplexityLE (p + 4) := by
    refine ⟨(hM i).1.mono (D i) hpq, ?_⟩
    change Real.log (2 + 1 + Real.exp p) ≤ p + 4
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    calc
      _ ≤ 4 * Real.exp p := by linarith [Real.one_le_exp hp]
      _ ≤ Real.exp 4 * Real.exp p := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  let o := (piMultidegree D M).orbitToOrdinary
    (MultidegreeLieFiltration.piRealOrbit (fun i => (M i).filtration) g)
  let T (j : ∀ i, I i) := (unitBoundedPiNiltest D (fun i => K i (j i)) hq (hι.trans hpq)
    (fun i => hK i (j i)) (fun _ => le_rfl)).withOrbit o
  refine ⟨(piMultidegree_complexity D M hq (hι.trans hpq)
      (fun i => (hM i).mono (M i) hpq)).mono _ (productNiltestBudget_geometry hq),
    T, (fun _ => rfl), (fun _ => rfl),
    (fun j => unitBoundedPiNiltest_complexity D (fun i => K i (j i)) hq (hι.trans hpq)
      (fun i => hK i (j i)) (fun _ => le_rfl)),
    (fun _ _ => rfl), ?_⟩
  intro j x
  change (∏ i, V i (j i) (productProjection D i
    (QuotientGroup.mk ((pi D).filtration.realification.polynomialOrbitEval (fun _ : σ => 1) x o)))) = _
  apply Finset.prod_congr rfl
  intro i _
  rw [productProjection_mk]
  apply congrArg (fun z : (D i).RealGroup => V i (j i) (QuotientGroup.mk z))
  exact (congrArg (productProjectionHom D i)
    ((piMultidegree D M).orbitToOrdinary_eval
      (MultidegreeLieFiltration.piRealOrbit (fun i => (M i).filtration) g) x)).trans
        (MultidegreeLieFiltration.piRealOrbit_eval (fun i => (M i).filtration) g x i)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

def HasBoundedBinaryMultidegreeFamily
    {σ I J : Type*} {L₀ L₁ : Type u} [Fintype σ]
    [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing L₁] [LieAlgebra ℚ L₁]
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
    [TopologicalSpace (ℝ ⊗[ℚ] L₁)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [T2Space (ℝ ⊗[ℚ] L₁)]
    {s d₀ d₁ : ℕ} {bound : σ → ℕ}
    (D₀ : RationalFilteredNilmanifold L₀ s d₀) (D₁ : RationalFilteredNilmanifold L₁ s d₁)
    (M₀ : D₀.MultidegreeStructure bound) (M₁ : D₁.MultidegreeStructure bound)
    (g₀ : M₀.filtration.realification.PolynomialOrbit) (g₁ : M₁.filtration.realification.PolynomialOrbit)
    (V₀ : I → D₀.Space → ℂ) (V₁ : J → D₁.Space → ℂ) (p : ℝ) : Prop :=
    let P := optionProduct D₀ (fun _ : Unit => D₁)
    ∃ M : P.MultidegreeStructure bound, M.ComplexityLE (productNiltestBudget (p + 4)) ∧
      ∃ g : M.filtration.realification.PolynomialOrbit,
        (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace L₀ (fun _ : Unit => L₁) i))
         letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace L₀ (fun _ : Unit => L₁) i)) :=
            IsModuleTopology.isTopologicalAddGroup ℝ _
         letI := realification_moduleTopology_t2 P.basis
         ∃ T : I × J → P.Niltest (fun _ : σ => 1),
           (∀ ij, (T ij).orbit = M.orbitToOrdinary g) ∧
           (∀ ij, (T ij).normBound = 1) ∧
           (∀ ij, (T ij).ComplexityLE (productNiltestBudget (p + 4))) ∧
           ∀ ij x, (T ij).eval x =
             V₀ ij.1 (QuotientGroup.mk (M₀.filtration.realification.polynomialOrbitEval x g₀)) *
             V₁ ij.2 (QuotientGroup.mk (M₁.filtration.realification.polynomialOrbitEval x g₁)))

theorem exists_bounded_binary_multidegree_family
    {σ I J : Type*} {L₀ L₁ : Type u} [Fintype σ]
    [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing L₁] [LieAlgebra ℚ L₁]
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
    [TopologicalSpace (ℝ ⊗[ℚ] L₁)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [T2Space (ℝ ⊗[ℚ] L₁)]
    {s d₀ d₁ : ℕ} {bound : σ → ℕ}
    (D₀ : RationalFilteredNilmanifold L₀ s d₀) (D₁ : RationalFilteredNilmanifold L₁ s d₁)
    (M₀ : D₀.MultidegreeStructure bound) (M₁ : D₁.MultidegreeStructure bound)
    (g₀ : M₀.filtration.realification.PolynomialOrbit) (g₁ : M₁.filtration.realification.PolynomialOrbit)
    (V₀ : I → D₀.Space → ℂ) (V₁ : J → D₁.Space → ℂ) {p : ℝ}
    (hp : 2 ≤ p) (hM₀ : M₀.ComplexityLE p) (hM₁ : M₁.ComplexityLE p)
    (hV₀ : ∀ i x, ‖V₀ i x‖ ≤ 1) (hV₁ : ∀ j x, ‖V₁ j x‖ ≤ 1)
    (hLip₀ : letI := D₀.metricSpace; ∀ i, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V₀ i))
    (hLip₁ : letI := D₁.metricSpace; ∀ j, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V₁ j)) :
    HasBoundedBinaryMultidegreeFamily D₀ D₁ M₀ M₁ g₀ g₁ V₀ V₁ p := by
  unfold HasBoundedBinaryMultidegreeFamily
  dsimp only
  let P := optionProduct D₀ (fun _ : Unit => D₁)
  let D := optionFactors D₀ (fun _ : Unit => D₁)
  let M : ∀ i : Option Unit, (D i).MultidegreeStructure bound
    | none => M₀
    | some _ => M₁
  let g : ∀ i : Option Unit, (M i).filtration.realification.PolynomialOrbit
    | none => g₀
    | some _ => g₁
  let : ∀ i : Option Unit, TopologicalSpace (ℝ ⊗[ℚ] optionLieSpace L₀ (fun _ : Unit => L₁) i) :=
    fun i => match i with
      | none => inferInstanceAs (TopologicalSpace (ℝ ⊗[ℚ] L₀))
      | some _ => inferInstanceAs (TopologicalSpace (ℝ ⊗[ℚ] L₁))
  let : ∀ i : Option Unit, IsTopologicalAddGroup (ℝ ⊗[ℚ] optionLieSpace L₀ (fun _ : Unit => L₁) i) :=
    fun i => match i with
      | none => inferInstanceAs (IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀))
      | some _ => inferInstanceAs (IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁))
  let : ∀ i : Option Unit, ContinuousSMul ℝ (ℝ ⊗[ℚ] optionLieSpace L₀ (fun _ : Unit => L₁) i) :=
    fun i => match i with
      | none => inferInstanceAs (ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀))
      | some _ => inferInstanceAs (ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁))
  let : ∀ i : Option Unit, T2Space (ℝ ⊗[ℚ] optionLieSpace L₀ (fun _ : Unit => L₁) i) :=
    fun i => match i with
      | none => inferInstanceAs (T2Space (ℝ ⊗[ℚ] L₀))
      | some _ => inferInstanceAs (T2Space (ℝ ⊗[ℚ] L₁))
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace L₀ (fun _ : Unit => L₁) i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace L₀ (fun _ : Unit => L₁) i)) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 P.basis
  let V : ∀ i : Option Unit, (I × J) → (D i).Space → ℂ
    | none => fun ij => V₀ ij.1
    | some _ => fun ij => V₁ ij.2
  have hM : ∀ i, (M i).ComplexityLE p := fun i => by
    match i with
    | none => exact hM₀
    | some _ => exact hM₁
  have hV : ∀ i ij x, ‖V i ij x‖ ≤ 1 := fun i => by
    match i with
    | none => exact fun ij x => hV₀ ij.1 x
    | some _ => exact fun ij x => hV₁ ij.2 x
  have hLip : ∀ i, letI := (D i).metricSpace;
      ∀ ij, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V i ij) := fun i => by
    match i with
    | none => exact fun ij => hLip₀ ij.1
    | some _ => exact fun ij => hLip₁ ij.2
  obtain ⟨hprod, T, hTo, hTn, hTc, _, hTe⟩ :=
    exists_bounded_multidegree_product_family D M g V (by linarith) (by simpa using hp) hM hV hLip
  refine ⟨piMultidegree D M, hprod, MultidegreeLieFiltration.piRealOrbit (fun i => (M i).filtration) g,
    (fun ij => T (fun _ => ij)), (fun ij => hTo (fun _ => ij)),
    (fun ij => hTn (fun _ => ij)), (fun ij => hTc (fun _ => ij)), ?_⟩
  intro ij x
  have he := hTe (fun _ => ij) x
  rw [Fintype.prod_option, Fintype.prod_unique] at he
  exact he

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

structure NativeBoundedMultidegreeFamily {σ : Type*} [Fintype σ]
    (bound : σ → ℕ) (I : Type*) (p : ℝ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L (∑ i, bound i) dim
  multi : model.MultidegreeStructure bound
  complexity : multi.ComplexityLE p
  orbit : multi.filtration.realification.PolynomialOrbit
  test : I → model.Niltest (fun _ : σ => 1)
  test_orbit : ∀ i, (test i).orbit = multi.orbitToOrdinary orbit
  test_norm : ∀ i, (test i).normBound = 1
  test_complexity : ∀ i, (test i).ComplexityLE p

attribute [local instance] NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra
  NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd
  NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

namespace NativeBoundedMultidegreeFamily

variable {σ I : Type*} [Fintype σ] {bound : σ → ℕ} {p q : ℝ}
  (F : NativeBoundedMultidegreeFamily bound I p)

noncomputable def eval (i : I) (x : σ → ℤ) : ℂ := (F.test i).eval x

theorem eval_multidegree (i : I) (x : σ → ℤ) : F.eval i x =
    (F.test i).observable (QuotientGroup.mk
      (F.multi.filtration.realification.polynomialOrbitEval x F.orbit)) := by
  change (F.test i).observable (QuotientGroup.mk
    (F.model.filtration.realification.polynomialOrbitEval (fun _ : σ => 1) x (F.test i).orbit)) = _
  rw [F.test_orbit, F.multi.orbitToOrdinary_eval]

noncomputable def mono (hpq : p ≤ q) : NativeBoundedMultidegreeFamily bound I q :=
  { F with
    complexity := F.complexity.mono F.multi hpq
    test_complexity := fun i => (F.test_complexity i).mono hpq }

@[simp] theorem mono_eval (hpq : p ≤ q) (i : I) (x : σ → ℤ) :
    (F.mono hpq).eval i x = F.eval i x := rfl

end NativeBoundedMultidegreeFamily

namespace NativeMultidegreeNilcharacter

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

theorem exists_product_with_bounded_family
    {σ J : Type*} [Fintype σ] {bound : σ → ℕ} {p B : ℝ}
    (W : NativeMultidegreeNilcharacter bound p)
    {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (M : D.MultidegreeStructure bound) (hstep : s = ∑ i, bound i)
    (g : M.filtration.realification.PolynomialOrbit)
    (G : J → D.Space → ℂ) (hB : 0 ≤ B) (hM : M.ComplexityLE B)
    (hG : ∀ j x, ‖G j x‖ ≤ 2)
    (hLip : letI := D.metricSpace; ∀ j, LipschitzWith ⟨Real.exp B, Real.exp_nonneg _⟩ (G j)) :
    ∃ F : NativeBoundedMultidegreeFamily bound (Fin W.outputDim × J)
        (productNiltestBudget (p + B + 2 + 4)),
      ∀ ij x, F.eval ij x = W.eval ij.1 x *
        G ij.2 (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)) / 2 := by
  subst hstep
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpP : p ≤ p + B + 2 := by linarith
  have hBP : B ≤ p + B + 2 := by linarith
  let G' (j : J) (x : D.Space) := G j x / 2
  have hGn (j : J) (x : D.Space) : ‖G' j x‖ ≤ 1 := by
    dsimp only [G']
    rw [norm_div]
    norm_num only [Complex.norm_ofNat]
    linarith [hG j x]
  have hGL : letI := D.metricSpace;
      ∀ j, LipschitzWith ⟨Real.exp (p + B + 2), Real.exp_nonneg _⟩ (G' j) := by
    let := D.metricSpace
    intro j
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (G j x / 2) (G j y / 2) ≤ _
    rw [dist_eq_norm, ← sub_div, norm_div]
    norm_num only [Complex.norm_ofNat]
    have h := (hLip j).dist_le_mul x y
    rw [dist_eq_norm] at h
    exact (div_le_self (norm_nonneg _) (by norm_num : (1 : ℝ) ≤ 2)).trans
      (h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hBP) dist_nonneg))
  have hWL : letI := W.model.metricSpace;
      ∀ i, LipschitzWith ⟨Real.exp (p + B + 2), Real.exp_nonneg _⟩ (W.vertical.observable i) := by
    let := W.model.metricSpace
    intro i
    exact (W.vertical.lipschitz i).weaken
      (show W.vertical.lipBound ≤ ⟨Real.exp (p + B + 2), Real.exp_nonneg _⟩ from
        W.vertical.lip_bound.trans (Real.exp_le_exp.mpr hpP))
  obtain ⟨MP, hMP, gP, htests⟩ := exists_bounded_binary_multidegree_family
    W.model D W.multi M W.orbit g W.vertical.observable G' (by linarith : 2 ≤ p + B + 2)
    (W.complexity.mono W.multi hpP) (hM.mono M hBP) W.vertical.norm hGn hWL hGL
  let P := optionProduct W.model (fun _ : Unit => D)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace W.L (fun _ : Unit => L) i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option Unit, optionLieSpace W.L (fun _ : Unit => L) i)) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 P.basis
  obtain ⟨T, hTo, hTn, hTc, hTe⟩ := htests
  let F : NativeBoundedMultidegreeFamily bound (Fin W.outputDim × J)
      (productNiltestBudget (p + B + 2 + 4)) := {
    L := ∀ i : Option Unit, optionLieSpace W.L (fun _ : Unit => L) i
    dim := Fintype.card (Σ i : Option Unit, Fin (optionDimension W.dim (fun _ : Unit => d) i))
    model := P
    multi := MP
    complexity := hMP
    orbit := gP
    test := T
    test_orbit := hTo
    test_norm := hTn
    test_complexity := hTc
  }
  refine ⟨F, ?_⟩
  intro ij x
  change (T ij).eval x = _
  rw [hTe]
  change W.eval ij.1 x * (G ij.2 _ / 2) = _
  rw [mul_div_assoc]

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.NativeBoundedMultidegreeFamily

open scoped TensorProduct

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

theorem norm_eval {σ I : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily bound I p) (i : I) (x : σ → ℤ) : ‖F.eval i x‖ ≤ 1 := by
  have h := (F.test i).norm_eval_le x
  rw [F.test_norm] at h
  exact h

noncomputable def slice {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p)
    (i : I) (h : ℤ) : F.model.Niltest (fun _ : Unit => 1) :=
  (F.test i).affinePullback (fun j _ => correlationInput 0 1 j) (correlationInput h 0)

theorem slice_eval {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p)
    (i : I) (h : ℤ) (x : Unit → ℤ) :
    (F.slice i h).eval x = F.eval i (correlationInput h (x ())) := by
  rw [slice, RationalFilteredNilmanifold.Niltest.eval_affinePullback]
  apply congrArg (F.test i).eval
  funext j
  refine Fin.cases ?_ (fun _ => ?_) j <;> simp [integerAffineMap, correlationInput]

theorem slice_orbit_eval {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p)
    (i : I) (h : ℤ) (x : Unit → ℤ) :
    F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (F.slice i h).orbit =
      F.multi.filtration.realification.polynomialOrbitEval (correlationInput h (x ())) F.orbit := by
  let A : Fin 2 → Unit → ℤ := fun j _ => correlationInput 0 1 j
  let b := correlationInput h 0
  have heq : integerAffineMap A b x = correlationInput h (x ()) := by
    funext j
    refine Fin.cases ?_ (fun _ => ?_) j <;> simp [A, b, integerAffineMap, correlationInput]
  have he := F.model.filtration.realification.polynomialOrbitSubstitute_eval
    (integerAffinePolynomial A b) (integerAffinePolynomial_support A b)
    (F.test i).orbit x (integerAffineMap A b x) (integerAffinePolynomial_eval A b x)
  change F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (F.slice i h).orbit =
    F.model.filtration.realification.polynomialOrbitEval (fun _ : Fin 2 => 1)
      (integerAffineMap A b x) (F.test i).orbit at he
  rw [he, heq, F.test_orbit, F.multi.orbitToOrdinary_eval]

theorem slice_norm {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p) (i : I) (h : ℤ) :
    (F.slice i h).normBound = 1 := F.test_norm i

theorem slice_complexity {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p) (i : I) (h : ℤ) :
    (F.slice i h).ComplexityLE p := F.test_complexity i

theorem slice_observable {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p) (i : I) (h : ℤ) :
    (F.slice i h).observable = (F.test i).observable := rfl

end Erdos3.NativeBoundedMultidegreeFamily

namespace Erdos3.NativeUnitRankFamily

open scoped TensorProduct

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

theorem withOrbit_eval {σ τ I : Type*} [Fintype I] {w : σ → ℕ} {s r : ℕ} {p : ℝ}
    (F : NativeUnitRankFamily w s r τ I p) (i : I) (t : τ) (x : σ → ℤ) :
    ((F.test i).withOrbit (F.orbit t)).eval x = F.eval t i x := rfl

end Erdos3.NativeUnitRankFamily

end

section

namespace Erdos3

open scoped TensorProduct

namespace NativeUnitRankFamily

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

variable {τ τ' I : Type*} [Fintype I] {s r : ℕ} {p q : ℝ}
  (F : NativeUnitRankFamily (fun _ : Unit => 1) s r τ I p)
  (e : τ' → τ) (hpq : p ≤ q) {n : ℕ} (hn : (n + 1 : ℝ) ≤ Real.exp q)
  (V : F.model.UnitVerticalObservable (F.model.filtration.realification.subgroup s) (Fin (n + 1)) q)

noncomputable def toVerticalFamily : NativeDegreeRankFamily s r τ' q where
  L := F.L
  dim := F.dim
  model := F.model
  rank := F.rank
  complexity := F.complexity.mono F.rank hpq
  orbit := fun t => F.orbit (e t)
  normalized := fun t => F.normalized (e t)
  outputDim := n + 1
  output_pos := Nat.succ_pos n
  output_bound := by simpa only [Nat.cast_add, Nat.cast_one] using hn
  vertical := {
    V with
    vertical := fun i z hz x => V.vertical i z (F.rank.realSubgroup_le_degree s r hz) x
    integral := fun z hz hL => V.integral z (F.rank.realSubgroup_le_degree s r hz) hL
  }

theorem toVerticalFamily_eval (i : Fin (n + 1)) (t : τ') (x : ℤ) :
    (F.toVerticalFamily e hpq hn V).eval i t x = V.observable i (QuotientGroup.mk
      (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => x) (F.orbit (e t)))) := rfl

end NativeUnitRankFamily

namespace NativeBoundedMultidegreeFamily

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

variable {σ I : Type*} [Fintype σ] {bound : σ → ℕ} {p q : ℝ}
  (M : NativeBoundedMultidegreeFamily bound I p) (hpq : p ≤ q)
  {n : ℕ} (hn : (n + 1 : ℝ) ≤ Real.exp q)
  (V : M.model.UnitVerticalObservable
    (M.model.filtration.realification.subgroup (∑ i, bound i)) (Fin (n + 1)) q)

noncomputable def toNilcharacter : NativeMultidegreeNilcharacter bound q where
  L := M.L
  dim := M.dim
  model := M.model
  multi := M.multi
  complexity := M.complexity.mono M.multi hpq
  orbit := M.orbit
  outputDim := n + 1
  output_pos := Nat.succ_pos n
  output_bound := by simpa only [Nat.cast_add, Nat.cast_one] using hn
  vertical := {
    V with
    vertical := fun i z hz x => V.vertical i z (M.multi.realSubgroup_top ▸ hz) x
    integral := fun z hz hL => V.integral z (M.multi.realSubgroup_top ▸ hz) hL
  }

theorem toNilcharacter_eval (i : Fin (n + 1)) (x : σ → ℤ) :
    (M.toNilcharacter hpq hn V).eval i x = V.observable i (QuotientGroup.mk
      (M.multi.filtration.realification.polynomialOrbitEval x M.orbit)) := rfl

end NativeBoundedMultidegreeFamily

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

attribute [local instance] NativeUnitRankFamily.lie NativeUnitRankFamily.algebra
  NativeUnitRankFamily.topology NativeUnitRankFamily.topologicalAdd
  NativeUnitRankFamily.continuousSMul NativeUnitRankFamily.hausdorff
  NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra
  NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd
  NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

theorem exists_native_correlation_of_unit_products
    {I K : Type} [Fintype I] {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
    (J : Finset (ZMod N))
    (F : NativeUnitRankFamily (fun _ : Unit => 1) s r {h // h ∈ J} I p)
    (M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) K p)
    (H : Finset {h // h ∈ J}) (hH : H.Nonempty)
    (hdense : Real.exp (-q) * N ≤ (H.card : ℝ)) (hpq : p ≤ q)
    {n₁ n₂ : ℕ} (hn₁ : (n₁ + 1 : ℝ) ≤ Real.exp q) (hn₂ : (n₂ + 1 : ℝ) ≤ Real.exp q)
    (V₁ : F.model.UnitVerticalObservable (F.model.filtration.realification.subgroup s)
      (Fin (n₁ + 1)) q)
    (V₂ : M.model.UnitVerticalObservable
      (M.model.filtration.realification.subgroup (∑ i, mixedCorrelationDegree s i)) (Fin (n₂ + 1)) q)
    (hcorr : ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N q (fun _ : Unit => fun x =>
      multiplicativeDerivative f h.val x * star (V₂.observable 0 (QuotientGroup.mk
        (M.multi.filtration.realification.polynomialOrbitEval
          (correlationInput (h.val.val : ℤ) (x.val : ℤ)) M.orbit))) *
        star (V₁.observable 0 (QuotientGroup.mk
          (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
            (fun _ => (x.val : ℤ)) (F.orbit h))))))) :
    Nonempty (NativeCorrelationStructure s r N q f) := by
  classical
  obtain ⟨h₀, hh₀⟩ := hH
  let e (h : ZMod N) : {h // h ∈ J} := if hh : h ∈ J then ⟨h, hh⟩ else h₀
  have he (h : {h // h ∈ J}) : e h.val = h := by
    simp only [e, dite_eq_left h.property]
  let family := F.toVerticalFamily e hpq hn₁ V₁
  let mixed := M.toNilcharacter hpq hn₂ V₂
  let shifts := H.image Subtype.val
  have hcard : shifts.card = H.card := Finset.card_image_of_injective _ Subtype.val_injective
  refine ⟨{
    shifts := shifts
    nonempty := (show H.Nonempty from ⟨h₀, hh₀⟩).image _
    density := by simpa only [ZMod.card, hcard] using hdense
    mixed := mixed
    family := family
    correlation := ?_
  }⟩
  intro h hh
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hh
  obtain ⟨Wh⟩ := hcorr z hz
  refine ⟨Wh.mapCoordinates _ (fun _ => ((0 : Fin (n₂ + 1)), (0 : Fin (n₁ + 1)))) ?_⟩
  intro i x
  have hinput : (fun j => ((correlationInput z.val x j).val : ℤ)) =
      correlationInput (z.val.val : ℤ) (x.val : ℤ) :=
    map_correlationInput (fun a : ZMod N => (a.val : ℤ)) z.val x
  have hmixed : mixed.evalCyclic N (0 : Fin (n₂ + 1)) (correlationInput z.val x) = V₂.observable 0 (QuotientGroup.mk
      (M.multi.filtration.realification.polynomialOrbitEval
        (correlationInput (z.val.val : ℤ) (x.val : ℤ)) M.orbit)) := by
    change (M.toNilcharacter hpq hn₂ V₂).eval (0 : Fin (n₂ + 1)) (fun j => ((correlationInput z.val x j).val : ℤ)) = _
    rw [hinput, M.toNilcharacter_eval]
  have hfamily : family.evalCyclic N (0 : Fin (n₁ + 1)) z.val x = V₁.observable 0 (QuotientGroup.mk
      (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (F.orbit z))) := by
    change (F.toVerticalFamily e hpq hn₁ V₁).eval (0 : Fin (n₁ + 1)) z.val (x.val : ℤ) = _
    rw [F.toVerticalFamily_eval, he]
  change nativeCorrelationResidual f mixed family z.val ((0 : Fin (n₂ + 1)), (0 : Fin (n₁ + 1))) x = _
  simp only [nativeCorrelationResidual, hmixed, hfamily]

end Erdos3

end

section

namespace Erdos3.QuadraticMarked

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

noncomputable def parameter (t : ℕ) (v : Fin t → ℝ) : (multidegree t).realification.Group :=
  realMarkedParameterElement filtration generators weights marked weight_pos generator_mem t v

theorem parameter_mul (t : ℕ) (v w : Fin t → ℝ) :
    parameter t v * parameter t w = parameter t (v + w) :=
  realMarkedParameterElement_mul filtration generators weights marked weight_pos generator_mem t v w

theorem parameter_inv (t : ℕ) (v : Fin t → ℝ) : (parameter t v)⁻¹ = parameter t (-v) :=
  realMarkedParameterElement_inv filtration generators weights marked weight_pos generator_mem t v

noncomputable def affineElement (t : ℕ) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) :
    (multidegree t).realification.Group := ⟨n • projectedLift t a b⟩

theorem affineElement_phase (t m : ℕ) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) :
    torusPhaseLinear (phase t m) (affineElement t a b n).coord = 0 := by
  change torusPhaseLinear (phase t m) (n • projectedLift t a b) = 0
  rw [map_smul, projectedLift_phase, smul_zero]

noncomputable def centeredElement (t m : ℕ) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) (v : Fin t → ℝ) :
    (multidegree t).realification.Group :=
  affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n * parameter t ((m : ℝ) • -v)

theorem centeredElement_phase {t d : ℕ} (D : RationalFilteredNilmanifold (Algebra t) 2 d)
    (m : ℕ) (hm : 0 < m) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) (v : Fin t → ℝ) :
    torusPhaseLinear (phase t m) (centeredElement t m a b n v).coord = -v := by
  rw [centeredElement, torusPhaseLinear_mul D, affineElement_phase, zero_add]
  exact normalizedMarkedPhase_real_scaled_parameter filtration generators weights marked t m hm (-v)

theorem centeredElement_retraction_coord {t d : ℕ}
    (D : RationalFilteredNilmanifold (Algebra t) 2 d)
    (m : ℕ) (hm : 0 < m) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) (v : Fin t → ℝ) :
    (normalizedMarkedRetraction filtration generators weights marked weight_pos generator_mem t m D
      (centeredElement t m a b n v)).coord =
        (lieQuotientMap (markedShiftSecondIdeal filtration generators weights marked t)).toLinearMap.baseChange ℝ
          (realMarkedAffineShift filtration generators weights marked weight_pos generator_mem t ((m : ℝ) • v)
            (n • sourceLift t a (fun i => (m : ℝ)⁻¹ * b i))) := by
  let f := affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n
  have heq : normalizedMarkedRetraction filtration generators weights marked weight_pos generator_mem t m D
      (centeredElement t m a b n v) = parameter t ((m : ℝ) • v) * f *
        (parameter t ((m : ℝ) • v))⁻¹ := by
    change parameter t ((m : ℝ) • -(torusPhaseLinear (phase t m)
      (centeredElement t m a b n v).coord)) *
        (f * parameter t ((m : ℝ) • -v)) = _
    rw [centeredElement_phase D m hm, neg_neg, smul_neg, ← parameter_inv]
    exact (mul_assoc _ _ _).symm
  rw [heq]
  change conjugationCoord (parameter t ((m : ℝ) • v)) (n • projectedLift t a _) = _
  have hlift : n • projectedLift t a (fun i => (m : ℝ)⁻¹ * b i) =
      (lieQuotientMap (markedShiftSecondIdeal filtration generators weights marked t)).toLinearMap.baseChange ℝ
        (n • sourceLift t a (fun i => (m : ℝ)⁻¹ * b i)) := (map_smul _ _ _).symm
  rw [hlift]
  exact realMarkedAffineShift_conjugation filtration generators weights marked weight_pos generator_mem
    t (by decide) ((m : ℝ) • v) _

theorem localCharacter_centeredElement {t d : ℕ}
    (D : RationalFilteredNilmanifold (Algebra t) 2 d)
    (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ)
    (hη : ∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0)
    (m : ℕ) (hm : 0 < m) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) (v : Fin t → ℝ) :
    localCharacter m D η (centeredElement t m a b n v) =
      CircleFourier.character ((n * (a + ∑ i, v i * b i) : ℝ) : CircleFourier.Circle) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hsum : a + ∑ i, ((m : ℝ) • v) i * ((m : ℝ)⁻¹ * b i) = a + ∑ i, v i * b i := by
    apply congrArg (a + ·)
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [localCharacter, centeredElement_retraction_coord D m hm]
  simp only [map_smul, smul_eq_mul]
  rw [shiftedLift_coordinate η hη, hsum]

end Erdos3.QuadraticMarked

end

section

namespace Erdos3.QuadraticMarked

open NilpotentLieBCHGroup
open scoped BigOperators

noncomputable def localOrbit {N : ℕ} (t m : ℕ) (a : ℝ) (b u c : Fin t → ℝ) (h₀ : ZMod N) :
    (multidegree t).realification.PolynomialOrbit :=
  Mul.mul (α := (multidegree t).realification.PolynomialOrbit)
    (pureOrbit t a (fun i => (m : ℝ)⁻¹ * b i))
    (realMarkedParameterOrbit filtration generators weights marked weight_pos generator_mem t
      (fun i => (m : ℝ) * ((h₀.val : ℝ) * u i + c i)) (fun i => -(m : ℝ) * u i))

theorem localOrbit_eval {N : ℕ} (t m : ℕ) (a : ℝ) (b u c : Fin t → ℝ)
    (h₀ h : ZMod N) (n : ℤ) :
    (multidegree t).realification.polynomialOrbitEval (correlationInput (h.val : ℤ) n)
      (localOrbit t m a b u c h₀) =
        affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n *
          parameter t (fun i => -(m : ℝ) * (((h.val : ℝ) - h₀.val) * u i - c i)) := by
  have he : (multidegree t).realification.polynomialOrbitEval (correlationInput (h.val : ℤ) n)
      (pureOrbit t a (fun i => (m : ℝ)⁻¹ * b i)) =
        affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n :=
    NilpotentLieBCHGroup.ext (pureOrbit_eval t a _ h.val n)
  let E := (multidegree t).realification.polynomialOrbitEval (correlationInput (h.val : ℤ) n)
  let P : (multidegree t).realification.PolynomialOrbit :=
    realMarkedParameterOrbit filtration generators weights marked weight_pos generator_mem t
      (fun i => (m : ℝ) * ((h₀.val : ℝ) * u i + c i)) (fun i => -(m : ℝ) * u i)
  have hmul : E (localOrbit t m a b u c h₀) =
      E (pureOrbit t a (fun i => (m : ℝ)⁻¹ * b i)) * E P := E.map_mul _ _
  apply hmul.trans
  change E (pureOrbit t a (fun i => (m : ℝ)⁻¹ * b i)) = _ at he
  rw [he]
  apply congrArg (affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n * ·)
  apply (realMarkedParameterOrbit_eval filtration generators weights marked weight_pos generator_mem t
    (fun i => (m : ℝ) * ((h₀.val : ℝ) * u i + c i)) (fun i => -(m : ℝ) * u i) h.val n).trans
  apply congrArg (parameter t)
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_natCast]
  ring

noncomputable def latticeCorrection {N : ℕ} (t m : ℕ) (u c : Fin t → ℝ) (h₀ h : ZMod N) :
    (multidegree t).realification.Group :=
  parameter t ((m : ℝ) • fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℝ))

theorem latticeCorrection_mem {N t d : ℕ}
    (D : RationalFilteredNilmanifold (Algebra t) 2 d) (m : ℕ)
    (hlat : ∀ a : Fin t → ℤ, (⟨(m : ℚ) • markedQuotientDirection
      filtration generators weights marked t (fun i => (a i : ℚ))⟩ : D.filtration.Group) ∈ D.lattice)
    (u c : Fin t → ℝ) (h₀ h : ZMod N) : latticeCorrection t m u c h₀ h ∈ D.realLattice :=
  realMarkedParameterElement_scaled_integer_mem filtration generators weights marked weight_pos generator_mem
    t m D hlat (fun i => -affineCyclicTorusCarry u c h₀ h i)

theorem localOrbit_right_normalization {N : ℕ} (t m : ℕ) (a : ℝ) (b u c : Fin t → ℝ)
    (h₀ h : ZMod N) (n : ℤ) :
    (multidegree t).realification.polynomialOrbitEval (correlationInput (h.val : ℤ) n)
      (localOrbit t m a b u c h₀) * (latticeCorrection t m u c h₀ h)⁻¹ =
        centeredElement t m a b n (affineCyclicTorusLocalLift u c h₀ h) := by
  rw [localOrbit_eval, latticeCorrection, parameter_inv, mul_assoc, parameter_mul]
  apply congrArg (affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n * ·)
  apply congrArg (parameter t)
  funext i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Int.cast_neg,
    affineCyclicTorusLocalLift_eq_sub_carry]
  ring

theorem localOrbit_quotient {N t d : ℕ}
    (D : RationalFilteredNilmanifold (Algebra t) 2 d) (m : ℕ)
    (hlat : ∀ a : Fin t → ℤ, (⟨(m : ℚ) • markedQuotientDirection
      filtration generators weights marked t (fun i => (a i : ℚ))⟩ : D.filtration.Group) ∈ D.lattice)
    (a : ℝ) (b u c : Fin t → ℝ) (h₀ h : ZMod N) (n : ℤ) :
    (QuotientGroup.mk ((multidegree t).realification.polynomialOrbitEval (correlationInput (h.val : ℤ) n)
      (localOrbit t m a b u c h₀)) : D.Space) =
        QuotientGroup.mk (centeredElement t m a b n (affineCyclicTorusLocalLift u c h₀ h)) := by
  have hc := latticeCorrection_mem D m hlat u c h₀ h
  calc
    _ = QuotientGroup.mk ((multidegree t).realification.polynomialOrbitEval
        (correlationInput (h.val : ℤ) n) (localOrbit t m a b u c h₀) *
          (latticeCorrection t m u c h₀ h)⁻¹) :=
      (quotient_mk_mul_mem D.realLattice _ ⟨_, D.realLattice.inv_mem hc⟩).symm
    _ = _ := congrArg QuotientGroup.mk (localOrbit_right_normalization t m a b u c h₀ h n)

theorem localOrbit_observable {N t d : ℕ}
    (D : RationalFilteredNilmanifold (Algebra t) 2 d)
    (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ)
    (hη : ∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0)
    (m : ℕ) (hm : 0 < m)
    (hlat : ∀ a : Fin t → ℤ, (⟨(m : ℚ) • markedQuotientDirection
      filtration generators weights marked t (fun i => (a i : ℚ))⟩ : D.filtration.Group) ∈ D.lattice)
    (G : D.Space → ℂ)
    (hG : ∀ g : D.RealGroup, (∀ i, |torusPhaseLinear (phase t m) g.coord i| ≤ 1 / 4) →
      G (QuotientGroup.mk g) = localCharacter m D η g)
    (a : ℝ) (b u c : Fin t → ℝ) (h₀ h : ZMod N)
    (hsmall : ∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 4) (n : ℤ) :
    G (QuotientGroup.mk ((multidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (localOrbit t m a b u c h₀))) =
        CircleFourier.character (((n : ℝ) * (a + ∑ i, affineCyclicTorusLocalLift u c h₀ h i * b i) : ℝ) :
          CircleFourier.Circle) := by
  rw [localOrbit_quotient D m hlat]
  apply (hG _ ?_).trans
    (localCharacter_centeredElement D η hη m hm a b n (affineCyclicTorusLocalLift u c h₀ h))
  intro i
  rw [centeredElement_phase D m hm]
  simpa only [Pi.neg_apply, abs_neg] using hsmall i

end Erdos3.QuadraticMarked

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_quadratic_bounded_family :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 1 ≤ p → ∀ t : ℕ, (t : ℝ) ≤ p →
      ∀ {N : ℕ} (a : ℝ) (b u c : Fin t → ℝ) (h₀ : ZMod N),
      ∃ F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree 1) (Fin 1 × Unit) ((p + C) ^ C),
        ∀ h : ZMod N, (∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 4) → ∀ n : ℤ,
          F.eval (0, ()) (correlationInput (h.val : ℤ) n) =
            CircleFourier.character (((n : ℝ) *
              (a + ∑ i, affineCyclicTorusLocalLift u c h₀ h i * b i) : ℝ) : CircleFourier.Circle) / 2 := by
  obtain ⟨A, _, hmodel⟩ := QuadraticMarked.exists_model
  obtain ⟨B, _, hproduct⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + 6 + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p hp t ht N a b u c h₀
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : productNiltestBudget (q + 6) ≤ (p + C) ^ C := by
    apply (hproduct (q + 6) (by positivity)).trans
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp0
  obtain ⟨η, hη, m, hm, _, d, D, _, M, hMF, hM, _, hlat, hG⟩ := hmodel hp t ht
  let := moduleTopology ℝ (ℝ ⊗[ℚ] QuadraticMarked.Algebra t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] QuadraticMarked.Algebra t) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 D.basis
  let := D.metricSpace
  obtain ⟨G, hGn, hGL, hGe⟩ := hG
  let W := NativeMultidegreeNilcharacter.constOne (mixedCorrelationDegree 1) (p := 0) (by positivity)
  have hreal : (QuadraticMarked.multidegree t).realification = M.filtration.realification :=
    congrArg MultidegreeLieFiltration.realification hMF.symm
  let g := (QuadraticMarked.multidegree t).realification.orbitEquivOfEq hreal
    (QuadraticMarked.localOrbit t m a b u c h₀)
  have hstep : 2 = ∑ i, mixedCorrelationDegree 1 i := (mixedCorrelationDegree_sum 1).symm
  obtain ⟨F, hF⟩ := W.exists_product_with_bounded_family D M hstep g (fun _ : Unit => G)
    hq hM (fun _ => hGn) (fun _ => hGL)
  have hcost' : productNiltestBudget (0 + q + 2 + 4) ≤ (p + C) ^ C := by
    rw [show 0 + q + 2 + 4 = q + 6 by ring]
    exact hcost
  refine ⟨F.mono hcost', ?_⟩
  intro h hsmall n
  change F.eval ((0 : Fin 1), ()) (correlationInput (h.val : ℤ) n) = _
  apply (hF ((0 : Fin 1), ()) (correlationInput (h.val : ℤ) n)).trans
  change 1 * G (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval
    (correlationInput (h.val : ℤ) n) g)) / 2 = _
  rw [one_mul]
  congr 1
  have he := (QuadraticMarked.multidegree t).realification.orbitEquivOfEq_eval hreal
    (QuadraticMarked.localOrbit t m a b u c h₀) (correlationInput (h.val : ℤ) n)
  change G (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval _ g)) = _
  rw [he]
  exact QuadraticMarked.localOrbit_observable D η hη m hm hlat G hGe a b u c h₀ h hsmall n

end Erdos3

end

end OAI
