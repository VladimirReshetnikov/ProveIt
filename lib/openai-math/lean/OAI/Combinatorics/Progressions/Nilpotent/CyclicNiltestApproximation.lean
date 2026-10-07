/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Mathematical statements are unchanged from the pinned upstream source.
Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.ProductOrbitCongruence
import OAI.Combinatorics.Progressions.Estimates.RealificationModuleTopology
import OAI.Combinatorics.Progressions.Fourier.ProductFrequencyKernel
import OAI.Combinatorics.Progressions.Linear.TripleProductBasisBounds
import OAI.Combinatorics.Progressions.Nilpotent.CellwiseNiltestDiscretization

namespace OAI

section

open scoped NNReal

namespace Erdos3

noncomputable def productExpBound (p : ℝ) : ℝ≥0 := ⟨Real.exp p, Real.exp_nonneg p⟩

@[simp] theorem coe_productExpBound (p : ℝ) : (productExpBound p : ℝ) = Real.exp p := rfl

def productObservableLipBudget (p : ℝ) : ℝ := p + (p ^ 2 + p + 3) ^ 2

def productNiltestBudget (p : ℝ) : ℝ :=
  (p + 2) ^ 2 + p + productObservableLipBudget p + p ^ 2 + 4

theorem productObservableLipBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ productObservableLipBudget p := by
  unfold productObservableLipBudget
  positivity

theorem productNiltestBudget_geometry {p : ℝ} (hp : 0 ≤ p) :
    (p + 2) ^ 2 ≤ productNiltestBudget p := by
  have hr := productObservableLipBudget_nonneg hp
  unfold productNiltestBudget
  nlinarith [sq_nonneg p]

theorem productNiltestBudget_observable {p : ℝ} (hp : 0 ≤ p) (m : ℕ) (hm : (m : ℝ) ≤ p) :
    2 + Real.exp p ^ m + (m : ℝ) * Real.exp (productObservableLipBudget p) * Real.exp p ^ m ≤
      Real.exp (productNiltestBudget p) := by
  let A := p + productObservableLipBudget p + p ^ 2
  have hR := productObservableLipBudget_nonneg hp
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : Real.exp p ^ m ≤ Real.exp (p ^ 2) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hmexp : (m : ℝ) ≤ Real.exp p := hm.trans (by linarith [Real.add_one_le_exp p])
  have hB' : Real.exp p ^ m ≤ Real.exp A := hB.trans (Real.exp_le_exp.mpr (by dsimp [A]; linarith))
  have hK : (m : ℝ) * Real.exp (productObservableLipBudget p) * Real.exp p ^ m ≤ Real.exp A := by
    calc
      _ ≤ Real.exp p * Real.exp (productObservableLipBudget p) * Real.exp (p ^ 2) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 4 * Real.exp A := by linarith [Real.one_le_exp_iff.mpr hA]
    _ ≤ Real.exp 4 * Real.exp A := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = Real.exp (4 + A) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by unfold productNiltestBudget; dsimp [A]; nlinarith [sq_nonneg (p + 2)])

theorem exists_productNiltestBudget_bound :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → productNiltestBudget p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + 2) ^ 2 + X + (X + (X ^ 2 + X + 3) ^ 2) + X ^ 2 + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, X, Polynomial.eval₂_pow, productNiltestBudget, productObservableLipBudget] using hbound p hp

end Erdos3

end

section

open Module
open scoped BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productLayerBasis_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hD : ∀ i, (D i).GeometryComplexityLE p) (j : Fin (s + 1))
    (k : Σ i, Fin (finrank ℚ ((D i).filtration.layer (j.val + 1)))) (l : Σ i, Fin (d i)) :
    rationalLogHeight ((Pi.basis (fun i => (D i).basis)).repr ((productLayerBasis D j k).val) l) ≤ p := by
  classical
  rcases k with ⟨a, k⟩
  rcases l with ⟨b, l⟩
  simp only [productLayerBasis, Basis.map_apply, Pi.basis_repr]
  change rationalLogHeight ((D b).basis.repr
    (((Pi.basis (fun i => (D i).layerBasis j)) ⟨a, k⟩ b).val) l) ≤ p
  rw [Pi.basis_apply]
  by_cases hab : a = b
  · subst b
    rw [Pi.single_eq_same]
    exact (hD a).2.2.2 j k l
  · rw [Pi.single_eq_of_ne (Ne.symm hab)]
    simpa [rationalLogHeight] using hp

theorem pi_geometry {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hD : ∀ i, (D i).GeometryComplexityLE p) :
    (pi D).GeometryComplexityLE ((p + 2) ^ 2) := by
  classical
  have hdim : (Fintype.card (Σ i, Fin (d i)) : ℝ) ≤ p ^ 2 :=
    sigma_card_le_budget hp hι (fun i => by simpa only [Fintype.card_fin] using (hD i).1)
  have hgrid : ((∏ i, (D i).grid : ℕ) : ℝ) ≤ Real.exp (p ^ 2) :=
    product_denominator_le_budget (fun i => (D i).grid) hp hι (fun i => (hD i).2.1)
  have hsmall : p + 1 ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
  have hsq : p ^ 2 ≤ (p + 2) ^ 2 := by nlinarith
  refine ⟨hdim.trans hsq, hgrid.trans (Real.exp_le_exp.mpr hsq), ?_, ?_⟩
  · intro i j k
    change rationalLogHeight (lieStructureConstants (productFinBasis D) i j k) ≤ _
    rw [productFinBasis, lieStructureConstants_reindex]
    have hh := lie_pi_structure_height (fun i => (D i).basis) (one_le_ceil_exp p)
      (fun a i j k => rationalHeightLE_ceil_exp ((hD a).2.2.1 i j k))
    exact (rationalLogHeight_le_of_height (hh _ _ _) (ceil_exp_le_exp_add_one hp)).trans hsmall
  · change ∀ (j : Fin (s + 1))
      (k : Fin (finrank ℚ ((NilpotentLieFiltration.pi (fun i => (D i).filtration)).layer (j.val + 1))))
      (l : Fin (Fintype.card (Σ i, Fin (d i)))),
        rationalLogHeight ((productFinBasis D).repr ((productLayerFinBasis D j k).val) l) ≤ (p + 2) ^ 2
    intro j k l
    rw [productFinBasis, Basis.repr_reindex_apply, productLayerFinBasis, Basis.reindex_apply]
    apply le_trans _ (show p ≤ (p + 2) ^ 2 by linarith)
    exact productLayerBasis_logHeight D hp hD j _ _

end Erdos3.RationalFilteredNilmanifold

end

section

open Module
open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productProjection_lattice (i : ι) :
    (pi D).lattice ≤ (D i).lattice.comap (NilpotentLieBCHGroup.mapOfSteps (liePiEval i)) := by
  intro g hg
  exact (mem_piBCHSubgroup (fun i => (D i).filtration) (fun i => (D i).lattice) g).mp hg i

noncomputable def productProjectionHom (i : ι) : (pi D).RealGroup →* (D i).RealGroup :=
  NilpotentLieBCHGroup.realificationMap (hnil := (pi D).filtration.lowerCentralSeries_eq_bot)
    (hM := (D i).filtration.lowerCentralSeries_eq_bot) (liePiEval i)

noncomputable def productProjection (i : ι) : (pi D).Space → (D i).Space :=
  cosetMap (pi D).realLattice (D i).realLattice (productProjectionHom D i)
    (NilpotentLieBCHGroup.realificationMap_subgroup (liePiEval i) _ _ (productProjection_lattice D i))

@[simp] theorem productProjection_mk (i : ι) (g : (pi D).RealGroup) :
    productProjection D i (QuotientGroup.mk g) = QuotientGroup.mk (productProjectionHom D i g) := rfl

theorem productProjection_matrix_height (i : ι)
    (j : Fin (Fintype.card (Σ i, Fin (d i)))) (k : Fin (d i)) :
    RationalHeightLE ((D i).basis.repr (liePiEval (R := ℚ) i ((pi D).basis j)) k) 1 := by
  classical
  change RationalHeightLE ((D i).basis.repr (productFinBasis D j i) k) 1
  rw [productFinBasis, Basis.reindex_apply]
  generalize he : (Fintype.equivFin (Σ i, Fin (d i))).symm j = z
  rcases z with ⟨a, l⟩
  rw [Pi.basis_apply]
  by_cases hai : a = i
  · subst a
    rw [Pi.single_eq_same, Basis.repr_self]
    by_cases hlk : l = k <;> simp [hlk, RationalHeightLE]
  · rw [Pi.single_eq_of_ne (Ne.symm hai), map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem productProjection_lipschitz (i : ι) :
    letI := (pi D).metricSpace
    letI := (D i).metricSpace
    LipschitzWith (coordinateLipschitzBound (d i) (Fintype.card (Σ i, Fin (d i))) 1)
      (productProjection D i) := by
  let := realificationQuotientMetricSpace (pi D).basis (pi D).lattice
    (pi D).grid (pi D).grid_pos (pi D).outer_grid
  let := realificationQuotientMetricSpace (D i).basis (D i).lattice
    (D i).grid (D i).grid_pos (D i).outer_grid
  have hh := NilpotentLieBCHGroup.lipschitz_realificationMap_quotient
    (pi D).basis (D i).basis (liePiEval i) (pi D).lattice (D i).lattice
    (productProjection_lattice D i) (pi D).grid (D i).grid (pi D).grid_pos (D i).grid_pos
    (pi D).outer_grid (D i).outer_grid 1 (fun k j => productProjection_matrix_height D i j k)
  exact hh.weaken (by simp only [Fintype.card_fin, Nat.cast_one, le_refl])

omit [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))] in
theorem productProjection_lipschitz_bound {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hD : ∀ i, (D i).GeometryComplexityLE p) (i : ι) :
    (coordinateLipschitzBound (d i) (Fintype.card (Σ i, Fin (d i))) 1 : ℝ) ≤
      Real.exp ((p ^ 2 + p + 3) ^ 2) := by
  have hdim := sigma_card_le_budget hp hι
    (κ := fun i => Fin (d i)) (fun i => by simpa only [Fintype.card_fin] using (hD i).1)
  have hi := (hD i).1
  have hq : 0 ≤ p ^ 2 + p + 1 := by positivity
  have hh := coordinateLipschitzBound_le_exp (d i) (Fintype.card (Σ i, Fin (d i))) 1 hq
    (by nlinarith [sq_nonneg p]) (by linarith)
    (by simpa only [NNReal.coe_one] using Real.one_le_exp_iff.mpr hq)
  convert hh using 2
  ring

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3

def optionLieSpace {ι : Type v} (L₀ : Type u) (L : ι → Type u) : Option ι → Type u
  | none => L₀
  | some i => L i

instance optionLieRing {ι : Type v} {L₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [∀ i, LieRing (L i)] (i : Option ι) : LieRing (optionLieSpace L₀ L i) := by
  cases i <;> dsimp [optionLieSpace] <;> infer_instance

instance optionLieAlgebra {ι : Type v} {L₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
    (i : Option ι) : LieAlgebra ℚ (optionLieSpace L₀ L i) := by
  cases i <;> dsimp [optionLieSpace] <;> infer_instance

def optionDimension {ι : Type v} (d₀ : ℕ) (d : ι → ℕ) : Option ι → ℕ
  | none => d₀
  | some i => d i

namespace RationalFilteredNilmanifold

open Module
open scoped TensorProduct

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def optionFactors : ∀ i : Option ι,
    RationalFilteredNilmanifold (optionLieSpace L₀ L i) s (optionDimension d₀ d i)
  | none => D₀
  | some i => D i

noncomputable def optionProduct := pi (optionFactors D₀ D)

theorem optionProduct_geometry {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hD₀ : D₀.GeometryComplexityLE p) (hD : ∀ i, (D i).GeometryComplexityLE p) :
    (optionProduct D₀ D).GeometryComplexityLE ((p + 3) ^ 2) := by
  have hpp : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  have h := pi_geometry (optionFactors D₀ D) (p := p + 1) (by linarith)
    (by simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one]; linarith)
    (fun i => by cases i with
      | none => exact hD₀.mono D₀ hpp
      | some i => exact (hD i).mono (D i) hpp)
  simpa only [optionProduct, show p + 1 + 2 = p + 3 by ring] using h

variable {H : Type u} [LieRing H] [LieAlgebra ℚ H]

def optionMaps (φ₀ : H →ₗ⁅ℚ⁆ L₀) (φ : ∀ i, H →ₗ⁅ℚ⁆ L i) :
    ∀ i : Option ι, H →ₗ⁅ℚ⁆ optionLieSpace L₀ L i
  | none => φ₀
  | some i => φ i

def optionProductMap (φ₀ : H →ₗ⁅ℚ⁆ L₀) (φ : ∀ i, H →ₗ⁅ℚ⁆ L i) :
    H →ₗ⁅ℚ⁆ (∀ i : Option ι, optionLieSpace L₀ L i) :=
  liePiMap (optionMaps φ₀ φ)

theorem optionProductMap_logHeight {κ : Type*} (b : Basis κ ℚ H)
    (φ₀ : H →ₗ⁅ℚ⁆ L₀) (φ : ∀ i, H →ₗ⁅ℚ⁆ L i) {p : ℝ}
    (h₀ : ∀ i j, rationalLogHeight (D₀.basis.repr (φ₀ (b j)) i) ≤ p)
    (hφ : ∀ a i j, rationalLogHeight ((D a).basis.repr (φ a (b j)) i) ≤ p) :
    ∀ i j, rationalLogHeight ((optionProduct D₀ D).basis.repr (optionProductMap φ₀ φ (b j)) i) ≤ p := by
  intro i j
  dsimp only [optionProduct]
  rw [productFinBasis_repr]
  generalize hz : (Fintype.equivFin (Σ i : Option ι, Fin (optionDimension d₀ d i))).symm i = z
  rcases z with ⟨a, k⟩
  cases a with
  | none => exact h₀ k j
  | some a => exact hφ a k j

include D₀ D in
theorem optionProductMap_real_kernel
    (φ₀ : H →ₗ⁅ℚ⁆ L₀) (φ : ∀ i, H →ₗ⁅ℚ⁆ L i) (x : ℝ ⊗[ℚ] H) :
    realificationLieHom (optionProductMap φ₀ φ) x = 0 ↔
      realificationLieHom φ₀ x = 0 ∧ ∀ i, realificationLieHom (φ i) x = 0 := by
  rw [optionProductMap, realification_liePiMap_eq_zero_iff (fun i => (optionFactors D₀ D i).basis)]
  constructor
  · intro h
    exact ⟨h none, fun i => h (some i)⟩
  · rintro ⟨h₀, hφ⟩ i
    cases i with
    | none => exact h₀
    | some i => exact hφ i

end RationalFilteredNilmanifold
end Erdos3

end

section

open scoped TensorProduct BigOperators NNReal

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}

noncomputable def productObservable (T : ∀ i, (D i).Niltest w) (z : (pi D).Space) : ℂ :=
  ∏ i, (T i).observable (productProjection D i z)

theorem productObservable_bounds (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p) :
    letI := (pi D).metricSpace
    (∀ z, ‖productObservable D T z‖ ≤ Real.exp p ^ Fintype.card ι) ∧
    LipschitzWith ((Fintype.card ι : ℝ≥0) *
      productExpBound (productObservableLipBudget p) *
        productExpBound p ^ Fintype.card ι) (productObservable D T) := by
  let := (pi D).metricSpace
  have hB : (1 : ℝ≥0) ≤ productExpBound p := Real.one_le_exp_iff.mpr hp
  have hnorm (i : ι) (z : (pi D).Space) :
      ‖(T i).observable (productProjection D i z)‖ ≤ Real.exp p := by
    have hb := (T i).observable_budget (hT i)
    exact ((T i).norm_le _).trans (by linarith [(T i).lipBound.coe_nonneg])
  have hlip (i : ι) : LipschitzWith
      (productExpBound (productObservableLipBudget p))
        (fun z => (T i).observable (productProjection D i z)) := by
    let := (D i).metricSpace
    apply ((T i).lipschitz.comp (productProjection_lipschitz D i)).weaken
    change (T i).lipBound *
      (coordinateLipschitzBound (d i) (Fintype.card (Σ i, Fin (d i))) 1 : ℝ) ≤ _
    have hb := (T i).observable_budget (hT i)
    have hk : ((T i).lipBound : ℝ) ≤ Real.exp p := by linarith [(T i).normBound.coe_nonneg]
    calc
      _ ≤ Real.exp p * Real.exp ((p ^ 2 + p + 3) ^ 2) :=
        mul_le_mul hk (productProjection_lipschitz_bound D hp hι (fun i => (hT i).1) i)
          (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; rfl
  exact bounded_lipschitz_fintype_prod (fun i z => (T i).observable (productProjection D i z))
    hB hlip hnorm

noncomputable def piNiltest (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p) : (pi D).Niltest w where
  orbit := NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (fun i => (T i).orbit)
  observable := productObservable D T
  normBound := productExpBound p ^ Fintype.card ι
  lipBound := (Fintype.card ι : ℝ≥0) *
    productExpBound (productObservableLipBudget p) *
      productExpBound p ^ Fintype.card ι
  norm_le z := by simpa only [NNReal.coe_pow, coe_productExpBound] using (productObservable_bounds D T hp hι hT).1 z
  lipschitz := (productObservable_bounds D T hp hι hT).2

theorem piNiltest_eval (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p) (x : σ → ℤ) :
    (piNiltest D T hp hι hT).eval x = ∏ i, (T i).eval x := by
  change (∏ i, (T i).observable (productProjection D i
    (QuotientGroup.mk ((pi D).filtration.realification.polynomialOrbitEval w x
      (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (fun i => (T i).orbit)))))) = _
  apply Finset.prod_congr rfl
  intro i _
  rw [productProjection_mk]
  exact congrArg (fun g => (T i).observable (QuotientGroup.mk g))
    (NilpotentLieFiltration.piRealOrbit_eval (fun i => (D i).filtration) (fun i => (T i).orbit) x i)

theorem piNiltest_complexity (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p) :
    (piNiltest D T hp hι hT).ComplexityLE (productNiltestBudget p) := by
  constructor
  · exact GeometryComplexityLE.mono (pi D) (pi_geometry D hp hι (fun i => (hT i).1))
      (productNiltestBudget_geometry hp)
  · change Real.log (2 + (Real.exp p) ^ Fintype.card ι +
      (Fintype.card ι : ℝ) * Real.exp (productObservableLipBudget p) * (Real.exp p) ^ Fintype.card ι) ≤ _
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    exact productNiltestBudget_observable hp _ hι

end Erdos3.RationalFilteredNilmanifold

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

theorem exists_product_niltest {ι σ : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}
    (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p) :
    letI : FiniteDimensional ℚ (∀ i, L i) := (productFinBasis D).finiteDimensional_of_finite
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i)) := IsModuleTopology.topologicalAddGroup ℝ _
    letI : T2Space (ℝ ⊗[ℚ] (∀ i, L i)) := realification_moduleTopology_t2 (productFinBasis D)
    ∃ S : (pi D).Niltest w, S.ComplexityLE (productNiltestBudget p) ∧
      ∀ x, S.eval x = ∏ i, (T i).eval x := by
  let : FiniteDimensional ℚ (∀ i, L i) := (productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, L i)) := realification_moduleTopology_t2 (productFinBasis D)
  exact ⟨piNiltest D T hp hι hT, piNiltest_complexity D T hp hι hT, piNiltest_eval D T hp hι hT⟩

end Erdos3.RationalFilteredNilmanifold

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productProjection_smul (i : ι) (g : (pi D).RealGroup) (x : (pi D).Space) :
    productProjection D i (g • x) = productProjectionHom D i g • productProjection D i x :=
  cosetMap_smul _ _ _ _ g x

theorem productProjectionHom_mem_layer (i : ι) (k : ℕ) (g : (pi D).RealGroup)
    (hg : g ∈ (pi D).filtration.realification.subgroup k) :
    productProjectionHom D i g ∈ (D i).filtration.realification.subgroup k := by
  apply baseChange_mem_of_mapsTo ((pi D).filtration.layer k) ((D i).filtration.layer k)
    (liePiEval i).toLinearMap _ hg
  intro x hx
  exact (NilpotentLieFiltration.mem_pi_layer (fun i => (D i).filtration) k x).mp hx i

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  {w : σ → ℕ}

omit [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))] in
theorem productObservable_vertical (T : ∀ i, (D i).Niltest w)
    (eta : ∀ i, L i →ₗ[ℚ] ℚ)
    (hvert : ∀ i z, z ∈ (D i).filtration.realification.subgroup s → ∀ x,
      (T i).observable (z • x) =
        CircleFourier.character ((realifyFunctional (eta i) z.coord : ℝ) : CircleFourier.Circle) *
          (T i).observable x)
    (z : (pi D).RealGroup) (hz : z ∈ (pi D).filtration.realification.subgroup s)
    (x : (pi D).Space) :
    productObservable D T (z • x) =
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) *
        productObservable D T x := by
  have hchar :
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) =
        ∏ i, CircleFourier.character
          ((realifyFunctional (eta i) (productProjectionHom D i z).coord : ℝ) : CircleFourier.Circle) := by
    rw [realify_piFrequency]
    have hcoe (f : ι → ℝ) : ((∑ i, f i : ℝ) : CircleFourier.Circle) =
        ∑ i, (f i : CircleFourier.Circle) :=
      map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f Finset.univ
    simp only [hcoe, CircleFourier.character_fintype_sum,
      productProjectionHom, NilpotentLieBCHGroup.realificationMap_coord]
  rw [hchar, productObservable, productObservable, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [productProjection_smul]
  exact hvert i _ (productProjectionHom_mem_layer D i s z hz) _

theorem piNiltest_vertical (T : ∀ i, (D i).Niltest w)
    (eta : ∀ i, L i →ₗ[ℚ] ℚ) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hvert : ∀ i z, z ∈ (D i).filtration.realification.subgroup s → ∀ x,
      (T i).observable (z • x) =
        CircleFourier.character ((realifyFunctional (eta i) z.coord : ℝ) : CircleFourier.Circle) *
          (T i).observable x)
    (z : (pi D).RealGroup) (hz : z ∈ (pi D).filtration.realification.subgroup s)
    (x : (pi D).Space) :
    (piNiltest D T hp hι hT).observable (z • x) =
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) *
        (piNiltest D T hp hι hT).observable x :=
  productObservable_vertical D T eta hvert z hz x

theorem piNiltest_orbit_eq (T U : ∀ i, (D i).Niltest w) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hιp : (Fintype.card ι : ℝ) ≤ p)
    (hιq : (Fintype.card ι : ℝ) ≤ q)
    (hT : ∀ i, (T i).ComplexityLE p) (hU : ∀ i, (U i).ComplexityLE q)
    (horbit : ∀ i, (T i).orbit = (U i).orbit) :
    (piNiltest D T hp hιp hT).orbit = (piNiltest D U hq hιq hU).orbit := by
  change NilpotentLieFiltration.piRealOrbit _ _ = NilpotentLieFiltration.piRealOrbit _ _
  exact congrArg (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration)) (funext horbit)

end Erdos3.RationalFilteredNilmanifold

end

section

open scoped TensorProduct BigOperators NNReal

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}

omit [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))] in
theorem productObservable_norm_le_one (T : ∀ i, (D i).Niltest w)
    (hcap : ∀ i, (T i).normBound ≤ 1) (x : (pi D).Space) :
    ‖productObservable D T x‖ ≤ 1 := by
  unfold productObservable
  calc
    _ = ∏ i, ‖(T i).observable (productProjection D i x)‖ := norm_prod _ _
    _ ≤ ∏ _i : ι, (1 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun i _ => ((T i).norm_le _).trans (by exact_mod_cast hcap i))
    _ = 1 := by simp

noncomputable def unitBoundedPiNiltest (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hcap : ∀ i, (T i).normBound ≤ 1) : (pi D).Niltest w :=
  { piNiltest D T hp hι hT with
    normBound := 1
    norm_le := productObservable_norm_le_one D T hcap }

theorem unitBoundedPiNiltest_normBound (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hcap : ∀ i, (T i).normBound ≤ 1) :
    (unitBoundedPiNiltest D T hp hι hT hcap).normBound = 1 := rfl

theorem unitBoundedPiNiltest_eval (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hcap : ∀ i, (T i).normBound ≤ 1) (x : σ → ℤ) :
    (unitBoundedPiNiltest D T hp hι hT hcap).eval x = ∏ i, (T i).eval x :=
  piNiltest_eval D T hp hι hT x

theorem unitBoundedPiNiltest_complexity (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hcap : ∀ i, (T i).normBound ≤ 1) :
    (unitBoundedPiNiltest D T hp hι hT hcap).ComplexityLE (productNiltestBudget p) := by
  have h := piNiltest_complexity D T hp hι hT
  refine ⟨h.1, le_trans ?_ h.2⟩
  apply Real.log_le_log (by positivity)
  change 2 + 1 + ((piNiltest D T hp hι hT).lipBound : ℝ) ≤
    2 + Real.exp p ^ Fintype.card ι + ((piNiltest D T hp hι hT).lipBound : ℝ)
  have hb : 1 ≤ Real.exp p ^ Fintype.card ι := one_le_pow₀ (Real.one_le_exp_iff.mpr hp)
  linarith

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem complex_prod_unit_interval {I : Type*} [Fintype I] (a : I → ℂ)
    (ha : ∀ i, (a i).im = 0 ∧ 0 ≤ (a i).re ∧ (a i).re ≤ 1) :
    (∏ i, a i).im = 0 ∧ 0 ≤ (∏ i, a i).re ∧ (∏ i, a i).re ≤ 1 := by
  have he (i : I) : a i = ((a i).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using (ha i).1
  have hprod : (∏ i, a i) = ((∏ i, (a i).re : ℝ) : ℂ) := by
    calc
      _ = ∏ i, ((a i).re : ℂ) := Finset.prod_congr rfl (fun i _ => he i)
      _ = _ := by rw [Complex.ofReal_prod]
  rw [hprod]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
  exact ⟨Finset.prod_nonneg (fun i _ => (ha i).2.1),
    Finset.prod_le_one₀ (fun i _ => (ha i).2.1) (fun i _ => (ha i).2.2)⟩

namespace RationalFilteredNilmanifold

theorem piNiltest_unit_interval {ι σ : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}
    (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hunit : ∀ i, (T i).UnitIntervalValued) :
    (piNiltest D T hp hι hT).UnitIntervalValued := by
  intro z
  exact complex_prod_unit_interval (fun i => (T i).observable (productProjection D i z))
    (fun i => hunit i _)

namespace Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem unit_interval_eval (T : D.Niltest w) (hT : T.UnitIntervalValued) (x : σ → ℤ) :
    (T.eval x).im = 0 ∧ 0 ≤ (T.eval x).re ∧ (T.eval x).re ≤ 1 := hT _

theorem unit_interval_evalCyclic (T : D.Niltest w) (hT : T.UnitIntervalValued)
    (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (T.evalCyclic N x).im = 0 ∧ 0 ≤ (T.evalCyclic N x).re ∧ (T.evalCyclic N x).re ≤ 1 := hT _

end Niltest
end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_cellwise_niltest_error
    {I J : Type*} [Fintype I] [Fintype J] (N : ℕ) [NeZero N]
    {K : ZMod N → Type*} [∀ h, LieRing (K h)] [∀ h, LieAlgebra ℚ (K h)]
    [∀ h, TopologicalSpace (ℝ ⊗[ℚ] K h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] K h)]
    [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] K h)] [∀ h, T2Space (ℝ ⊗[ℚ] K h)]
    {s : ℕ} {d : ZMod N → ℕ} (D : ∀ h, RationalFilteredNilmanifold (K h) s (d h))
    (U : I → J → (h : ZMod N) → (D h).Niltest (fun _ : Unit => 1))
    (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ)
    (T : ZMod N → ZMod N → ℝ) (E : ZMod N → Finset (ZMod N))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hA : ∀ i n, 0 ≤ A i n) (hB : ∀ j n, 0 ≤ B j n)
    (hAsum : ∀ n, ∑ i, A i n = 1) (hBsum : ∀ n, ∑ j, B j n = 1)
    (hT : ∀ h n, 0 ≤ T h n ∧ T h n ≤ 1)
    (hU : ∀ i j h, (U i j h).UnitIntervalValued)
    (hgood : ∀ h n, n ∉ E h →
      |T h n - ∑ i, ∑ j, A i n * B j (n + h) *
        ((U i j h).evalCyclic N (fun _ : Unit => n)).re| ≤ ε) :
    ∃ e : ZMod N → ZMod N → ℝ,
      (∀ h n, T h n = (∑ i, ∑ j, A i n * B j (n + h) *
        ((U i j h).evalCyclic N (fun _ : Unit => n)).re) + e h n) ∧
      ∀ h, (𝔼 n, |e h n|) ≤ ε + ((E h).card : ℝ) / N := by
  let e : ZMod N → ZMod N → ℝ := fun h n =>
    T h n - ∑ i, ∑ j, A i n * B j (n + h) * ((U i j h).evalCyclic N (fun _ : Unit => n)).re
  refine ⟨e, fun h n => by dsimp [e]; ring, ?_⟩
  intro h
  have hmean := positive_partition_approximation_mean_error (E h)
    (fun ij : I × J => fun n => A ij.1 n * B ij.2 (n + h))
    (fun ij : I × J => fun n => ((U ij.1 ij.2 h).evalCyclic N (fun _ : Unit => n)).re)
    (T h) hε
    (fun ij n => mul_nonneg (hA ij.1 n) (hB ij.2 (n + h)))
    (fun n => sum_pair_partition_weights (fun i => A i n) (fun j => B j (n + h))
      (hAsum n) (hBsum (n + h)))
    (fun ij n => ((U ij.1 ij.2 h).unit_interval_evalCyclic (hU ij.1 ij.2 h) N (fun _ : Unit => n)).2)
    (hT h) (fun n hn => by simpa only [Fintype.sum_prod_type] using hgood h n hn)
  simpa only [e, Fintype.sum_prod_type, ZMod.card] using hmean

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

theorem exists_cyclic_cellwise_niltest_approximation
    {I J Ξ : Type*} [Fintype I] [Fintype J] [PseudoMetricSpace Ξ]
    (N : ℕ) [NeZero N] {K : ZMod N → Type*}
    [∀ h, LieRing (K h)] [∀ h, LieAlgebra ℚ (K h)] {s : ℕ} {d : ZMod N → ℕ}
    [∀ h, TopologicalSpace (ℝ ⊗[ℚ] K h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] K h)]
    [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] K h)] [∀ h, T2Space (ℝ ⊗[ℚ] K h)]
    (D : ∀ h, RationalFilteredNilmanifold (K h) s (d h))
    (g : ∀ h, (D h).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (F : I → ∀ h, (D h).Space → Ξ → ℝ)
    (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ)
    (xi : ZMod N → ZMod N → Ξ) (T : ZMod N → ZMod N → ℝ)
    {L M : ℝ≥0} {ρ δ η p : ℝ} (hρ : 0 < ρ) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hA : ∀ i n, 0 ≤ A i n) (hB : ∀ j n, 0 ≤ B j n)
    (hAsum : ∀ n, ∑ i, A i n = 1) (hBsum : ∀ n, ∑ j, B j n = 1)
    (hF : ∀ i h z a, 0 ≤ F i h z a ∧ F i h z a ≤ 1)
    (hFirstLip : ∀ i h, let := (D h).metricSpace; ∀ a, LipschitzWith M (fun z => F i h z a))
    (hSecondLip : ∀ i h z, LipschitzWith L (F i h z))
    (hGeometry : ∀ h, (D h).GeometryComplexityLE p)
    (hBudget : Real.log (3 + (M : ℝ)) ≤ p)
    (hT : ∀ h n, 0 ≤ T h n ∧ T h n ≤ 1)
    (happrox : ∀ i h n, n ∉ cyclicWrapExceptional h ρ → 0 < A i n →
      |T h n - F i h ((D h).cyclicOrbitPoint (g h) N (fun _ : Unit => n)) (xi h n)| ≤ δ)
    (hdiam : ∀ i j h n n', n ∉ cyclicWrapExceptional h ρ → n' ∉ cyclicWrapExceptional h ρ →
      0 < A i n * B j (n + h) → 0 < A i n' * B j (n' + h) → dist (xi h n) (xi h n') ≤ η) :
    ∃ U : I → J → (h : ZMod N) → (D h).Niltest (fun _ : Unit => 1),
      (∀ i j h, (U i j h).UnitIntervalValued) ∧
      (∀ i j h, (U i j h).ComplexityLE p) ∧
      (∀ i j h, (¬∃ n, n ∉ cyclicWrapExceptional h ρ ∧ 0 < A i n * B j (n + h)) →
        ∀ x, (U i j h).eval x = 0) ∧
      (∀ h n, n ∉ cyclicWrapExceptional h ρ →
        |T h n - ∑ i, ∑ j, A i n * B j (n + h) *
          ((U i j h).evalCyclic N (fun _ : Unit => n)).re| ≤ δ + L * η) ∧
      ∃ e : ZMod N → ZMod N → ℝ,
        (∀ h n, T h n = (∑ i, ∑ j, A i n * B j (n + h) *
          ((U i j h).evalCyclic N (fun _ : Unit => n)).re) + e h n) ∧
        ∀ h, (𝔼 n, |e h n|) ≤ δ + L * η + 6 * ρ + 3 / N := by
  obtain ⟨U, hU, hUcomplexity, hUempty, hgood⟩ := exists_cellwise_niltest_discretization
    N D g F A B (fun h => ↑(cyclicWrapExceptional h ρ)) xi T
    hA hB hAsum hBsum hF hFirstLip hSecondLip hGeometry hBudget happrox hdiam
  have herror : 0 ≤ δ + (L : ℝ) * η := add_nonneg hδ (mul_nonneg L.coe_nonneg hη)
  obtain ⟨e, heval, hmean⟩ := exists_cellwise_niltest_error N D U A B T
    (fun h => cyclicWrapExceptional h ρ) herror hA hB hAsum hBsum hT hU hgood
  refine ⟨U, hU, hUcomplexity, hUempty, hgood, e, heval, ?_⟩
  intro h
  calc
    _ ≤ δ + (L : ℝ) * η + ((cyclicWrapExceptional h ρ).card : ℝ) / N := hmean h
    _ ≤ δ + (L : ℝ) * η + (6 * ρ + 3 / N) := by
      linarith [cyclicWrapExceptional_density_le h hρ.le]
    _ = _ := by ring

end Erdos3

end

end OAI
