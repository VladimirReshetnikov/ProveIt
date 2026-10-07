/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Isometry
import OAI.Combinatorics.Progressions.Geometry.NativeProductOrbitMetric
import OAI.Combinatorics.Progressions.Geometry.OptionProductMetric
import OAI.Combinatorics.Progressions.Geometry.ProductComponentCoordinates
import OAI.Combinatorics.Progressions.Geometry.SquarefreeActionMetric
import OAI.Combinatorics.Progressions.Lattices.SourceLatticeCover

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {L : Option ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : Option ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def optionProductSpaceEquiv :
    (pi D).Space ≃ (D none).Space × (pi (fun i => D (some i))).Space :=
  ((productSpaceEquiv D).trans Equiv.piOptionEquivProd).trans
    (Equiv.prodCongr (Equiv.refl _) (productSpaceEquiv (fun i => D (some i))).symm)

theorem optionProductSpaceEquiv_apply (x : (pi D).Space) :
    optionProductSpaceEquiv D x =
      (productSpaceEquiv D x none,
        (productSpaceEquiv (fun i => D (some i))).symm (fun i => productSpaceEquiv D x (some i))) := rfl

theorem optionProductSpaceEquiv_symm_apply
    (x : (D none).Space × (pi (fun i => D (some i))).Space) :
    (optionProductSpaceEquiv D).symm x =
      (productSpaceEquiv D).symm
        (Equiv.piOptionEquivProd.symm (x.1, productSpaceEquiv (fun i => D (some i)) x.2)) := rfl

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [T2Space (ℝ ⊗[ℚ] (∀ i, L (some i)))]

theorem optionProductSpaceEquiv_lipschitz :
    letI := (pi D).metricSpace
    letI := (D none).metricSpace
    letI := (pi (fun i => D (some i))).metricSpace
    LipschitzWith ((1 + productMetricBound (fun i => d (some i))) * productMetricBound d)
      (optionProductSpaceEquiv D) := by
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  let := (pi (fun i => D (some i))).metricSpace
  have hpair : LipschitzWith (1 + productMetricBound (fun i => d (some i)))
      (fun x : (D none).Space × (∀ i, (D (some i)).Space) =>
        (x.1, (productSpaceEquiv (fun i => D (some i))).symm x.2)) := by
    have h := (LipschitzWith.prod_fst (α := (D none).Space)
      (β := ∀ i, (D (some i)).Space)).prodMk
      ((productSpaceEquiv_symm_lipschitz (fun i => D (some i))).comp
        (LipschitzWith.prod_snd (α := (D none).Space)))
    apply h.weaken
    simp only [mul_one]
    exact max_le (le_add_of_nonneg_right zero_le) (le_add_of_nonneg_left zero_le)
  have h := hpair.comp (piOptionEquivProd_isometry.lipschitzWith.comp (productSpaceEquiv_lipschitz D))
  have heq : (optionProductSpaceEquiv D : (pi D).Space → _) =
      (fun x => ((Equiv.piOptionEquivProd (productSpaceEquiv D x)).1,
        (productSpaceEquiv (fun i => D (some i))).symm
          (Equiv.piOptionEquivProd (productSpaceEquiv D x)).2)) := rfl
  rw [heq]
  simpa only [one_mul, Function.comp_def] using h

theorem optionProductSpaceEquiv_symm_lipschitz :
    letI := (pi D).metricSpace
    letI := (D none).metricSpace
    letI := (pi (fun i => D (some i))).metricSpace
    LipschitzWith ((1 + productMetricBound (fun i => d (some i))) * productMetricBound d)
      (optionProductSpaceEquiv D).symm := by
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  let := (pi (fun i => D (some i))).metricSpace
  have hpair : LipschitzWith (1 + productMetricBound (fun i => d (some i)))
      (fun x : (D none).Space × (pi (fun i => D (some i))).Space =>
        (x.1, productSpaceEquiv (fun i => D (some i)) x.2)) := by
    have h := (LipschitzWith.prod_fst (α := (D none).Space)
      (β := (pi (fun i => D (some i))).Space)).prodMk
      ((productSpaceEquiv_lipschitz (fun i => D (some i))).comp
        (LipschitzWith.prod_snd (α := (D none).Space)))
    apply h.weaken
    simp only [mul_one]
    exact max_le (le_add_of_nonneg_right zero_le) (le_add_of_nonneg_left zero_le)
  have h := (productSpaceEquiv_symm_lipschitz D).comp
    ((optionPiIsometryEquiv (X := fun i => (D i).Space)).symm.isometry.lipschitzWith.comp hpair)
  have heq : ((optionProductSpaceEquiv D).symm : _ → (pi D).Space) =
      (fun x => (productSpaceEquiv D).symm
        ((optionPiIsometryEquiv (X := fun i => (D i).Space)).symm
          (x.1, productSpaceEquiv (fun i => D (some i)) x.2))) := rfl
  rw [heq]
  simpa only [one_mul, mul_comm, Function.comp_def] using h

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [LieRing H] [LieAlgebra ℚ H]
  {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {r t : ℕ} {d : ι → ℕ} (F : NilpotentLieFiltration H r)
  (D : ∀ i, RationalFilteredNilmanifold (L i) t (d i))

omit [DecidableEq ι] in
theorem productProjectionHom_realificationMap (φ : ∀ i, H →ₗ⁅ℚ⁆ L i)
    (x : F.realification.Group) (i : ι) :
    productProjectionHom D i
      (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := (pi D).filtration.lowerCentralSeries_eq_bot) (liePiMap φ) x) =
      realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := (D i).filtration.lowerCentralSeries_eq_bot) (φ i) x := by
  apply NilpotentLieBCHGroup.ext
  exact realification_liePiEval_liePiMap φ x.coord i

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [LieRing H] [LieAlgebra ℚ H]
  {L : Option ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {r t : ℕ} {d : Option ι → ℕ} (F : NilpotentLieFiltration H r)
  (D : ∀ i, RationalFilteredNilmanifold (L i) t (d i))

theorem optionProductSpaceEquiv_realificationMap (φ : ∀ i, H →ₗ⁅ℚ⁆ L i)
    (x : F.realification.Group) :
    optionProductSpaceEquiv D
      (QuotientGroup.mk (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := (pi D).filtration.lowerCentralSeries_eq_bot) (liePiMap φ) x)) =
      (QuotientGroup.mk (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
          (hM := (D none).filtration.lowerCentralSeries_eq_bot) (φ none) x),
        QuotientGroup.mk (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
          (hM := (pi (fun i => D (some i))).filtration.lowerCentralSeries_eq_bot)
          (liePiMap (fun i => φ (some i))) x)) := by
  rw [optionProductSpaceEquiv_apply]
  apply Prod.ext
  · simp only [productSpaceEquiv_mk, productProjectionHom_realificationMap]
  · apply (productSpaceEquiv (fun i => D (some i))).injective
    rw [Equiv.apply_symm_apply]
    funext i
    simp only [productSpaceEquiv_mk, productProjectionHom_realificationMap]

omit [DecidableEq ι] in
theorem lowered_productProjectionHom_realificationMap {s n : ℕ}
    (Q : RationalFilteredNilmanifold (L none) s n) (φ : ∀ i, H →ₗ⁅ℚ⁆ L i)
    (x : F.realification.Group) :
    changeStep (D none).filtration.realification.lowerCentralSeries_eq_bot
      Q.filtration.realification.lowerCentralSeries_eq_bot
      (productProjectionHom D none (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := (pi D).filtration.lowerCentralSeries_eq_bot) (liePiMap φ) x)) =
      realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (φ none) x := by
  rw [productProjectionHom_realificationMap]
  rfl

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (E : RationalFilteredNilmanifold L s d)

noncomputable def singletonProductSpace (y : E.Space) :
    (pi (fun _ : Unit => E)).Space :=
  (productSpaceEquiv (fun _ : Unit => E)).symm (fun _ => y)

@[simp] theorem productSpaceEquiv_singletonProductSpace (y : E.Space) (i : Unit) :
    productSpaceEquiv (fun _ : Unit => E) (E.singletonProductSpace y) i = y := by
  simp only [singletonProductSpace, Equiv.apply_symm_apply]

theorem productMetricBound_singleton (d : ℕ) :
    productMetricBound (fun _ : Unit => d) = coordinateLipschitzBound d d 1 := by
  simp [productMetricBound, Fintype.card_sigma]

theorem productMetricBound_singleton_le_exp {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) :
    (productMetricBound (fun _ : Unit => d) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
  rw [productMetricBound_singleton]
  exact coordinateLipschitzBound_le_exp d d 1 hp hd hd
    (by simpa only [NNReal.coe_one] using Real.one_le_exp hp)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] (Unit → L))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Unit → L))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Unit → L))] [T2Space (ℝ ⊗[ℚ] (Unit → L))]

theorem singletonProductSpace_lipschitz :
    letI := E.metricSpace
    letI := (pi (fun _ : Unit => E)).metricSpace
    LipschitzWith (productMetricBound (fun _ : Unit => d)) E.singletonProductSpace := by
  let := E.metricSpace
  let : ∀ _ : Unit, MetricSpace E.Space := fun _ => E.metricSpace
  let := (pi (fun _ : Unit => E)).metricSpace
  have hconstant : LipschitzWith 1 (fun y : E.Space => fun _ : Unit => y) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    apply (dist_pi_le_iff (by positivity)).mpr
    intro i
    simp only [NNReal.coe_one, one_mul, le_refl]
  have h := (productSpaceEquiv_symm_lipschitz (fun _ : Unit => E)).comp hconstant
  rw [mul_one] at h
  exact h

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] (Unit → L))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Unit → L))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Unit → L))] [T2Space (ℝ ⊗[ℚ] (Unit → L))] in

theorem singletonProductSpace_realificationMap
    {H : Type*} [LieRing H] [LieAlgebra ℚ H] {r : ℕ}
    (F : NilpotentLieFiltration H r) (φ : H →ₗ⁅ℚ⁆ L)
    (x : F.realification.Group) :
    E.singletonProductSpace
        (QuotientGroup.mk (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ x)) =
      QuotientGroup.mk (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := (pi (fun _ : Unit => E)).filtration.lowerCentralSeries_eq_bot)
        (liePiMap (fun _ : Unit => φ)) x) := by
  apply (productSpaceEquiv (fun _ : Unit => E)).injective
  rw [singletonProductSpace, Equiv.apply_symm_apply]
  funext i
  rw [productSpaceEquiv_mk, productProjectionHom_realificationMap]

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type v} {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [LieAlgebra ℚ L₀] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

def optionComplementMaps : ∀ j : {j : Option ι // j ≠ none},
    (∀ i, L i) →ₗ⁅ℚ⁆ optionLieSpace L₀ L j.val
  | ⟨none, h⟩ => False.elim (h rfl)
  | ⟨some i, _⟩ => liePiEval i

def optionComplementMap : (∀ i, L i) →ₗ⁅ℚ⁆
    (∀ j : {j : Option ι // j ≠ none}, optionLieSpace L₀ L j.val) :=
  liePiMap (optionComplementMaps (L₀ := L₀) (L := L))

theorem optionComplementMap_some (x : ∀ i, L i) (i : ι) (h : some i ≠ (none : Option ι)) :
    optionComplementMap (L₀ := L₀) x ⟨some i, h⟩ = x i := rfl

theorem optionComplementMap_comp_someProjection :
    (optionComplementMap (L₀ := L₀) (L := L)).comp
      (liePiMap (fun i => (liePiEval (some i) :
        (∀ j : Option ι, optionLieSpace L₀ L j) →ₗ⁅ℚ⁆ L i))) =
      liePiMap (fun j : {j : Option ι // j ≠ none} => liePiEval j.val) := by
  ext x j
  rcases j with ⟨j, hj⟩
  cases j with
  | none => exact False.elim (hj rfl)
  | some i => rfl

namespace RationalFilteredNilmanifold

variable [Fintype ι] [DecidableEq ι] {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def optionComplementFactors : ∀ j : {j : Option ι // j ≠ none},
    RationalFilteredNilmanifold (optionLieSpace L₀ L j.val) s (optionDimension d₀ d j.val) :=
  fun j => optionFactors D₀ D j.val

omit [DecidableEq ι] in
theorem optionComplementMap_logHeight
    (i : Fin (Fintype.card (Σ j : {j : Option ι // j ≠ none}, Fin (optionDimension d₀ d j.val))))
    (j : Fin (Fintype.card (Σ i, Fin (d i)))) :
    rationalLogHeight ((pi (optionComplementFactors D₀ D)).basis.repr
      (optionComplementMap (L₀ := L₀) ((pi D).basis j)) i) = 0 := by
  rw [productFinBasis_repr]
  generalize heq : (Fintype.equivFin
    (Σ j : {j : Option ι // j ≠ none}, Fin (optionDimension d₀ d j.val))).symm i = z
  rcases z with ⟨⟨z, hz⟩, k⟩
  cases z with
  | none => exact False.elim (hz rfl)
  | some a =>
    change Fin (d a) at k
    change rationalLogHeight ((D a).basis.repr (((pi D).basis j) a) k) = 0
    rw [productFinBasis_repr_component D, Basis.repr_self]
    by_cases h : j = Fintype.equivFin (Σ i, Fin (d i)) ⟨a, k⟩ <;> simp [h, rationalLogHeight]

omit [DecidableEq ι] in
theorem optionComplementMap_lattice :
    (pi D).lattice ≤ (pi (optionComplementFactors D₀ D)).lattice.comap
      (mapOfSteps (hL := (pi D).filtration.lowerCentralSeries_eq_bot)
        (hM := (pi (optionComplementFactors D₀ D)).filtration.lowerCentralSeries_eq_bot)
        (optionComplementMap (L₀ := L₀))) := by
  intro x hx
  apply (mem_piBCHSubgroup _ _ _).mpr
  rintro ⟨j, hj⟩
  cases j with
  | none => exact False.elim (hj rfl)
  | some i => exact (mem_piBCHSubgroup _ _ x).mp hx i

noncomputable def optionComplementOrbits {σ : Type*} {w : σ → ℕ}
    (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w) :
    ∀ j, ((optionComplementFactors D₀ D) j).filtration.realification.PolynomialOrbit w
  | ⟨none, h⟩ => False.elim (h rfl)
  | ⟨some i, _⟩ => g i

theorem optionComplementMap_piRealOrbit_eval {σ : Type*} {w : σ → ℕ}
    (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    realificationMap (hnil := (pi D).filtration.lowerCentralSeries_eq_bot)
      (hM := (pi (optionComplementFactors D₀ D)).filtration.lowerCentralSeries_eq_bot)
      (optionComplementMap (L₀ := L₀))
      ((pi D).filtration.realification.polynomialOrbitEval w x
        (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) g)) =
      (pi (optionComplementFactors D₀ D)).filtration.realification.polynomialOrbitEval w x
        (NilpotentLieFiltration.piRealOrbit
          (fun j => ((optionComplementFactors D₀ D) j).filtration) (optionComplementOrbits D₀ D g)) := by
  apply (realBCHPiEquiv (fun j => ((optionComplementFactors D₀ D) j).filtration)).injective
  funext j
  change productProjectionHom (optionComplementFactors D₀ D) j
      (realificationMap (optionComplementMap (L₀ := L₀)) _) = _
  rw [optionComplementMap, productProjectionHom_realificationMap]
  rcases j with ⟨j, hj⟩
  cases j with
  | none => exact False.elim (hj rfl)
  | some i =>
    exact (NilpotentLieFiltration.piRealOrbit_eval (fun i => (D i).filtration) g x i).trans
      (NilpotentLieFiltration.piRealOrbit_eval
        (fun j => ((optionComplementFactors D₀ D) j).filtration) (optionComplementOrbits D₀ D g) x
        ⟨some i, hj⟩).symm

end RationalFilteredNilmanifold
end Erdos3

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup NilpotentLieFiltration
open scoped TensorProduct

theorem exists_option_complement_cover :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type v} [Fintype ι] [DecidableEq ι]
      {L₀ : Type u} {L : ι → Type u}
      [LieRing L₀] [LieAlgebra ℚ L₀] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      {s d₀ : ℕ} {d : ι → ℕ}
      (D₀ : RationalFilteredNilmanifold L₀ s d₀)
      (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)),
      let Z₀ := pi (optionComplementFactors D₀ D)
      ∀ (Λ : Subgroup Z₀.filtration.Group) (n : ℕ) (hn : 0 < n)
        (hin : scaledIntegerGrid n ⊆ bchSubgroupCoordinates Z₀.basis Λ)
        (hout : bchSubgroupCoordinates Z₀.basis Λ ⊆ denominatorGrid n),
      let V := Z₀.withLattice Λ n hn hin hout
      ∀ {p : ℝ}, 0 ≤ p → (pi D).GeometryComplexityLE p → V.GeometryComplexityLE p →
      ∃ Γ : Subgroup (pi D).filtration.Group,
        Γ ≤ (pi D).lattice ∧ (Γ.subgroupOf (pi D).lattice).Characteristic ∧
        (Γ.subgroupOf (pi D).lattice).Normal ∧ (Γ.subgroupOf (pi D).lattice).FiniteIndex ∧
        (Γ.relIndex (pi D).lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (m : ℕ) (hm : 0 < m)
          (hmin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (pi D).basis Γ)
          (hmout : bchSubgroupCoordinates (pi D).basis Γ ⊆ denominatorGrid m),
          let W := (pi D).withLattice Γ m hm hmin hmout
          W.GeometryComplexityLE ((p + C) ^ C) ∧
          Γ ≤ V.lattice.comap (mapOfSteps (hL := W.filtration.lowerCentralSeries_eq_bot)
            (hM := V.filtration.lowerCentralSeries_eq_bot) (optionComplementMap (L₀ := L₀))) ∧
          ∀ [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))]
            [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
            [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))]
            [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
            [TopologicalSpace (ℝ ⊗[ℚ] (∀ j : {j : Option ι // j ≠ none}, optionLieSpace L₀ L j.val))]
            [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ j : {j : Option ι // j ≠ none}, optionLieSpace L₀ L j.val))]
            [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ j : {j : Option ι // j ≠ none}, optionLieSpace L₀ L j.val))]
            [T2Space (ℝ ⊗[ℚ] (∀ j : {j : Option ι // j ≠ none}, optionLieSpace L₀ L j.val))],
          letI := W.metricSpace
          letI := V.metricSpace
          ∀ {σ : Type*} {w : σ → ℕ}
            (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w) (x y : σ → ℤ),
            dist (QuotientGroup.mk (Z₀.filtration.realification.polynomialOrbitEval w x
                (piRealOrbit (fun j => ((optionComplementFactors D₀ D) j).filtration)
                  (optionComplementOrbits D₀ D g))) : V.Space)
              (QuotientGroup.mk (Z₀.filtration.realification.polynomialOrbitEval w y
                (piRealOrbit (fun j => ((optionComplementFactors D₀ D) j).filtration)
                  (optionComplementOrbits D₀ D g)))) ≤
                Real.exp ((p + C) ^ C) *
                  dist (QuotientGroup.mk ((pi D).filtration.realification.polynomialOrbitEval w x
                    (piRealOrbit (fun i => (D i).filtration) g)) : W.Space)
                    (QuotientGroup.mk ((pi D).filtration.realification.polynomialOrbitEval w y
                      (piRealOrbit (fun i => (D i).filtration) g))) := by
  obtain ⟨F, _, hcover⟩ := exists_native_source_cover
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C F) ^ F
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + 3) ^ 2)
  refine ⟨C, hC, ?_⟩
  dsimp only
  intro ι _ _ L₀ L _ _ _ _ s d₀ d D₀ D Λ n hn hin hout p hp hD hV
  let V := (pi (optionComplementFactors D₀ D)).withLattice Λ n hn hin hout
  have hφ (i j) : rationalLogHeight (V.basis.repr
      (optionComplementMap (L₀ := L₀) ((pi D).basis j)) i) ≤ p := by
    change rationalLogHeight ((pi (optionComplementFactors D₀ D)).basis.repr
      (optionComplementMap (L₀ := L₀) ((pi D).basis j)) i) ≤ p
    rw [optionComplementMap_logHeight]
    exact hp
  obtain ⟨Γ, hΓ, hchar, hnormal, hfinite, hindex, m, hm, hmin, hmout, hW, hmap⟩ :=
    hcover (pi D) V (optionComplementMap (L₀ := L₀)) hp hD hV hφ
  let W := (pi D).withLattice Γ m hm hmin hmout
  let t := p + (p + F) ^ F
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hFt : (p + F) ^ F ≤ t := le_add_of_nonneg_left hp
  have htotal : t + (t + 3) ^ 2 ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := by nlinarith [sq_nonneg (t + 3)]
  have hmetric : (t + 3) ^ 2 ≤ (p + C) ^ C := by linarith
  refine ⟨Γ, hΓ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr (hFt.trans htC)), m, hm, hmin, hmout,
    hW.mono W (hFt.trans htC), hmap, ?_⟩
  intro _ _ _ _ _ _ _ _
  let := W.metricSpace
  let := V.metricSpace
  intro σ w g x y
  have hh := nativeMap_dist_le W V (optionComplementMap (L₀ := L₀)) hmap ht
    (hW.mono W hFt) (hV.mono V hpt) (fun i j => (hφ i j).trans hpt)
    ((pi D).filtration.realification.polynomialOrbitEval w x
      (piRealOrbit (fun i => (D i).filtration) g))
    ((pi D).filtration.realification.polynomialOrbitEval w y
      (piRealOrbit (fun i => (D i).filtration) g))
  rw [optionComplementMap_piRealOrbit_eval, optionComplementMap_piRealOrbit_eval] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hmetric) dist_nonneg)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
