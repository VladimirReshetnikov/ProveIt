import Mathlib.MeasureTheory.Measure.OpenPos
import OAI.Combinatorics.Progressions.Estimates.DependentPiProduct
import OAI.Combinatorics.Progressions.Geometry.MixedCoveredChart
import OAI.Combinatorics.Progressions.Geometry.RestrictedChartReindex

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def mixedCoveredJetEquiv (d : ℕ) :
    ((∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) ≃ᵐ CoveredJetChartSource U O B n d :=
  (dependentPiProd (Fin m)
    (fun j => (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
    (fun j => O j → B j → ZMod d)).symm.trans
      (MeasurableEquiv.piCongrRight (fun j =>
        arrayResidueChart (O := O j) (Z := Fin (n j)) (R := B j → ZMod d) (o j)))

omit [∀ j, Fintype (O j)] in
theorem mixedCoveredJetEquiv_apply (d : ℕ)
    (p : (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) :
    mixedCoveredJetEquiv U o d p = mixedCoveredJetCoordinates U o d p := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical BigOperators ENNReal

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coveredJetArrayReference (d : ℕ) [NeZero d] :
    Measure ((∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) :=
  (Measure.pi (fun j =>
    (ENNReal.ofReal (ZLattice.covolume
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))))⁻¹ ^
        Fintype.card (O j) • mixedArrayReference (I j) (Fin (n j)) (O j))).prod
    (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem coveredJetArrayReference_eq_smul (d : ℕ) [NeZero d] :
    coveredJetArrayReference (O := O) (I := I) (B := B) (n := n) U d =
      (∏ j, (ENNReal.ofReal (ZLattice.covolume
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))))⁻¹ ^
          Fintype.card (O j)) •
        ((Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod
          (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure) := by
  unfold coveredJetArrayReference
  rw [pi_smul_finite _ _ (fun j => ENNReal.pow_ne_top
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos _ volume)).ne')),
    Measure.prod_smul_left]

theorem coveredJetArrayReference_sigmaFinite (d : ℕ) [NeZero d] :
    SigmaFinite (coveredJetArrayReference (O := O) (I := I) (B := B) (n := n) U d) := by
  let c := fun j => (ENNReal.ofReal (ZLattice.covolume
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))))⁻¹
  have hc (j) : c j ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos _ volume)).ne'
  let : ∀ j, SigmaFinite (c j ^ Fintype.card (O j) •
      mixedArrayReference (I j) (Fin (n j)) (O j)) := fun j =>
    ennreal_smul_sigmaFinite (mixedArrayReference (I j) (Fin (n j)) (O j)) _
      (ENNReal.pow_ne_top (hc j))
  unfold coveredJetArrayReference
  infer_instance

theorem mixedCoveredJetEquiv_measurePreserving
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))) (d : ℕ) [NeZero d] :
    MeasurePreserving (mixedCoveredJetEquiv (O := O) (B := B) (n := n) U o d)
      (coveredJetArrayReference U d) (coveredJetReference U d) := by
  let c := fun j => (ENNReal.ofReal (ZLattice.covolume
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))))⁻¹
  have hc (j) : c j ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos _ volume)).ne'
  let μ := fun j => c j ^ Fintype.card (O j) • mixedArrayReference (I j) (Fin (n j)) (O j)
  let ν := fun j => (PMF.uniformOfFintype (O j → B j → ZMod d)).toMeasure
  let : ∀ j, SigmaFinite (μ j) := fun j =>
    ennreal_smul_sigmaFinite (mixedArrayReference (I j) (Fin (n j)) (O j)) _
      (ENNReal.pow_ne_top (hc j))
  let : ∀ j, SigmaFinite (normalizedCoveredReference (R := B j) (n := n j)
      (euclideanSubspace (U j)) d) := fun j => normalizedCoveredReference_sigmaFinite _ d
  have h (j) : MeasurePreserving
      (arrayResidueChart (O := O j) (Z := Fin (n j)) (R := B j → ZMod d) (o j))
      ((μ j).prod (ν j)) (Measure.pi (fun _ : O j =>
        normalizedCoveredReference (R := B j) (n := n j) (euclideanSubspace (U j)) d)) := by
    simpa only [μ, ν, normalizedCoveredReference, uniformPMF_toMeasure_pi] using
      arrayResidueChart_measurePreserving (O := O j) (Z := Fin (n j)) (o j)
        (PMF.uniformOfFintype (B j → ZMod d)).toMeasure (c j) (hc j)
  have h₁ := (dependentPiProd_measurePreserving μ ν).symm
    (dependentPiProd (Fin m)
      (fun j => (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
      (fun j => O j → B j → ZMod d))
  have h₂ := measurePreserving_pi (fun j => (μ j).prod (ν j))
    (fun j => Measure.pi (fun _ : O j =>
      normalizedCoveredReference (R := B j) (n := n j) (euclideanSubspace (U j)) d)) h
  change MeasurePreserving _ ((Measure.pi μ).prod
    (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure) (coveredJetReference U d)
  rw [uniformPMF_toMeasure_pi]
  exact h₂.comp h₁

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coveredJetArrayScale : ℝ :=
  ∏ j, (ZLattice.covolume
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))⁻¹ ^ Fintype.card (O j)

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem coveredJetArrayScale_pos : 0 < coveredJetArrayScale (O := O) U :=
  Finset.prod_pos (fun _ _ => pow_pos (inv_pos.mpr (ZLattice.covolume_pos _ volume)) _)

variable [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}

theorem coveredJetArrayReference_eq_real_smul (d : ℕ) [NeZero d] :
    coveredJetArrayReference (O := O) (I := I) (B := B) (n := n) U d =
      ENNReal.ofReal (coveredJetArrayScale (O := O) U) •
        ((Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod
          (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure) := by
  rw [coveredJetArrayReference_eq_smul]
  congr 1
  symm
  rw [coveredJetArrayScale, ENNReal.ofReal_prod_of_nonneg (fun j _ =>
    pow_nonneg (inv_nonneg.mpr (ZLattice.covolume_pos _ volume).le) _)]
  apply Finset.prod_congr rfl
  intro j _
  rw [ENNReal.ofReal_pow (inv_nonneg.mpr (ZLattice.covolume_pos _ volume).le),
    ENNReal.ofReal_inv_of_pos (ZLattice.covolume_pos _ volume)]

theorem coveredJetArrayReference_density (d : ℕ) [NeZero d]
    (f : ((∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) → ℝ) :
    realDensityMeasure (coveredJetArrayReference U d)
      (fun x => f x / coveredJetArrayScale (O := O) U) =
    realDensityMeasure
      ((Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod
        (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure) f := by
  rw [coveredJetArrayReference_eq_real_smul,
    realDensityMeasure_smul_real _ _ (coveredJetArrayScale_pos U).le]
  congr 1
  funext x
  field_simp [(coveredJetArrayScale_pos (O := O) U).ne']

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical ENNReal

theorem count_isOpenPosMeasure (X : Type*)
    [TopologicalSpace X] [MeasurableSpace X] [MeasurableSingletonClass X] :
    (Measure.count : Measure X).IsOpenPosMeasure := by
  constructor
  intro S _ hS
  obtain ⟨x, hx⟩ := hS
  apply ne_of_gt
  have h : (0 : ℝ≥0∞) < (Measure.count : Measure X) {x} := by simp
  exact h.trans_le (measure_mono (Set.singleton_subset_iff.mpr hx))

theorem uniformPMF_isOpenPosMeasure (X : Type*) [Fintype X] [Nonempty X]
    [TopologicalSpace X] [MeasurableSpace X] [MeasurableSingletonClass X] :
    (PMF.uniformOfFintype X).toMeasure.IsOpenPosMeasure := by
  constructor
  intro S _ hS
  obtain ⟨x, hx⟩ := hS
  apply ne_of_gt
  apply lt_of_lt_of_le _ (measure_mono (Set.singleton_subset_iff.mpr hx))
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x), PMF.uniformOfFintype_apply]
  exact ENNReal.inv_pos.mpr (by simp)

theorem normalizedCoveredReference_isOpenPosMeasure {D B : Type*}
    [Fintype D] [Fintype B] {n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)] (d : ℕ) [NeZero d] :
    (normalizedCoveredReference (R := B) (n := n) W d).IsOpenPosMeasure := by
  let : (PMF.uniformOfFintype (B → ZMod d)).toMeasure.IsOpenPosMeasure :=
    uniformPMF_isOpenPosMeasure _
  let : (Measure.count : Measure (Fin n → ℤ)).IsOpenPosMeasure := count_isOpenPosMeasure _
  let : ((volume : Measure W).prod (Measure.count : Measure (Fin n → ℤ))).IsOpenPosMeasure := inferInstance
  let : ((ENNReal.ofReal (ZLattice.covolume (latticeSection (standardEuclideanLattice D) W)))⁻¹ •
      ((volume : Measure W).prod (Measure.count : Measure (Fin n → ℤ)))).IsOpenPosMeasure :=
    Measure.isOpenPosMeasure_smul _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
  unfold normalizedCoveredReference
  infer_instance

namespace VectorPolynomial

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

omit [∀ j, Fintype (O j)] [∀ j, Fintype (B j)] in
theorem mixedCoveredJetEquiv_continuous (d : ℕ) :
    Continuous (mixedCoveredJetEquiv (O := O) (B := B) (n := n) U o d) := by
  change Continuous (fun p : ((∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) => fun (j : Fin m) (t : O j) =>
    ((orthonormalChart (o j) (fun i => (p.1 j).1 i t), fun i => (p.1 j).2 i t), p.2 j t))
  fun_prop

omit [∀ j, Fintype (O j)] [∀ j, Fintype (B j)] in
theorem mixedCoveredJetEquiv_symm_continuous (d : ℕ) :
    Continuous (mixedCoveredJetEquiv (O := O) (B := B) (n := n) U o d).symm := by
  change Continuous (fun x : CoveredJetChartSource U O B n d =>
    (fun (j : Fin m) => (fun i (t : O j) => (orthonormalChart (o j)).symm (x j t).1.1 i,
      fun i t => (x j t).1.2 i), fun j t => (x j t).2))
  fun_prop

omit [∀ j, Fintype (B j)] in
theorem coveredJetSourceRegion_isOpen
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ) (d : ℕ)
    (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j))) (hΩ : ∀ j t, IsOpen (Ω j t)) :
    IsOpen (coveredJetSourceRegion (B := B) U b d Ω) := by
  apply isOpen_set_pi Set.finite_univ
  intro j _
  apply isOpen_set_pi Set.finite_univ
  intro t _
  exact ((hΩ j t).preimage (normalizedLatticePoint_continuous _ (b j))).prod isOpen_univ

theorem coveredJetReference_isOpenPosMeasure
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (d : ℕ) [NeZero d] :
    (coveredJetReference (O := O) (B := B) (n := n) U d).IsOpenPosMeasure := by
  let : ∀ j, (normalizedCoveredReference (R := B j) (n := n j) (euclideanSubspace (U j)) d).IsOpenPosMeasure :=
    fun j => normalizedCoveredReference_isOpenPosMeasure _ d
  let : ∀ j, SigmaFinite (normalizedCoveredReference (R := B j) (n := n j) (euclideanSubspace (U j)) d) :=
    fun j => normalizedCoveredReference_sigmaFinite _ d
  unfold coveredJetReference
  infer_instance

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule Set
open scoped Classical BigOperators

variable {m : ℕ} {I O O' E J : Fin m → Type*} {n : Fin m → ℕ}
variable (e : ∀ j, O' j ≃ O j)

noncomputable def mixedCoveredRowsReindex (d : ℕ) :
    MixedCoveredJetSource I O E n d ≃ MixedCoveredJetSource I O' E n d where
  toFun z := (fun j => (fun i t => (z.1 j).1 i (e j t), fun i t => (z.1 j).2 i (e j t)),
    fun j t => z.2 j (e j t))
  invFun z := (fun j => (fun i t => (z.1 j).1 i ((e j).symm t), fun i t => (z.1 j).2 i ((e j).symm t)),
    fun j t => z.2 j ((e j).symm t))
  left_inv z := by simp only [Equiv.apply_symm_apply]
  right_inv z := by simp only [Equiv.symm_apply_apply]

variable [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def euclideanJetRowsReindex : EuclideanJetLayers U O ≃ᵐ EuclideanJetLayers U O' :=
  MeasurableEquiv.piCongrRight (fun j =>
    (MeasurableEquiv.piCongrLeft (fun _ : O j => euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) (e j)).symm)

variable [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)]

theorem euclideanJetRowsReindex_measurePreserving
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, SigmaFinite (ν j)] :
    MeasurePreserving (euclideanJetRowsReindex e U)
      (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))
      (Measure.pi (fun j => Measure.pi (fun _ : O' j => ν j))) :=
  measurePreserving_pi _ _ (fun j => (measurePreserving_piCongrLeft (fun _ : O j => ν j) (e j)).symm)

include e in
theorem coveredJetArrayScale_reindex_rows :
    coveredJetArrayScale (O := O') U = coveredJetArrayScale (O := O) U := by
  unfold coveredJetArrayScale
  exact Finset.prod_congr rfl (fun j _ => congrArg (fun k => _ ^ k) (Fintype.card_congr (e j)))

variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

omit [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)] in
theorem mixedCoveredJetChart_reindex_rows [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)]
    (z : MixedCoveredJetSource I O E n d) :
    mixedCoveredJetChart U o b hb bW d (mixedCoveredRowsReindex e d z) =
      euclideanJetRowsReindex e U (mixedCoveredJetChart U o b hb bW d z) := rfl

omit [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)] [∀ j, Fintype (E j)] [NeZero d] in
theorem mixedCoveredJetRegion_reindex_rows [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)]
    [∀ j, Fintype (E j)] [NeZero d] (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (z : MixedCoveredJetSource I O E n d) :
    mixedCoveredRowsReindex e d z ∈ mixedCoveredJetRegion U o b d (fun j => Ω j ∘ e j) ↔
      z ∈ mixedCoveredJetRegion U o b d Ω := by
  constructor
  · intro hz j hj t ht
    have h := hz j hj ((e j).symm t) (Set.mem_univ _)
    change mixedCoveredJetCoordinates U o d z j (e j ((e j).symm t)) ∈
      (normalizedLatticePoint (euclideanSubspace (U j)) (b j) ⁻¹' Ω j (e j ((e j).symm t))) ×ˢ univ at h
    simpa only [Equiv.apply_symm_apply] using h
  · intro hz j hj t ht
    exact hz j hj (e j t) (Set.mem_univ _)

end Erdos3.VectorPolynomial

end

end OAI
