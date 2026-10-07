import OAI.Combinatorics.Progressions.Geometry.CoefficientDeckChartRecovery

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

noncomputable def canonicalCoefficientJetValues (x : CoefficientSamplerArrays (K := K) I n) :
    EuclideanJetLayers U O := fun j r =>
  ∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) r e •
    mixedArrayQuotient (euclideanSubspace (U j)) (b j) (hb j) (o j) (x j) e

theorem canonicalCoefficientSample_jets (x : CoefficientSamplerArrays (K := K) I n) :
    euclideanCoefficientJetMap U root D rows (canonicalCoefficientSample U b hb o x) =
      canonicalCoefficientJetValues U b hb o root D rows x := by
  funext j r
  change _ = ∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) r e •
    mixedArrayQuotient (euclideanSubspace (U j)) (b j) (hb j) (o j) (x j) e
  simpa only [canonicalCoefficientSample, AddEquiv.apply_symm_apply] using
    euclideanCoefficientJetMap_apply U root D rows (canonicalCoefficientSample U b hb o x) j r

variable [∀ j, Fintype (O j)]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include ν in
theorem canonicalCoefficientJetValues_law
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (hw : ∀ j i e, 0 < w j i e)
    (hs : ∀ j e x, mixedCoefficientDensity (fun i => c j i e) (fun i => w j i e)
      (fun i => p j i e) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j)) :
    (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))).map
        (canonicalCoefficientJetValues U b hb o root D rows) =
      (realDensityMeasure μ (canonicalCoefficientDensity U b hb o c w p)).map
        (euclideanCoefficientJetMap U root D rows) := by
  have he : canonicalCoefficientJetValues U b hb o root D rows =
      euclideanCoefficientJetMap U root D rows ∘ canonicalCoefficientSample U b hb o :=
    funext (fun x => (canonicalCoefficientSample_jets U b hb o root D rows x).symm)
  rw [he, ← Measure.map_map (euclideanCoefficientJetMap_continuous U root D rows).measurable
    (canonicalCoefficientSample_measurable U b hb o),
    canonicalCoefficientDensity_law U b hb o c w p μ ν hw hs]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I : Fin m → Type*} [∀ j, Fintype (O j)]
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

noncomputable def canonicalCoefficientJetArrays
    (x : CoefficientSamplerArrays (K := K) I n) :
    ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ) := fun j =>
  mixedArrayIntegerImage (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) (x j)

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, Fintype (I j)] in
theorem canonicalCoefficientJetArrays_integer
    (x : CoefficientSamplerArrays (K := K) I n) (j : Fin m) (z : Fin (n j)) :
    (canonicalCoefficientJetArrays root D rows x j).2 z =
      boundedCoefficientJetMatrix root D (j.val + 1) (rows j) *ᵥ (x j).2 z := rfl

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, Fintype (I j)] in
theorem canonicalCoefficientJetArrays_real
    (x : CoefficientSamplerArrays (K := K) I n) (j : Fin m) (i : I j) :
    (canonicalCoefficientJetArrays root D rows x j).1 i =
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).map (Int.cast : ℤ → ℝ)
        *ᵥ (x j).1 i := rfl

omit [Fintype α] in
theorem canonicalCoefficientJetValues_eq_mixedImage
    (x : CoefficientSamplerArrays (K := K) I n) :
    canonicalCoefficientJetValues U b hb o root D rows x =
      fun j => mixedArrayQuotient (euclideanSubspace (U j)) (b j) (hb j) (o j)
        (canonicalCoefficientJetArrays root D rows x j) := by
  funext j r
  exact (mixedArrayIntegerImage_quotient _ (b j) (hb j) (o j)
    (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) (x j) r).symm

theorem canonicalCoefficientSample_mixed_jets
    (x : CoefficientSamplerArrays (K := K) I n) :
    euclideanCoefficientJetMap U root D rows (canonicalCoefficientSample U b hb o x) =
      fun j => mixedArrayQuotient (euclideanSubspace (U j)) (b j) (hb j) (o j)
        (canonicalCoefficientJetArrays root D rows x j) :=
  (canonicalCoefficientSample_jets U b hb o root D rows x).trans
    (canonicalCoefficientJetValues_eq_mixedImage U b hb o root D rows x)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include ν in
theorem canonicalCoefficientJetArrays_quotient_law
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (hw : ∀ j i e, 0 < w j i e)
    (hs : ∀ j e x, mixedCoefficientDensity (fun i => c j i e) (fun i => w j i e)
      (fun i => p j i e) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j)) :
    (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))).map
        (fun x j => mixedArrayQuotient (euclideanSubspace (U j)) (b j) (hb j) (o j)
          (canonicalCoefficientJetArrays root D rows x j)) =
      (realDensityMeasure μ (canonicalCoefficientDensity U b hb o c w p)).map
        (euclideanCoefficientJetMap U root D rows) := by
  have he := funext (canonicalCoefficientJetValues_eq_mixedImage U b hb o root D rows)
  rw [← he]
  exact canonicalCoefficientJetValues_law U b hb o root D rows μ ν c w p hw hs

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

noncomputable def normalizedLatticeRepresentativeHom : (W × (Fin n → ℤ)) →+ W where
  toFun := normalizedLatticeRepresentative W b hb
  map_zero' := by simp [normalizedLatticeRepresentative]
  map_add' x y := by
    simp only [normalizedLatticeRepresentative, Prod.fst_add, Prod.snd_add,
      map_add, Submodule.coe_add]
    abel

theorem normalizedLatticeRepresentative_sum_zsmul {S : Type*} (s : Finset S)
    (a : S → ℤ) (x : S → W × (Fin n → ℤ)) :
    normalizedLatticeRepresentative W b hb (∑ i ∈ s, a i • x i) =
      ∑ i ∈ s, a i • normalizedLatticeRepresentative W b hb (x i) := by
  change normalizedLatticeRepresentativeHom W b hb _ = _
  simp only [map_sum, map_zsmul, normalizedLatticeRepresentativeHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk]

theorem normalizedCoverLift_sum_zsmul (d : ℕ) {S : Type*} (s : Finset S)
    (a : S → ℤ) (x : S → W × (Fin n → ℤ)) :
    normalizedCoverLift W b hb d (∑ i ∈ s, a i • x i) =
      ∑ i ∈ s, a i • normalizedCoverLift W b hb d (x i) := by
  have he (i) : (d : ℝ)⁻¹ • (a i • normalizedLatticeRepresentative W b hb (x i)) =
      a i • ((d : ℝ)⁻¹ • normalizedLatticeRepresentative W b hb (x i)) := smul_comm _ _ _
  simp only [normalizedCoverLift, normalizedLatticeRepresentative_sum_zsmul,
    Finset.smul_sum, he]
  change QuotientAddGroup.mk' _ (∑ i ∈ s, a i • ((d : ℝ)⁻¹ •
    normalizedLatticeRepresentative W b hb (x i))) = _
  simp only [map_sum, map_zsmul]
  rfl

namespace VectorPolynomial

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable {ns : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bs : ∀ j, Basis (Fin (ns j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hbs : ∀ j, span ℤ (Set.range (bs j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

theorem canonicalCoefficientCoverLift_jets (d : ℕ)
    (x : CoefficientSamplerArrays (K := K) I ns) (j : Fin m) (t : O j) :
    euclideanCoefficientJetMap U root A rows (canonicalCoefficientCoverLift U bs hbs o d x) j t =
      normalizedCoverLift (euclideanSubspace (U j)) (bs j) (hbs j) d
        (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _
          (canonicalCoefficientJetArrays root A rows x j) t)) := by
  rw [euclideanCoefficientJetMap_apply]
  simp only [canonicalCoefficientCoverLift, AddEquiv.apply_symm_apply]
  rw [canonicalCoefficientJetArrays, mixedArrayIntegerImage_regroup,
    orthonormalMixedChart_sum_zsmul, normalizedCoverLift_sum_zsmul]

theorem canonicalCoefficientDeckSample_mixed_jets
    {B : Fin m → Type*} [∀ j, Fintype (B j)]
    (bW : ∀ j, Basis (B j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) (hd : 0 < d) (x : CoefficientSamplerArrays (K := K) I ns)
    (r : CoefficientDeckResidues (K := K) B d) (j : Fin m) (t : O j) :
    euclideanCoefficientJetMap U root A rows
        (canonicalCoefficientDeckSample U bW bs hbs o d hd x r) j t =
      normalizedCoverLift (euclideanSubspace (U j)) (bs j) (hbs j) d
        (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _
          (canonicalCoefficientJetArrays root A rows x j) t)) +
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (coefficientDeckJetMap root A rows d r j t)).val := by
  rw [canonicalCoefficientDeckSample_jets, canonicalCoefficientCoverLift_jets]

end VectorPolynomial

end Erdos3

end

end OAI
