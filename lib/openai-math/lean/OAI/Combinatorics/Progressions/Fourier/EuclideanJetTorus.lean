/- Modified for ProveIt: Use older set-comprehension and discrete-subgroup names; statements unchanged. -/
import OAI.Combinatorics.Progressions.Fourier.CommonCoveredSiteCharacter
import OAI.Combinatorics.Progressions.Linear.BooleanJetMatrixFactor

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

def coefficientIntegerLattice {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) : AddSubgroup (CoefficientArray (K := K) U) where
  carrier := {x | ∀ s a, ∃ n : ℤ, (x s).val a = n}
  zero_mem' s a := ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy s a
    obtain ⟨n, hn⟩ := hx s a
    obtain ⟨m, hm⟩ := hy s a
    refine ⟨n + m, ?_⟩
    change (x s).val a + (y s).val a = ((n + m : ℤ) : ℝ)
    rw [hn, hm, Int.cast_add]
  neg_mem' := by
    intro x hx s a
    obtain ⟨n, hn⟩ := hx s a
    refine ⟨-n, ?_⟩
    change -(x s).val a = ((-n : ℤ) : ℝ)
    rw [hn, Int.cast_neg]

abbrev CoefficientTorus {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :=
  CoefficientArray (K := K) U ⧸ coefficientIntegerLattice U

theorem coefficientArrayFunctional_integral {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    ∃ n : ℤ, coefficientArrayFunctional U frequency x = n := by
  change ∀ s a, ∃ n : ℤ, (x s).val a = n at hx
  choose z hz using hx
  refine ⟨∑ s : CoefficientSlot K m, ∑ a, frequency s.1 s.2.val a * z s a, ?_⟩
  change (∑ s : CoefficientSlot K m, ∑ a, (frequency s.1 s.2.val a : ℝ) * (x s).val a) = _
  simp only [hz, Int.cast_sum, Int.cast_mul]

noncomputable def coefficientTorusCharacter {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    CoefficientTorus (K := K) U → ℂ :=
  quotientLinearCharacter (coefficientIntegerLattice U) (coefficientArrayFunctional U frequency)
    (coefficientArrayFunctional_integral U frequency)

theorem coefficientTorusCharacter_mk {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (x : CoefficientArray (K := K) U) :
    coefficientTorusCharacter U frequency (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) =
      CircleFourier.character (coefficientArrayFunctional U frequency x : CircleFourier.Circle) := rfl

theorem coefficientTorusCharacter_integrable {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ] :
    Integrable (coefficientTorusCharacter U frequency) μ :=
  quotientLinearCharacter_integrable _ _ _
    (coefficientArrayFunctional U frequency).continuous_of_finiteDimensional μ

theorem coefficientTorusCharacter_integral {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [MeasurableAdd₂ (CoefficientTorus (K := K) U)]
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] :
    (∫ x, coefficientTorusCharacter U frequency x ∂μ) =
      if affineCoefficientModeTrivial U frequency then 1 else 0 := by
  rw [coefficientTorusCharacter, quotientLinearCharacter_integral,
    coefficientArrayFunctional_eq_zero_iff_trivial]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

abbrev CoefficientCoordinateTori {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :=
  ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1)

def coefficientCoordinateArray {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (s : CoefficientSlot K m) :
    CoefficientArray (K := K) U →ₗ[ℝ] (Unit → U s.1) where
  toFun x _ := x s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coefficientCoordinateTorus {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    CoefficientTorus (K := K) U →+ CoefficientCoordinateTori (K := K) U :=
  AddMonoidHom.pi (fun s => QuotientAddGroup.map (coefficientIntegerLattice U)
    (subspaceArrayIntegerLattice Unit (U s.1)) (coefficientCoordinateArray U s).toAddMonoidHom
    (fun _x hx _ a => hx s a))

theorem coefficientCoordinateTorus_mk {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (x : CoefficientArray (K := K) U)
    (s : CoefficientSlot K m) :
    coefficientCoordinateTorus U (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) s =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U s.1)) (fun _ => x s) := rfl

theorem coefficientCoordinateTorus_surjective {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    Function.Surjective (coefficientCoordinateTorus (K := K) U) := by
  intro y
  choose v hv using fun s => QuotientAddGroup.mk'_surjective
    (subspaceArrayIntegerLattice Unit (U s.1)) (y s)
  refine ⟨QuotientAddGroup.mk' (coefficientIntegerLattice U) (fun s => v s ()), ?_⟩
  funext s
  rw [coefficientCoordinateTorus_mk]
  have he : (fun _ : Unit => v s ()) = v s := funext (fun u => by cases u; rfl)
  rw [he, hv s]

theorem coefficientCoordinateTorus_continuous {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    Continuous (coefficientCoordinateTorus (K := K) U) := by
  apply continuous_pi
  intro s
  apply (QuotientAddGroup.isQuotientMap_mk (coefficientIntegerLattice U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (coefficientCoordinateArray U s).continuous_of_finiteDimensional

theorem coefficientCoordinateTori_compact {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)] :
    CompactSpace (CoefficientCoordinateTori (K := K) U) := by
  have h := isCompact_univ.image (coefficientCoordinateTorus_continuous (K := K) U)
  rw [Set.image_univ, Set.range_eq_univ.mpr (coefficientCoordinateTorus_surjective U)] at h
  exact ⟨h⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def coefficientLayerArray {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m) :
    CoefficientArray (K := K) U →ₗ[ℝ] (BoundedCoefficientExponent K (j.val + 1) → U j) where
  toFun x d := x ⟨j, d⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coefficientLayerArray_preserves_lattice {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    coefficientLayerArray U j x ∈ subspaceArrayIntegerLattice
      (BoundedCoefficientExponent K (j.val + 1)) (U j) := fun d a => hx ⟨j, d⟩ a

def coefficientLayerTorus {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m) :
    CoefficientTorus (K := K) U →+
      SubspaceArrayTorus (BoundedCoefficientExponent K (j.val + 1)) (U j) :=
  QuotientAddGroup.map (coefficientIntegerLattice U)
    (subspaceArrayIntegerLattice (BoundedCoefficientExponent K (j.val + 1)) (U j))
    (coefficientLayerArray U j).toAddMonoidHom (coefficientLayerArray_preserves_lattice U j)

theorem coefficientLayerTorus_mk {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m) (x : CoefficientArray (K := K) U) :
    coefficientLayerTorus U j (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice
        (BoundedCoefficientExponent K (j.val + 1)) (U j)) (coefficientLayerArray U j x) := rfl

theorem coefficientLayerTorus_continuous {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m) :
    Continuous (coefficientLayerTorus (K := K) U j) := by
  apply (QuotientAddGroup.isQuotientMap_mk (coefficientIntegerLattice U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (coefficientLayerArray U j).continuous_of_finiteDimensional

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module

instance coefficientIntegerLattice_closed {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    IsClosed (coefficientIntegerLattice (K := K) U : Set (CoefficientArray (K := K) U)) := by
  change IsClosed {x : CoefficientArray (K := K) U | ∀ s a, ∃ n : ℤ, (x s).val a = n}
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro a
  have h₁ : Continuous (fun x : CoefficientArray (K := K) U => x s) := continuous_apply s
  have h₂ : Continuous (fun x : CoefficientArray (K := K) U => (x s).val) :=
    continuous_subtype_val.comp h₁
  have h₃ : Continuous (fun x : CoefficientArray (K := K) U => (x s).val a) :=
    (continuous_apply a).comp h₂
  have h : IsClosed {x : CoefficientArray (K := K) U | ∃ n : ℤ, (n : ℝ) = (x s).val a} :=
    Real.isClosedEmbedding_intCast.isClosed_range.preimage h₃
  simpa only [eq_comm] using h

theorem coefficientTorus_compact_of_basis {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {B : Fin m → Type*} [∀ j, Fintype (B j)]
    (b : ∀ j, Basis (B j) ℝ (U j))
    (hb : ∀ j i a, ∃ n : ℤ, (b j i).val a = n) :
    CompactSpace (CoefficientTorus (K := K) U) := by
  classical
  apply compact_quotient_of_integral_basis (coefficientIntegerLattice U)
    (Pi.basis (fun s : CoefficientSlot K m => b s.1))
  rintro ⟨s, i⟩ t a
  simp only [Pi.basis_apply]
  by_cases hts : t = s
  · subst t
    simpa only [Pi.single_eq_same] using hb s.1 i a
  · exact ⟨0, by simp [Pi.single_eq_of_ne hts]⟩

noncomputable def coefficientTorusHaar {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    {B : Fin m → Type*} [∀ j, Fintype (B j)]
    (b : ∀ j, Basis (B j) ℝ (U j))
    (hb : ∀ j i a, ∃ n : ℤ, (b j i).val a = n) : Measure (CoefficientTorus (K := K) U) := by
  letI := coefficientTorus_compact_of_basis (K := K) U b hb
  exact probabilityAddHaar _

instance coefficientTorusHaar_probability {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    {B : Fin m → Type*} [∀ j, Fintype (B j)]
    (b : ∀ j, Basis (B j) ℝ (U j))
    (hb : ∀ j i a, ∃ n : ℤ, (b j i).val a = n) :
    IsProbabilityMeasure (coefficientTorusHaar (K := K) U b hb) := by
  let _ := coefficientTorus_compact_of_basis (K := K) U b hb
  exact probabilityAddHaar_probability _

instance coefficientTorusHaar_invariant {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    {B : Fin m → Type*} [∀ j, Fintype (B j)]
    (b : ∀ j, Basis (B j) ℝ (U j))
    (hb : ∀ j i a, ∃ n : ℤ, (b j i).val a = n) :
    (coefficientTorusHaar (K := K) U b hb).IsAddLeftInvariant := by
  let _ := coefficientTorus_compact_of_basis (K := K) U b hb
  exact probabilityAddHaar_invariant _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def affineSampleCoefficientArray {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (b : Option K → I → ℝ) : CoefficientArray (K := K) U :=
  fun s => coefficients (substitute (affineParameterSubstitution b)
    (restrictCoefficients (U s.1) (p s.1) (hm s.1))) s.2.val

theorem affineSampleCoefficientArray_val {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (b : Option K → I → ℝ) (s : CoefficientSlot K m) :
    (affineSampleCoefficientArray U p hm b s).val =
      coefficients (substitute (affineParameterSubstitution b) (p s.1)) s.2.val := by
  change (U s.1).subtype (coefficients _ s.2.val) = _
  rw [← coefficients_map, map_substitute, map_restrictCoefficients]

theorem coefficientArrayFunctional_sample {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (b : Option K → I → ℝ) :
    coefficientArrayFunctional U frequency (affineSampleCoefficientArray U p hm b) =
      ∑ j, affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ)))
        (substitute (fun u => rowPolynomial (fun k => b k u)) (p j)) := by
  change (∑ s : CoefficientSlot K m, ∑ a,
    (frequency s.1 s.2.val a : ℝ) * (affineSampleCoefficientArray U p hm b s).val a) = _
  simp only [affineSampleCoefficientArray_val, CoefficientSlot, Fintype.sum_sigma,
    affineModeLift_substitute]
  apply Finset.sum_congr rfl
  intro j _
  exact (coefficientFunctional_bounded_expansion (fun d a => (frequency j d a : ℝ)) (h := j.val + 1) _
    (degreeLE_substitute_affine _ (affineParameterSubstitution_degree b) (p j) (hp j))).symm

noncomputable def affineSampleCoefficientTorus {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (b : Option K → I → ℝ) : CoefficientTorus (K := K) U :=
  QuotientAddGroup.mk' (coefficientIntegerLattice U) (affineSampleCoefficientArray U p hm b)

theorem coefficientTorusCharacter_sample {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (b : Option K → I → ℝ) :
    coefficientTorusCharacter U frequency (affineSampleCoefficientTorus U p hm b) =
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ)))) p b := by
  rw [affineSampleCoefficientTorus, coefficientTorusCharacter_mk, coefficientArrayFunctional_sample U frequency p hp hm]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem integerMatrixTorusMap_continuous {I S J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) :
    Continuous (integerMatrixTorusMap U E) := by
  apply (QuotientAddGroup.isQuotientMap_mk (subspaceArrayIntegerLattice I U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp
    (matrixModuleAction (W := U) (fun s i => (E s i : ℝ))).continuous_of_finiteDimensional

namespace VectorPolynomial

abbrev SiteTorus (S : Type*) {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) := ∀ j, SubspaceArrayTorus S (U j)

noncomputable def coefficientSiteTorusMap {K S : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ) :
    CoefficientTorus (K := K) U →+ SiteTorus S U :=
  AddMonoidHom.pi (fun j => (integerMatrixTorusMap (U j) (boundedSiteMatrix (j.val + 1) site)).comp
    (coefficientLayerTorus U j))

theorem coefficientSiteTorusMap_mk {K S : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ)
    (x : CoefficientArray (K := K) U) (j : Fin m) :
    coefficientSiteTorusMap U site (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) j =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice S (U j))
        (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ))
          (coefficientLayerArray U j x)) := rfl

theorem coefficientSiteTorusMap_continuous {K S : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ) :
    Continuous (coefficientSiteTorusMap U site) :=
  continuous_pi (fun j => (integerMatrixTorusMap_continuous _ _).comp
    (coefficientLayerTorus_continuous U j))

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

def zeroCoefficientExponent (K : Type*) (h : ℕ) : BoundedCoefficientExponent K h :=
  ⟨0, by simp⟩

noncomputable def constantCoefficientTorus {K J : Type*} (U : Submodule ℝ (J → ℝ)) (h : ℕ) :
    SubspaceArrayTorus Unit U →+ SubspaceArrayTorus (BoundedCoefficientExponent K h) U :=
  integerMatrixTorusMap U (Matrix.of (fun d _ => if d = zeroCoefficientExponent K h then 1 else 0))

theorem constantCoefficientTorus_mk {K J : Type*} (U : Submodule ℝ (J → ℝ)) (h : ℕ)
    (x : Unit → U) :
    constantCoefficientTorus (K := K) U h (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit U) x) =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice (BoundedCoefficientExponent K h) U)
        (fun d => if d = zeroCoefficientExponent K h then x () else 0) := by
  rw [constantCoefficientTorus, integerMatrixTorusMap_mk]
  congr 1
  funext d
  change (∑ _u : Unit, ((if d = zeroCoefficientExponent K h then 1 else 0 : ℤ) : ℝ) • x _u) = _
  by_cases hd : d = zeroCoefficientExponent K h <;> simp [hd]

theorem constantCoefficientTorus_continuous {K J : Type*} [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (h : ℕ) :
    Continuous (constantCoefficientTorus (K := K) U h) := integerMatrixTorusMap_continuous _ _

theorem oneSite_constantCoefficientTorus {K J : Type*} [Fintype K]
    (U : Submodule ℝ (J → ℝ)) (h : ℕ) (t : K → ℤ) (c : SubspaceArrayTorus Unit U) :
    integerMatrixTorusMap U (boundedSiteMatrix h (fun _ : Unit => t))
      (constantCoefficientTorus U h c) = c := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice Unit U) c
  rw [constantCoefficientTorus_mk, integerMatrixTorusMap_mk]
  congr 1
  funext u
  change (∑ d : BoundedCoefficientExponent K h, (boundedSiteMatrix h (fun _ : Unit => t) u d : ℝ) •
    (if d = zeroCoefficientExponent K h then x () else 0)) = x u
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp [boundedSiteMatrix, zeroCoefficientExponent]

theorem oneSite_add_constantCoefficientTorus {K J : Type*} [Fintype K]
    (U : Submodule ℝ (J → ℝ)) (h : ℕ) (t : K → ℤ) (c : SubspaceArrayTorus Unit U)
    (r : SubspaceArrayTorus (BoundedCoefficientExponent K h) U) :
    integerMatrixTorusMap U (boundedSiteMatrix h (fun _ : Unit => t))
      (constantCoefficientTorus U h c + r) =
      c + integerMatrixTorusMap U (boundedSiteMatrix h (fun _ : Unit => t)) r := by
  rw [map_add, oneSite_constantCoefficientTorus]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem matrixModuleAction_surjective_of_period {I S W : Type*}
    [Fintype I] [Fintype S] [AddCommGroup W] [Module ℝ W]
    (E : Matrix S I ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice S a ≤ E.mulVecLin.range) :
    Function.Surjective (matrixModuleAction (W := W) (fun s i => (E s i : ℝ))) := by
  classical
  obtain ⟨n, hn⟩ := exists_integer_kernel_dual E a hperiod
  let e : S → I → ℤ := E
  let A : Matrix S I ℝ := Matrix.of (fun s i => (e s i : ℝ))
  let T : Matrix I S ℝ := fun i s => (n s i : ℝ) / a
  have hET : A * T = 1 := by
    ext s r
    have hsum : (∑ i, (n r i : ℝ) * (e s i : ℝ)) = if r = s then (a : ℝ) else 0 := by
      exact_mod_cast hn r s
    change (∑ i, (e s i : ℝ) * ((n r i : ℝ) / a)) = _
    have hswap : (∑ i, (e s i : ℝ) * ((n r i : ℝ) / a)) =
        (∑ i, (n r i : ℝ) * (e s i : ℝ)) / a := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hswap, hsum]
    by_cases hrs : r = s
    · subst r
      simp [ha]
    · simp [hrs, Ne.symm hrs]
  intro y
  refine ⟨matrixModuleAction T y, ?_⟩
  change matrixModuleAction A (matrixModuleAction T y) = y
  calc
    _ = matrixModuleAction (A * T) y := matrixModuleAction_mul A T y
    _ = matrixModuleAction (1 : Matrix S S ℝ) y := congrArg (fun M => matrixModuleAction M y) hET
    _ = y := by ext s; simp [matrixModuleAction_apply, Matrix.one_apply]

theorem integerMatrixTorusMap_surjective_of_period {I S J : Type*}
    [Fintype I] [Fintype S] (U : Submodule ℝ (J → ℝ))
    (E : Matrix S I ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice S a ≤ E.mulVecLin.range) :
    Function.Surjective (integerMatrixTorusMap U E) := by
  intro y
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice S U) y
  obtain ⟨x, hx⟩ := matrixModuleAction_surjective_of_period (W := U) E a ha hperiod v
  refine ⟨QuotientAddGroup.mk' (subspaceArrayIntegerLattice I U) x, ?_⟩
  rw [integerMatrixTorusMap_mk, hx]

theorem integerMatrixTorusMap_comp {I S T J : Type*}
    [Fintype I] [Fintype S] (U : Submodule ℝ (J → ℝ))
    (A : Matrix T S ℤ) (B : Matrix S I ℤ) (x : SubspaceArrayTorus I U) :
    integerMatrixTorusMap U A (integerMatrixTorusMap U B x) =
      integerMatrixTorusMap U (A * B) x := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice I U) x
  have hcast : Matrix.of (fun t s => (A t s : ℝ)) *
      Matrix.of (fun s i => (B s i : ℝ)) =
      Matrix.of (fun t i => ((A * B) t i : ℝ)) := by
    ext t i
    simp [Matrix.mul_apply]
  exact congrArg (QuotientAddGroup.mk' (subspaceArrayIntegerLattice T U))
    ((matrixModuleAction_mul (Matrix.of (fun t s => (A t s : ℝ)))
      (Matrix.of (fun s i => (B s i : ℝ))) v).trans
      (congrArg (fun M => matrixModuleAction M v) hcast))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

abbrev BooleanJetTorus {m : ℕ} (O : Fin m → Type*) {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) := ∀ j, SubspaceArrayTorus (O j) (U j)

noncomputable def siteBooleanJetTorusMap {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} {O J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (rows : ∀ j, O j → Finset α) : SiteTorus (Finset α) U →+ BooleanJetTorus O U where
  toFun x j := integerMatrixTorusMap (U j) (booleanJetExtractionMatrix (rows j)) (x j)
  map_zero' := funext (fun j => map_zero (integerMatrixTorusMap (U j) _))
  map_add' x y := funext (fun j => map_add (integerMatrixTorusMap (U j) _) (x j) (y j))

theorem siteBooleanJetTorusMap_continuous {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} {O J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (rows : ∀ j, O j → Finset α) :
    Continuous (siteBooleanJetTorusMap U rows) :=
  continuous_pi (fun j => (integerMatrixTorusMap_continuous _ _).comp (continuous_apply j))

noncomputable def coefficientBooleanJetTorusMap {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (rows : ∀ j, O j → Finset α) : CoefficientTorus (K := K) U →+ BooleanJetTorus O U :=
  (siteBooleanJetTorusMap U rows).comp (coefficientSiteTorusMap U (integerAffineCube root D))

theorem coefficientBooleanJetTorusMap_mk {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (rows : ∀ j, O j → Finset α) (x : CoefficientArray (K := K) U) (j : Fin m) :
    coefficientBooleanJetTorusMap U root D rows
        (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) j =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice (O j) (U j))
        (matrixModuleAction
          (fun o e => (boundedCoefficientJetMatrix root D (j.val + 1) (rows j) o e : ℝ))
          (coefficientLayerArray U j x)) := by
  change integerMatrixTorusMap (U j) (booleanJetExtractionMatrix (rows j))
    (integerMatrixTorusMap (U j) (boundedSiteMatrix (j.val + 1) (integerAffineCube root D))
      (QuotientAddGroup.mk' _ (coefficientLayerArray U j x))) = _
  rw [integerMatrixTorusMap_comp, booleanJetExtractionMatrix_mul_boundedSite]
  rfl

theorem coefficientBooleanJetTorusMap_continuous {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α) :
    Continuous (coefficientBooleanJetTorusMap U root D rows) :=
  (siteBooleanJetTorusMap_continuous U rows).comp
    (coefficientSiteTorusMap_continuous U (integerAffineCube root D))

theorem coefficientBooleanJetTorusMap_surjective {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (O j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (rows : ∀ j, O j → Finset α) (hinj : ∀ j, Function.Injective (rows j))
    (hdegree : ∀ j o, (rows j o).card ≤ j.val + 1) :
    Function.Surjective (coefficientBooleanJetTorusMap U root D rows) := by
  intro y
  choose v hv using fun j => QuotientAddGroup.mk'_surjective
    (subspaceArrayIntegerLattice (O j) (U j)) (y j)
  choose c hc using fun j => matrixModuleAction_surjective_of_period (W := U j)
    (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) (a ^ (j.val + 1))
    (pow_ne_zero _ ha)
    (boundedCoefficientJetMatrix_period root D a hperiod (j.val + 1) (rows j)
      (hinj j) (hdegree j)) (v j)
  refine ⟨QuotientAddGroup.mk' (coefficientIntegerLattice U) (fun s => c s.1 s.2), ?_⟩
  funext j
  rw [coefficientBooleanJetTorusMap_mk]
  change QuotientAddGroup.mk' _ (matrixModuleAction _ (c j)) = y j
  rw [hc j, hv j]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {O J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

abbrev EuclideanJetLayers (O : Fin m → Type*) :=
  ∀ j : Fin m, O j → euclideanSubspace (U j) ⧸
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup

instance euclideanJetLayers_borel [∀ j, Fintype (O j)] : BorelSpace (EuclideanJetLayers U O) := by
  let : ∀ j, BorelSpace (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun _ => QuotientAddGroup.borelSpace
  let : ∀ j, BorelSpace (O j → euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun _ => Pi.borelSpace
  exact Pi.borelSpace

noncomputable def euclideanJetEquiv : BooleanJetTorus O U ≃+ EuclideanJetLayers U O where
  toFun x j o := (euclideanSubspaceTorusEquiv (U j)).symm (arrayCoordinateEquiv (U j) (x j) o)
  invFun y j := (arrayCoordinateEquiv (U j)).symm (fun o => euclideanSubspaceTorusEquiv (U j) (y j o))
  left_inv x := by
    funext j
    apply (arrayCoordinateEquiv (U j)).injective
    rw [AddEquiv.apply_symm_apply]
    funext o
    exact (euclideanSubspaceTorusEquiv (U j)).apply_symm_apply _
  right_inv y := by
    funext j o
    dsimp only
    rw [AddEquiv.apply_symm_apply]
    exact (euclideanSubspaceTorusEquiv (U j)).symm_apply_apply _
  map_add' x y := by
    funext j o
    simp only [map_add, Pi.add_apply]

theorem euclideanJetEquiv_continuous [∀ j, Fintype (O j)] :
    Continuous (euclideanJetEquiv (O := O) U) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro o
  exact (euclideanSubspaceTorusEquiv_symm_continuous (U j)).comp
    ((continuous_apply o).comp ((arrayCoordinateEquiv_continuous (U j)).comp (continuous_apply j)))

end Erdos3.VectorPolynomial

end

end OAI
