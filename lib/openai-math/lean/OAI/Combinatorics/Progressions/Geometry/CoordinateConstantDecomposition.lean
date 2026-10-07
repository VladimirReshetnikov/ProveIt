/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Remove redundant reflexivity after simplification closes the constant-coordinate case.
Mathematical statements are unchanged. -/
import OAI.Compat.Core
import Mathlib.MeasureTheory.Constructions.Pi
import OAI.Combinatorics.Progressions.Fourier.EuclideanJetTorus

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def coordinateSiteValue {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x : CoefficientCoordinateTori (K := K) U) : SiteTorus Unit U :=
  fun j => ∑ d : BoundedCoefficientExponent K (j.val + 1),
    boundedSiteMatrix (j.val + 1) (fun _ : Unit => t) () d • x ⟨j, d⟩

theorem coordinateSiteValue_continuous {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) :
    Continuous (coordinateSiteValue U t) := by
  apply continuous_pi
  intro j
  apply continuous_finsetSum
  intro d _
  exact (show Continuous (fun x : CoefficientCoordinateTori (K := K) U => x ⟨j, d⟩) from
    continuous_apply _).zsmul _

theorem coordinateSiteValue_add {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x y : CoefficientCoordinateTori (K := K) U) :
    coordinateSiteValue U t (x + y) = coordinateSiteValue U t x + coordinateSiteValue U t y := by
  funext j
  let X : BoundedCoefficientExponent K (j.val + 1) → SubspaceArrayTorus Unit (U j) := fun d => x ⟨j, d⟩
  let Y : BoundedCoefficientExponent K (j.val + 1) → SubspaceArrayTorus Unit (U j) := fun d => y ⟨j, d⟩
  let w : BoundedCoefficientExponent K (j.val + 1) → ℤ :=
    fun d => boundedSiteMatrix (j.val + 1) (fun _ : Unit => t) () d
  change (∑ d, w d • (X d + Y d)) = (∑ d, w d • X d) + ∑ d, w d • Y d
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  exact zsmul_add (X d) (Y d) _

theorem coordinateSiteValue_coefficientCoordinates {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x : CoefficientTorus (K := K) U) :
    coordinateSiteValue U t (coefficientCoordinateTorus U x) =
      coefficientSiteTorusMap U (fun _ : Unit => t) x := by
  classical
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  funext j
  let π : (Unit → U j) →+ SubspaceArrayTorus Unit (U j) :=
    QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U j))
  let w : BoundedCoefficientExponent K (j.val + 1) → ℤ :=
    fun d => boundedSiteMatrix (j.val + 1) (fun _ : Unit => t) () d
  let v : BoundedCoefficientExponent K (j.val + 1) → U j := fun d => y ⟨j, d⟩
  have hsum (s : Finset (BoundedCoefficientExponent K (j.val + 1))) :
      (∑ d ∈ s, π (w d • (fun _ : Unit => v d))) = π (∑ d ∈ s, w d • (fun _ : Unit => v d)) := by
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (congrArg (fun z => π (w a • (fun _ : Unit => v a)) + z) ih).trans
        (π.map_add' _ _).symm
  change (∑ d, w d • π (fun _ => v d)) = π (fun _ => ∑ d, (w d : ℝ) • v d)
  calc
    _ = ∑ d, π (w d • (fun _ : Unit => v d)) := by
      apply Finset.sum_congr rfl
      intro d _
      exact (map_zsmul π _ _).symm
    _ = π (∑ d, w d • (fun _ : Unit => v d)) := hsum Finset.univ
    _ = _ := by
      apply congrArg π
      funext u
      simp only [Finset.sum_apply, Pi.smul_apply]
      apply Finset.sum_congr rfl
      intro d _
      exact (Int.cast_smul_eq_zsmul ℝ (w d) (v d)).symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

abbrev ConstantCoefficientSlot (K : Type*) (m : ℕ) :=
  {s : CoefficientSlot K m // s.2.val = 0}

abbrev NonconstantCoefficientSlot (K : Type*) (m : ℕ) :=
  {s : CoefficientSlot K m // s.2.val ≠ 0}

noncomputable instance constantCoefficientSlotFintype (K : Type*) [Fintype K] (m : ℕ) :
    Fintype (ConstantCoefficientSlot K m) := Fintype.ofFinite _

noncomputable instance nonconstantCoefficientSlotFintype (K : Type*) [Fintype K] (m : ℕ) :
    Fintype (NonconstantCoefficientSlot K m) := Fintype.ofFinite _

def constantCoefficientSlotEquiv (K : Type*) (m : ℕ) : Fin m ≃ ConstantCoefficientSlot K m where
  toFun j := ⟨⟨j, zeroCoefficientExponent K (j.val + 1)⟩, rfl⟩
  invFun s := s.val.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨j, ⟨d, hd⟩⟩, he⟩
    cases he
    rfl

abbrev NonconstantCoordinateTori {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :=
  ∀ s : NonconstantCoefficientSlot K m, SubspaceArrayTorus Unit (U s.val.1)

def coefficientConstantCoordinates {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (x : CoefficientCoordinateTori (K := K) U) : SiteTorus Unit U :=
  fun j => x (constantCoefficientSlotEquiv K m j).val

def coefficientCoordinateSplit {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (x : CoefficientCoordinateTori (K := K) U) :
    NonconstantCoordinateTori (K := K) U × SiteTorus Unit U :=
  (fun s => x s.val, coefficientConstantCoordinates U x)

theorem coefficientCoordinateSplit_measurePreserving {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    [∀ j, MeasurableSpace (SubspaceArrayTorus Unit (U j))]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, SigmaFinite (ν s)] :
    MeasurePreserving (coefficientCoordinateSplit U) (Measure.pi ν)
      ((Measure.pi (fun s : NonconstantCoefficientSlot K m => ν s.val)).prod
        (Measure.pi (fun j => ν (constantCoefficientSlotEquiv K m j).val))) := by
  classical
  have hs := measurePreserving_piEquivPiSubtypeProd ν (fun s => s.2.val = 0)
  have eC : Subtype.fintype (fun s : CoefficientSlot K m => s.2.val = 0) =
      constantCoefficientSlotFintype K m := Subsingleton.elim _ _
  have eN : Subtype.fintype (fun s : CoefficientSlot K m => ¬s.2.val = 0) =
      nonconstantCoefficientSlotFintype K m := Subsingleton.elim _ _
  rw [eC, eN] at hs
  have hc := (measurePreserving_piCongrLeft
    (fun s : ConstantCoefficientSlot K m => ν s.val) (constantCoefficientSlotEquiv K m)).symm
  have hp := ((MeasurePreserving.id _).prod hc).comp (Measure.measurePreserving_swap.comp hs)
  exact hp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def constantCoordinateExtension {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (c : SiteTorus Unit U) : CoefficientCoordinateTori (K := K) U :=
  fun s => if s.2.val = 0 then c s.1 else 0

noncomputable def nonconstantCoordinateExtension {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (r : NonconstantCoordinateTori (K := K) U) :
    CoefficientCoordinateTori (K := K) U := fun s => if h : s.2.val = 0 then 0 else r ⟨s, h⟩

theorem nonconstantCoordinateExtension_continuous {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) : Continuous (nonconstantCoordinateExtension (K := K) U) := by
  apply continuous_pi
  intro s
  by_cases hs : s.2.val = 0
  · simpa only [nonconstantCoordinateExtension, dite_eq_left hs] using
      (continuous_const : Continuous (fun _ : NonconstantCoordinateTori (K := K) U => (0 : SubspaceArrayTorus Unit (U s.1))))
  · simpa only [nonconstantCoordinateExtension, dite_eq_right hs] using
      (continuous_apply (⟨s, hs⟩ : NonconstantCoefficientSlot K m))

theorem coordinate_constant_decomposition {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (x : CoefficientCoordinateTori (K := K) U) :
    x = constantCoordinateExtension U (coefficientCoordinateSplit U x).2 +
      nonconstantCoordinateExtension U (coefficientCoordinateSplit U x).1 := by
  funext s
  rcases s with ⟨j, ⟨d, hd⟩⟩
  by_cases hz : d = 0
  · subst d
    simp [constantCoordinateExtension, nonconstantCoordinateExtension, coefficientCoordinateSplit,
      coefficientConstantCoordinates, constantCoefficientSlotEquiv, zeroCoefficientExponent]
  · simp [constantCoordinateExtension, nonconstantCoordinateExtension, coefficientCoordinateSplit, hz]

theorem coordinateSiteValue_constant {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) (c : SiteTorus Unit U) :
    coordinateSiteValue U t (constantCoordinateExtension U c) = c := by
  funext j
  change (∑ d : BoundedCoefficientExponent K (j.val + 1),
    boundedSiteMatrix (j.val + 1) (fun _ : Unit => t) () d •
      (if d.val = 0 then c j else 0)) = c j
  rw [Finset.sum_eq_single (zeroCoefficientExponent K (j.val + 1))]
  · simp [boundedSiteMatrix, zeroCoefficientExponent]
  · intro d _ hd
    have hz : d.val ≠ 0 := fun he => hd (Subtype.ext he)
    simp [hz]
  · simp

theorem coordinateSiteValue_split {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) (x : CoefficientCoordinateTori (K := K) U) :
    coordinateSiteValue U t x = (coefficientCoordinateSplit U x).2 +
      coordinateSiteValue U t (nonconstantCoordinateExtension U (coefficientCoordinateSplit U x).1) := by
  calc
    _ = coordinateSiteValue U t (constantCoordinateExtension U (coefficientCoordinateSplit U x).2 +
        nonconstantCoordinateExtension U (coefficientCoordinateSplit U x).1) :=
      congrArg (coordinateSiteValue U t) (coordinate_constant_decomposition U x)
    _ = _ := by rw [coordinateSiteValue_add, coordinateSiteValue_constant]

end Erdos3.VectorPolynomial

end

end OAI
