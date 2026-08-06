import PolynomialFormulas.GaussianPolynomialApproximationSearch
import PolynomialFormulas.GaussianPolynomialRootMatching
import PolynomialFormulas.GaussianPolynomialApproximationCore

/-!
# Correctness of the exhaustive Gaussian-rational root search

A valid search certificate supplies one contraction disk for every active
center of each monic factor.  The disks in a layer are pairwise disjoint, so
choosing one root from each disk gives all roots of that factor, with exactly
the multiplicities recorded by `Polynomial.roots`.  Concatenating the four
layer vectors then gives all roots of the input polynomial.

The executable search returns only Gaussian-rational centers.  The exact
complex roots chosen in this file are theorem-side witnesses; no classical
choice enters the search or its validity test.
-/

namespace LeanProofs.PolynomialFormulas

namespace GaussianPolynomialApproximationCorrectness

open GaussianPolynomialApproximationCore
open GaussianPolynomialApproximationCore.QPoly
open GaussianPolynomialApproximationSearch
open GaussianPolynomialContractionCertificate
open GaussianPolynomialRootMatching
open Metric Polynomial

noncomputable section

/-! ## One certified factor layer -/

/-- The active center in a factor layer. -/
def layerCenter (raw : RawCertificate) (i : Fin 4)
    (j : Fin (degree (raw.factors i))) : GaussianRat :=
  raw.centers i (layerSlot raw i j)

/-- The automatically computed radius of an active center. -/
def layerRadius (raw : RawCertificate) (i : Fin 4)
    (j : Fin (degree (raw.factors i))) : ℚ :=
  radius raw i (layerSlot raw i j)

theorem layerSlot_injective (raw : RawCertificate) (i : Fin 4) :
    Function.Injective (layerSlot raw i) := by
  intro j k hjk
  apply Fin.ext
  simpa using congrArg Fin.val hjk

/-- Each active center has a certified root of its factor in the claimed
variable-radius disk. -/
theorem layer_has_certified_root {p : QPoly4} {ε : ℚ} {raw : RawCertificate}
    (h : IsValid p ε raw) (i : Fin 4)
    (j : Fin (degree (raw.factors i))) :
    ∃ z ∈ closedBall (GaussianRat.toComplex (layerCenter raw i j))
        (layerRadius raw i j : ℝ),
      (toComplexPolynomial (raw.factors i)).eval z = 0 := by
  have hactive := layerSlot_active raw i j
  have hvalid := h.activeAutoValid i (layerSlot raw i j) hactive
  obtain ⟨z, hz, hzero⟩ := autoValid_exists_zero_in_closedBall hvalid
  refine ⟨z, ?_, ?_⟩
  · simpa [layerCenter, layerRadius, radius] using hz
  · rw [← evalComplex_eq_toComplexPolynomial_eval]
    exact hzero

/-- Distinct active centers in a layer have disjoint certified disks.  The
rational `linf` lower bound converts to Euclidean center distance. -/
theorem layer_centers_separated {p : QPoly4} {ε : ℚ} {raw : RawCertificate}
    (h : IsValid p ε raw) (i : Fin 4)
    (j k : Fin (degree (raw.factors i))) (hjk : j ≠ k) :
    (layerRadius raw i j : ℝ) + (layerRadius raw i k : ℝ) <
      dist (GaussianRat.toComplex (layerCenter raw i j))
        (GaussianRat.toComplex (layerCenter raw i k)) := by
  have hslots : layerSlot raw i j ≠ layerSlot raw i k :=
    (layerSlot_injective raw i).ne hjk
  have hsep := h.activeSeparated i (layerSlot raw i j) (layerSlot raw i k)
    (layerSlot_active raw i j) (layerSlot_active raw i k) hslots
  calc
    (layerRadius raw i j : ℝ) + (layerRadius raw i k : ℝ) =
        ((layerRadius raw i j + layerRadius raw i k : ℚ) : ℝ) := by
      push_cast
      rfl
    _ < (GaussianRat.linf
        (layerCenter raw i j - layerCenter raw i k) : ℚ) := by
      exact_mod_cast hsep
    _ ≤ ‖GaussianRat.toComplex
        (layerCenter raw i j - layerCenter raw i k)‖ :=
      GaussianRat.linf_toComplex_le_norm _
    _ = dist (GaussianRat.toComplex (layerCenter raw i j))
        (GaussianRat.toComplex (layerCenter raw i k)) := by
      rw [GaussianRat.toComplex_sub, dist_eq_norm]

theorem factor_toComplex_monic {p : QPoly4} {ε : ℚ} {raw : RawCertificate}
    (h : IsValid p ε raw) (i : Fin 4) :
    (toComplexPolynomial (raw.factors i)).Monic := by
  rw [toComplexPolynomial_eq_map]
  apply Polynomial.Monic.map
  rw [Polynomial.Monic, ← leadingCoeff_eq_toPolynomial]
  exact h.monicFactors i

theorem factor_toComplex_ne_zero {p : QPoly4} {ε : ℚ} {raw : RawCertificate}
    (h : IsValid p ε raw) (i : Fin 4) :
    toComplexPolynomial (raw.factors i) ≠ 0 :=
  (factor_toComplex_monic h i).ne_zero

theorem factor_toComplex_natDegree {p : QPoly4} {ε : ℚ}
    {raw : RawCertificate} (_h : IsValid p ε raw) (i : Fin 4) :
    (toComplexPolynomial (raw.factors i)).natDegree = degree (raw.factors i) := by
  rw [toComplexPolynomial_eq_map,
    Polynomial.natDegree_map_eq_of_injective GaussianRat.toComplex_injective,
    ← degree_eq_natDegree]

theorem factor_toComplex_splits {p : QPoly4} {ε : ℚ} {raw : RawCertificate}
    (_h : IsValid p ε raw) (i : Fin 4) :
    (toComplexPolynomial (raw.factors i)).Splits :=
  IsAlgClosed.splits _

/-- A full root vector exists for each layer.  It contains one root in every
certified disk, is injective, and enumerates the factor's root multiset. -/
theorem exists_layer_root_vector {p : QPoly4} {ε : ℚ} {raw : RawCertificate}
    (h : IsValid p ε raw) (i : Fin 4) :
    ∃ u : Fin (degree (raw.factors i)) → ℂ,
      (∀ j, u j ∈ closedBall (GaussianRat.toComplex (layerCenter raw i j))
        (layerRadius raw i j : ℝ)) ∧
      Function.Injective u ∧
      vectorMultiset u = (toComplexPolynomial (raw.factors i)).roots := by
  obtain ⟨u, hroots, hmem⟩ :=
    exists_root_vector_of_pairwiseDisjoint_closedBalls
      (factor_toComplex_ne_zero h i) (factor_toComplex_splits h i)
      (factor_toComplex_natDegree h i)
      (fun j => GaussianRat.toComplex (layerCenter raw i j))
      (fun j => (layerRadius raw i j : ℝ))
      (layer_has_certified_root h i) (layer_centers_separated h i)
  have hinjective : Function.Injective u :=
    injective_of_mem_pairwiseDisjoint_closedBalls hmem
      (layer_centers_separated h i)
  exact ⟨u, hmem, hinjective, hroots⟩

/-- The theorem-side exact roots selected for one factor layer. -/
noncomputable def exactLayerRoots {p : QPoly4} {ε : ℚ}
    (raw : RawCertificate) (h : IsValid p ε raw) (i : Fin 4) :
    Fin (degree (raw.factors i)) → ℂ :=
  Classical.choose (exists_layer_root_vector h i)

theorem exactLayerRoots_mem_closedBall {p : QPoly4} {ε : ℚ}
    {raw : RawCertificate} (h : IsValid p ε raw) (i : Fin 4)
    (j : Fin (degree (raw.factors i))) :
    exactLayerRoots raw h i j ∈
      closedBall (GaussianRat.toComplex (layerCenter raw i j))
        (layerRadius raw i j : ℝ) :=
  (Classical.choose_spec (exists_layer_root_vector h i)).1 j

theorem exactLayerRoots_injective {p : QPoly4} {ε : ℚ}
    {raw : RawCertificate} (h : IsValid p ε raw) (i : Fin 4) :
    Function.Injective (exactLayerRoots raw h i) :=
  (Classical.choose_spec (exists_layer_root_vector h i)).2.1

theorem exactLayerRoots_vectorMultiset {p : QPoly4} {ε : ℚ}
    {raw : RawCertificate} (h : IsValid p ε raw) (i : Fin 4) :
    vectorMultiset (exactLayerRoots raw h i) =
      (toComplexPolynomial (raw.factors i)).roots :=
  (Classical.choose_spec (exists_layer_root_vector h i)).2.2

theorem exactLayerRoots_listMultiset {p : QPoly4} {ε : ℚ}
    {raw : RawCertificate} (h : IsValid p ε raw) (i : Fin 4) :
    (List.ofFn (exactLayerRoots raw h i) : Multiset ℂ) =
      (toComplexPolynomial (raw.factors i)).roots := by
  simpa [vectorMultiset] using exactLayerRoots_vectorMultiset h i

/-! ## Accuracy and list pairing -/

theorem exactLayerRoots_accuracy {p : QPoly4} {ε : ℚ}
    {raw : RawCertificate} (h : IsValid p ε raw) (i : Fin 4)
    (j : Fin (degree (raw.factors i))) :
    GaussianRat.complexManhattan (exactLayerRoots raw h i j)
        (GaussianRat.toComplex (layerCenter raw i j)) ≤ (ε : ℝ) := by
  have hdist := mem_closedBall.mp (exactLayerRoots_mem_closedBall h i j)
  have haccuracy := h.activeAccuracy i (layerSlot raw i j)
    (layerSlot_active raw i j)
  calc
    GaussianRat.complexManhattan (exactLayerRoots raw h i j)
        (GaussianRat.toComplex (layerCenter raw i j)) ≤
        2 * dist (exactLayerRoots raw h i j)
          (GaussianRat.toComplex (layerCenter raw i j)) :=
      GaussianRat.complexManhattan_le_two_dist _ _
    _ ≤ 2 * (layerRadius raw i j : ℝ) := by
      exact mul_le_mul_of_nonneg_left hdist (by norm_num)
    _ ≤ (ε : ℝ) := by
      exact_mod_cast haccuracy

private theorem forall₂_ofFn {α β : Type*} {R : α → β → Prop} {n : ℕ}
    (f : Fin n → α) (g : Fin n → β) (h : ∀ i, R (f i) (g i)) :
    List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero => simp [List.ofFn_zero]
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      exact List.Forall₂.cons (h 0)
        (ih (fun j => f j.succ) (fun j => g j.succ) (fun j => h j.succ))

theorem exactLayerRoots_forall₂ {p : QPoly4} {ε : ℚ}
    {raw : RawCertificate} (h : IsValid p ε raw) (i : Fin 4) :
    List.Forall₂
      (fun center root =>
        GaussianRat.complexManhattan root (GaussianRat.toComplex center) ≤ (ε : ℝ))
      (layerCenters raw i) (List.ofFn (exactLayerRoots raw h i)) := by
  simpa [layerCenters, layerCenter] using
    forall₂_ofFn
      (fun j : Fin (degree (raw.factors i)) => layerCenter raw i j)
      (exactLayerRoots raw h i) (exactLayerRoots_accuracy h i)

/-! ## Combining the four layers -/

/-- The theorem-side exact roots in the same layer order as `centersList`. -/
noncomputable def exactRootsList {p : QPoly4} {ε : ℚ}
    (raw : RawCertificate) (h : IsValid p ε raw) : List ℂ :=
  List.ofFn (exactLayerRoots raw h 0) ++
    List.ofFn (exactLayerRoots raw h 1) ++
    List.ofFn (exactLayerRoots raw h 2) ++
    List.ofFn (exactLayerRoots raw h 3)

@[simp]
theorem exactRootsList_length {p : QPoly4} {ε : ℚ}
    (raw : RawCertificate) (h : IsValid p ε raw) :
    (exactRootsList raw h).length = degree p := by
  simp only [exactRootsList, List.length_append, List.length_ofFn]
  rw [← h.degreeSum]
  unfold factorDegreeSum
  omega

theorem productMatches_toPolynomial {p : QPoly4} {raw : RawCertificate}
    (h : ProductMatches p raw) :
    toPolynomial (factorProduct raw) = toPolynomial p := by
  apply Polynomial.ext
  intro k
  simp only [coeff_toPolynomial]
  by_cases hk : k < 17
  · change coeff (factorProduct raw) (↑(⟨k, hk⟩ : Fin 17)) = coeff p k
    rw [coeff_apply]
    exact h ⟨k, hk⟩
  · rw [coeff_eq_zero_of_bound_lt (factorProduct raw) (by omega),
      coeff_eq_zero_of_bound_lt p (by omega)]

theorem productMatches_toComplexPolynomial {p : QPoly4} {raw : RawCertificate}
    (h : ProductMatches p raw) :
    toComplexPolynomial (factorProduct raw) = toComplexPolynomial p := by
  rw [toComplexPolynomial_eq_map, toComplexPolynomial_eq_map,
    productMatches_toPolynomial h]

theorem toComplexPolynomial_factorProduct (raw : RawCertificate) :
    toComplexPolynomial (factorProduct raw) =
      (toComplexPolynomial (raw.factors 0) *
        toComplexPolynomial (raw.factors 1)) *
      (toComplexPolynomial (raw.factors 2) *
        toComplexPolynomial (raw.factors 3)) := by
  simp [factorProduct, toComplexPolynomial_eq_map]

theorem factorProduct_eq_input {p : QPoly4} {ε : ℚ} {raw : RawCertificate}
    (h : IsValid p ε raw) :
    (toComplexPolynomial (raw.factors 0) *
        toComplexPolynomial (raw.factors 1)) *
      (toComplexPolynomial (raw.factors 2) *
        toComplexPolynomial (raw.factors 3)) =
      toComplexPolynomial p := by
  rw [← toComplexPolynomial_factorProduct]
  exact productMatches_toComplexPolynomial h.productMatches

/-- The concatenated exact list is exactly the input polynomial's root
multiset, including multiplicity. -/
theorem exactRootsList_multiset {p : QPoly4} {ε : ℚ}
    {raw : RawCertificate} (h : IsValid p ε raw) :
    (exactRootsList raw h : Multiset ℂ) = (toComplexPolynomial p).roots := by
  have h0 := factor_toComplex_ne_zero h (0 : Fin 4)
  have h1 := factor_toComplex_ne_zero h (1 : Fin 4)
  have h2 := factor_toComplex_ne_zero h (2 : Fin 4)
  have h3 := factor_toComplex_ne_zero h (3 : Fin 4)
  have h01 : toComplexPolynomial (raw.factors 0) *
      toComplexPolynomial (raw.factors 1) ≠ 0 := mul_ne_zero h0 h1
  have h23 : toComplexPolynomial (raw.factors 2) *
      toComplexPolynomial (raw.factors 3) ≠ 0 := mul_ne_zero h2 h3
  have hall :
      (toComplexPolynomial (raw.factors 0) *
          toComplexPolynomial (raw.factors 1)) *
        (toComplexPolynomial (raw.factors 2) *
          toComplexPolynomial (raw.factors 3)) ≠ 0 :=
    mul_ne_zero h01 h23
  rw [← factorProduct_eq_input h, Polynomial.roots_mul hall,
    Polynomial.roots_mul h01, Polynomial.roots_mul h23]
  unfold exactRootsList
  change
    (((List.ofFn (exactLayerRoots raw h 0) : Multiset ℂ) +
        (List.ofFn (exactLayerRoots raw h 1) : Multiset ℂ)) +
      (List.ofFn (exactLayerRoots raw h 2) : Multiset ℂ)) +
      (List.ofFn (exactLayerRoots raw h 3) : Multiset ℂ) = _
  rw [exactLayerRoots_listMultiset h 0, exactLayerRoots_listMultiset h 1,
    exactLayerRoots_listMultiset h 2, exactLayerRoots_listMultiset h 3]
  ac_rfl

/-- The exact roots are paired position-for-position with the executable
Gaussian-rational center list and satisfy the requested Manhattan error. -/
theorem centersList_forall₂_exactRootsList {p : QPoly4} {ε : ℚ}
    {raw : RawCertificate} (h : IsValid p ε raw) :
    List.Forall₂
      (fun center root =>
        GaussianRat.complexManhattan root (GaussianRat.toComplex center) ≤ (ε : ℝ))
      (centersList raw) (exactRootsList raw h) := by
  unfold centersList exactRootsList
  exact List.rel_append
    (List.rel_append
      (List.rel_append (exactLayerRoots_forall₂ h 0)
        (exactLayerRoots_forall₂ h 1))
      (exactLayerRoots_forall₂ h 2))
    (exactLayerRoots_forall₂ h 3)

end

end GaussianPolynomialApproximationCorrectness

end LeanProofs.PolynomialFormulas
