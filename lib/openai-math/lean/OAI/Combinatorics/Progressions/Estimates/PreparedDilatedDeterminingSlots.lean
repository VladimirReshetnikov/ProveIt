import OAI.Combinatorics.Progressions.Linear.DeterminingMatrixDilation
import OAI.Combinatorics.Progressions.Linear.PreparedDeterminingMatrixBudget

namespace OAI

section

namespace Erdos3.RankPreparationFamily
open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))
variable (c : ∀ j, (L j).space)
variable (hmem : ∀ j α, coefficients (L j).poly α ∈ (L j).space)

noncomputable def dilatedCenteredDeterminingPolynomial (q : ℕ)
    (a : Fin (Fintype.card (Σ j, E j))) : MvPolynomial X ℝ :=
  (q : ℝ)⁻¹ • L.centeredDeterminingPolynomial bW c hmem a

noncomputable def dilatedSortedDeterminingMatrix (q : ℕ) {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) :
    Fin n → Fin (Fintype.card (Σ j, E j)) → ℤ :=
  dilatedIntegerMatrix q (L.sortedDeterminingMatrix bW e)

theorem dilatedCenteredDeterminingPolynomial_support (q : ℕ)
    (hdegree : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L j).poly)
    (a : Fin (Fintype.card (Σ j, E j))) :
    L.dilatedCenteredDeterminingPolynomial bW c hmem q a ∈
      weightedSupportLE (fun _ : X => 1) (sortedLayerCoordinateWeight E a) :=
  (weightedSupportLE _ _).smul_mem _
    (L.centeredDeterminingPolynomial_support bW c hmem hdegree a)

@[simp] theorem dilatedCenteredDeterminingPolynomial_eval (q : ℕ)
    (x : X → ℝ) (a : Fin (Fintype.card (Σ j, E j))) :
    MvPolynomial.aeval x (L.dilatedCenteredDeterminingPolynomial bW c hmem q a) =
      MvPolynomial.aeval x (L.centeredDeterminingPolynomial bW c hmem a) / (q : ℝ) := by
  simp [dilatedCenteredDeterminingPolynomial, map_smul, smul_eq_mul, div_eq_mul_inv,
    mul_comm]

theorem dilatedCenteredDeterminingPolynomial_reconstruction (q : ℕ) (hq : 0 < q)
    {n : ℕ} (e : Fin n ≃ L.PreparedCoordinate) (x : X → ℝ) (i : Fin n) :
    realIntegerMatrix (L.dilatedSortedDeterminingMatrix bW q e)
      (fun a => MvPolynomial.aeval x (L.dilatedCenteredDeterminingPolynomial bW c hmem q a)) i =
      eval x (L (e i).1).poly (e i).2 - (c (e i).1).val (e i).2 := by
  simp only [dilatedSortedDeterminingMatrix, dilatedCenteredDeterminingPolynomial_eval]
  rw [realIntegerMatrix_dilated_div q (L.sortedDeterminingMatrix bW e) hq]
  exact L.centeredDeterminingPolynomial_reconstruction bW c hmem e x i

theorem fullTaggedBufferedCoordinates_eq_dilatedCenteredDetermining (q : ℕ) (hq : 0 < q)
    {n : ℕ} (e : Fin n ≃ L.PreparedCoordinate) (x : X → ℤ) :
    fullTaggedBufferedCoordinates e (fun j => (L j).poly) (fun j => (c j).val) x =
      realIntegerMatrix (L.dilatedSortedDeterminingMatrix bW q e)
        (fun a => MvPolynomial.aeval (fun i => (x i : ℝ))
          (L.dilatedCenteredDeterminingPolynomial bW c hmem q a)) := by
  funext i
  exact (L.dilatedCenteredDeterminingPolynomial_reconstruction bW c hmem q hq e
    (fun i => (x i : ℝ)) i).symm

theorem dilatedSortedDeterminingMatrix_dvd (q : ℕ) {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n)
    (a : Fin (Fintype.card (Σ j, E j))) :
    (q : ℤ) ∣ L.dilatedSortedDeterminingMatrix bW q e i a :=
  ⟨L.sortedDeterminingMatrix bW e i a, rfl⟩

theorem dilatedSortedDeterminingMatrix_weight (q : ℕ) {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n)
    (a : Fin (Fintype.card (Σ j, E j)))
    (hne : L.dilatedSortedDeterminingMatrix bW q e i a ≠ 0) :
    sortedLayerCoordinateWeight E a ≤ (e i).1.val + 1 := by
  apply L.sortedDeterminingMatrix_weight bW e i a
  intro hzero
  apply hne
  simp [dilatedSortedDeterminingMatrix, dilatedIntegerMatrix, hzero]

theorem dilatedSortedDeterminingMatrix_row_abs_sum_le (q : ℕ) {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n) {K : ℝ}
    (hK : (∑ a, |(L.sortedDeterminingMatrix bW e i a : ℝ)|) ≤ K) :
    (∑ a, |(L.dilatedSortedDeterminingMatrix bW q e i a : ℝ)|) ≤ (q : ℝ) * K :=
  dilatedIntegerMatrix_row_abs_sum_le q (L.sortedDeterminingMatrix bW e) i hK

theorem dilatedSortedDeterminingMatrix_row_abs_sum_le_exp (q : ℕ) {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n) {a b : ℝ}
    (hq : (q : ℝ) ≤ Real.exp a)
    (hM : (∑ j, |(L.sortedDeterminingMatrix bW e i j : ℝ)|) ≤ Real.exp b) :
    (∑ j, |(L.dilatedSortedDeterminingMatrix bW q e i j : ℝ)|) ≤ Real.exp (a + b) := by
  calc
    _ ≤ (q : ℝ) * Real.exp b := L.dilatedSortedDeterminingMatrix_row_abs_sum_le bW q e i hM
    _ ≤ Real.exp a * Real.exp b := mul_le_mul_of_nonneg_right hq (Real.exp_nonneg b)
    _ = Real.exp (a + b) := (Real.exp_add a b).symm

noncomputable def dilatedCenteredDeterminingPatch (q : ℕ) {s : ℕ} (hm : m ≤ s)
    (hdegree : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L j).poly)
    (Φ : PatchKernel (Fintype.card (Σ j, E j))) :
    PolynomialPatch X s (Fintype.card (Σ j, E j)) :=
  PolynomialPatch.ofCoordinates (sortedLayerCoordinateWeight E)
    (sortedLayerCoordinateWeight_pos E)
    (fun i => (sortedLayerCoordinateWeight_le E i).trans hm)
    (sortedLayerCoordinateWeight_mono E)
    (L.dilatedCenteredDeterminingPolynomial bW c hmem q)
    (L.dilatedCenteredDeterminingPolynomial_support bW c hmem q hdegree) Φ

@[simp] theorem dilatedCenteredDeterminingPatch_weight (q : ℕ) {s : ℕ} (hm : m ≤ s)
    (hdegree : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L j).poly)
    (Φ : PatchKernel (Fintype.card (Σ j, E j))) :
    (L.dilatedCenteredDeterminingPatch bW c hmem q hm hdegree Φ).weight =
      sortedLayerCoordinateWeight E := rfl

@[simp] theorem dilatedCenteredDeterminingPatch_kernel (q : ℕ) {s : ℕ} (hm : m ≤ s)
    (hdegree : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L j).poly)
    (Φ : PatchKernel (Fintype.card (Σ j, E j))) :
    (L.dilatedCenteredDeterminingPatch bW c hmem q hm hdegree Φ).kernel = Φ := rfl

end Erdos3.RankPreparationFamily

end

end OAI
