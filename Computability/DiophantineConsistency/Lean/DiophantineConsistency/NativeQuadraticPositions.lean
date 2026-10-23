import DiophantineConsistency.NativeQuadraticParent
import DiophantineConsistency.SelectiveCoefficientBounds

/-!
# Actual package-52 source positions, span, and simultaneous carry test

The finite position proof uses only the 136 supported records of the original
interior-regular certificate. The complete source and arbitrary four-port
coefficients are imported from NativeQuadraticParent. Coefficient-size and
binary-base assumptions remain explicit; no native compiler is postulated.
-/

namespace DiophantineConsistency.NativeQuadraticPositions

open Polynomial SidonPositions SelectiveQuadraticCoding NativeQuadraticParent
open scoped BigOperators

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

def target (k : Fin 22) : ℕ := 349 * (k.val + 1)

private theorem index_span : ∀ k i, i ∈ rowSupportIndices k →
    target k - pairWeight SelectiveCertificate52.weights (SelectiveCertificate52.activePair i) ≤ 7516 := by
  intro k i hi
  fin_cases k
  · change i ∈ {32, 1, 25, 0} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {37, 1, 17, 25, 0} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {35, 1, 11, 22, 0} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {48, 10, 17, 18, 21, 0} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {50, 52, 13, 53, 55, 18, 20, 21} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {50, 14, 58, 19, 20, 0} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {49, 12, 51, 13, 54, 14, 60, 0} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {57, 16, 62, 20, 21, 22, 23, 0} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {63, 21, 31, 0} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {61, 20, 24} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    all_goals decide
  · change i ∈ {65, 23, 66, 24, 31, 0} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {45, 6, 47, 9, 13, 14, 18, 20, 27} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {32, 33, 36, 37, 1, 39, 40, 2, 42, 3, 47, 9, 17, 20, 25, 27, 0} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {34, 35, 1, 38, 2, 41, 3, 4, 11, 0} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {43, 5, 26} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    all_goals decide
  · change i ∈ {44, 5, 8, 20, 27, 0} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {56, 15, 68, 27, 28, 0} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {46, 7, 24, 29} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {70, 29, 30} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    all_goals decide
  · change i ∈ {67, 26, 30, 0} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {56, 15, 69, 28, 30, 0} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · change i ∈ {59, 18, 64, 21, 0} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    all_goals decide

theorem encoding_span (k : Fin 22) (p : PairIndex 31) (hp : p ∈ rowSupport k) :
    target k - pairWeight SelectiveCertificate52.weights p ≤ 7516 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  exact index_span k i hi

theorem target_lt_span (k : Fin 22) : target k < 7865 := by
  have hk := k.isLt
  dsimp [target]
  omega

noncomputable def kernel (ports : Fin 4 → ℤ) : ℤ[X] :=
  combined SelectiveCertificate52.weights rowSupport (rowCoefficient ports) target

noncomputable def product (ports : Fin 4 → ℤ) (x : Fin 31 → ℤ) : ℤ[X] :=
  SelectiveCarry.rowProduct SelectiveCertificate52.weights rowSupport (rowCoefficient ports) (padded x) target

theorem product_degree_lt (ports : Fin 4 → ℤ) (x : Fin 31 → ℤ) :
    (product ports x).natDegree < 7865 := by
  exact SelectiveCarry.rowProduct_degree_lt _ _ _ _ _ 174 7516
    SelectiveCertificate52.maximum_weight encoding_span

theorem kernel_exponents_injective {k l : Fin 22} {p q : PairIndex 31}
    (hp : p ∈ rowSupport k) (hq : q ∈ rowSupport l)
    (he : target k - pairWeight SelectiveCertificate52.weights p =
      target l - pairWeight SelectiveCertificate52.weights q) : k = l ∧ p = q := by
  apply SelectiveCoefficientBounds.kernel_exponents_injective
    SelectiveCertificate52.weights rowSupport target ?_ ?_ ?_ hp hq he
  · intro k p hp
    exact pairWeight_le_regularTarget SelectiveCertificate52.weights 174
      SelectiveCertificate52.maximum_weight p k.val
  · intro k p hp
    exact SelectiveCertificate52.support_isolated p (rowSupport_subset k p hp)
  · intro k l hkl p hp i j
    exact cross_regularTarget SelectiveCertificate52.weights 174
      SelectiveCertificate52.maximum_weight (fun h => hkl (Fin.ext h)) p i j

theorem kernel_degree_le (ports : Fin 4 → ℤ) : (kernel ports).natDegree ≤ 7516 := by
  exact SelectiveCarry.combined_degree_le _ _ _ _ 7516 encoding_span

theorem kernel_coefficient_at (ports : Fin 4 → ℤ) (k : Fin 22) (p : PairIndex 31)
    (hp : p ∈ rowSupport k) :
    (kernel ports).coeff (target k - pairWeight SelectiveCertificate52.weights p) =
      QuadraticCoding.correction p * rowCoefficient ports k p := by
  exact SelectiveCoefficientBounds.coeff_combined_at_entry _ _ _ _
    (fun k l p q hp hq he => kernel_exponents_injective hp hq he) k p hp

/-- The last constant guard is the actual top kernel entry for every port tuple. -/
theorem kernel_top_coefficient (ports : Fin 4 → ℤ) : (kernel ports).coeff 7516 = 2 := by
  have hp : SelectiveCertificate52.activePair 0 ∈ rowSupport 21 := by
    exact Finset.mem_image.mpr ⟨0, by decide, rfl⟩
  have h := kernel_coefficient_at ports 21 (SelectiveCertificate52.activePair 0) hp
  have he : target 21 - pairWeight SelectiveCertificate52.weights
      (SelectiveCertificate52.activePair 0) = 7516 := by decide
  have hc : rowCoefficient ports 21 (SelectiveCertificate52.activePair 0) = 1 := by
    unfold rowCoefficient SelectiveCertificate52.activePair
    rfl
  have hcor : (QuadraticCoding.correction (SelectiveCertificate52.activePair 0) : ℤ) = 2 := rfl
  rw [he, hc, hcor, mul_one] at h
  exact h

theorem kernel_natDegree (ports : Fin 4 → ℤ) : (kernel ports).natDegree = 7516 := by
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (kernel_degree_le ports)
    (by rw [kernel_top_coefficient]; norm_num)

theorem kernel_coefficient_bound (ports : Fin 4 → ℤ) {H : ℤ} (hH : 0 ≤ H)
    (hc : ∀ k p, p ∈ rowSupport k → |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ H)
    (n : ℕ) : |(kernel ports).coeff n| ≤ H := by
  exact SelectiveCoefficientBounds.abs_coeff_combined_le _ _ _ _ H hH hc
    (fun k l p q hp hq he => kernel_exponents_injective hp hq he) n

theorem coeff_product_target (ports : Fin 4 → ℤ) (x : Fin 31 → ℤ) (k : Fin 22) :
    (product ports x).coeff (target k) = 2 * shiftedRows ports x k := by
  exact coeff_source_rows ports x k

/-- The actual 22 residuals are tested individually, with explicit half-base bounds. -/
theorem tau_selected_rows_iff (ports : Fin 4 → ℤ) (x : Fin 31 → ℤ)
    {t : ℕ} (ht : 1 ≤ t)
    (hb : ∀ i < 7865, |(product ports x).coeff i| < 2 ^ (t - 1)) :
    Jones1982.τ 2 (2 * MultiTargetCarry.shiftedValue t 7865 (product ports x).coeff)
      (2 * MultiTargetCarry.selectedMask t 7865 (Finset.univ.image target)) = 0 ↔
      ∀ k, shiftedRows ports x k = 0 := by
  exact SelectiveCarry.tau_selected_rows_iff ht (product ports x) target (shiftedRows ports x)
    target_lt_span (coeff_product_target ports x) hb

/-- The supplied scale derives every needed coefficient bound, without a row-count factor. -/
theorem product_half_base_bound (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    {H : ℤ} (hH : 0 < H)
    (hc : ∀ k p, p ∈ rowSupport k → |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ H)
    {b t : ℕ} (hb : 0 < b) (ht : 1 ≤ t) (hx : ∀ i, x i < b)
    (hbase : (2 : ℤ) ^ t = 4096 * H * (b : ℤ) ^ 2) (n : ℕ) :
    |(product ports (fun i => (x i : ℤ))).coeff n| < 2 ^ (t - 1) := by
  exact SelectiveCoefficientBounds.half_base_bound_31 SelectiveCertificate52.weights x (kernel ports)
    hH (kernel_coefficient_bound ports hH.le hc) hb ht hx hbase n

/-- The high word evaluates the full source polynomial; the degree bound
rules out an unproved truncation of high coefficients. -/
theorem doubled_full_polynomial (ports : Fin 4 → ℤ) (x : Fin 31 → ℤ)
    {t : ℕ} (ht : 1 ≤ t)
    (hb : ∀ i < 7865, |(product ports x).coeff i| < 2 ^ (t - 1)) :
    ((2 * MultiTargetCarry.shiftedValue t 7865 (product ports x).coeff : ℕ) : ℤ) =
      2 * (product ports x).eval (2 ^ t) +
        (2 ^ t : ℤ) * ∑ i ∈ Finset.range 7865, (2 ^ t : ℤ) ^ i := by
  exact SelectiveCarry.doubled_shifted_polynomial_cast (product ports x) ht
    (product_degree_lt ports x) hb

theorem tau_selected_rows_iff_of_scale (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    {H : ℤ} (hH : 0 < H)
    (hc : ∀ k p, p ∈ rowSupport k → |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ H)
    {b t : ℕ} (hb : 0 < b) (ht : 1 ≤ t) (hx : ∀ i, x i < b)
    (hbase : (2 : ℤ) ^ t = 4096 * H * (b : ℤ) ^ 2) :
    Jones1982.τ 2
      (2 * MultiTargetCarry.shiftedValue t 7865 (product ports (fun i => (x i : ℤ))).coeff)
      (2 * MultiTargetCarry.selectedMask t 7865 (Finset.univ.image target)) = 0 ↔
      ∀ k, shiftedRows ports (fun i => (x i : ℤ)) k = 0 := by
  exact tau_selected_rows_iff ports _ ht
    (fun i hi => product_half_base_bound ports x hH hc hb ht hx hbase i)

/-- The calibrated simultaneous test recovers the complete literal 60-gate
predicate on positive successor inputs, with all four ports retained. -/
theorem tau_source_rows_iff_of_scale (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    {H : ℤ} (hH : 0 < H)
    (hc : ∀ k p, p ∈ rowSupport k → |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ H)
    {b t : ℕ} (hb : 0 < b) (ht : 1 ≤ t) (hx : ∀ i, x i < b)
    (hbase : (2 : ℤ) ^ t = 4096 * H * (b : ℤ) ^ 2) :
    Jones1982.τ 2
      (2 * MultiTargetCarry.shiftedValue t 7865 (product ports (fun i => (x i : ℤ))).coeff)
      (2 * MultiTargetCarry.selectedMask t 7865 (Finset.univ.image target)) = 0 ↔
      ∀ j, sourceRows ports (fun i => (x i : ℤ) + 1) j = 0 := by
  rw [tau_selected_rows_iff_of_scale ports x hH hc hb ht hx hbase]
  constructor
  · intro h j
    obtain ⟨k, rfl⟩ := rowOrder_surjective j
    exact h k
  · intro h k
    exact h (rowOrder k)

#print axioms encoding_span
#print axioms product_degree_lt
#print axioms kernel_exponents_injective
#print axioms tau_selected_rows_iff
#print axioms product_half_base_bound

end DiophantineConsistency.NativeQuadraticPositions
