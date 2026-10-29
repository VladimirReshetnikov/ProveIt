import DiophantineConsistency.QuadraticCoding

/-!
# Selective quadratic extraction with arbitrary row targets

Only pairs used by the supplied rows have to be isolated among all ordered
pairs. Other positions may collide. Row support intervals may overlap when
no term from another row reaches a selected target. This is the common
algebraic foundation of the wave-7 support-sensitive proposals.
-/

namespace DiophantineConsistency.SelectiveQuadraticCoding

open Polynomial SidonPositions
open scoped BigOperators

variable {R : Type*} [CommRing R] {m r : ℕ}

def pairWeight (w : Fin (m + 1) → ℕ) (p : PairIndex m) : ℕ :=
  w p.val.1 + w p.val.2

/-- Isolation is required only at the chosen supported pair. -/
def Isolated (w : Fin (m + 1) → ℕ) (p : PairIndex m) : Prop :=
  ∀ i j, w i + w j = pairWeight w p ↔
    (i = p.val.1 ∧ j = p.val.2) ∨ (i = p.val.2 ∧ j = p.val.1)

noncomputable def encoded (w : Fin (m + 1) → ℕ) (u : Fin (m + 1) → R) : R[X] :=
  ∑ i, monomial (w i) (u i)

theorem encoded_square (w : Fin (m + 1) → ℕ) (u : Fin (m + 1) → R) :
    encoded w u ^ 2 = ∑ i, ∑ j, monomial (w i + w j) (u i * u j) := by
  simp only [pow_two, encoded, Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial]
  rw [Finset.sum_comm]

theorem coeff_encoded_square (w : Fin (m + 1) → ℕ) (u : Fin (m + 1) → R)
    (p : PairIndex m) (hp : Isolated w p) :
    (encoded w u ^ 2).coeff (pairWeight w p) =
      if p.val.1 = p.val.2 then u p.val.1 ^ 2 else 2 * u p.val.1 * u p.val.2 := by
  exact QuadraticFiber.coeff_square_at_isolated w u p.val.1 p.val.2 hp

def rowValue (s : Finset (PairIndex m)) (a : PairIndex m → R)
    (u : Fin (m + 1) → R) : R :=
  ∑ p ∈ s, a p * u p.val.1 * u p.val.2

noncomputable def complementary (w : Fin (m + 1) → ℕ) (s : Finset (PairIndex m))
    (a : PairIndex m → R) (E : ℕ) : R[X] :=
  ∑ p ∈ s, monomial (E - pairWeight w p) (QuadraticCoding.correction p * a p)

/-- Complete coefficient identity for one supported row, allowing unused collisions. -/
theorem coeff_square_mul_complementary (w : Fin (m + 1) → ℕ)
    (s : Finset (PairIndex m)) (a : PairIndex m → R) (u : Fin (m + 1) → R)
    (E : ℕ) (hE : ∀ p ∈ s, pairWeight w p ≤ E)
    (hi : ∀ p ∈ s, Isolated w p) :
    (encoded w u ^ 2 * complementary w s a E).coeff E = 2 * rowValue s a u := by
  classical
  simp only [complementary, Finset.mul_sum, finsetSum_coeff]
  rw [rowValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hc := coeff_mul_monomial (encoded w u ^ 2) (E - pairWeight w p)
    (pairWeight w p) (QuadraticCoding.correction p * a p)
  rw [Nat.add_sub_of_le (hE p hp)] at hc
  rw [hc, coeff_encoded_square w u p (hi p hp)]
  by_cases h : p.val.1 = p.val.2
  · simp only [QuadraticCoding.correction, if_pos h]
    rw [h]
    ring
  · simp only [QuadraticCoding.correction, if_neg h, one_mul]
    ring

/-- Exclude cross-row contributions only at the tested target. -/
theorem coeff_at_other_target (w : Fin (m + 1) → ℕ) (s : Finset (PairIndex m))
    (a : PairIndex m → R) (u : Fin (m + 1) → R) (E F : ℕ)
    (hx : ∀ p ∈ s, ∀ i j, w i + w j + (E - pairWeight w p) ≠ F) :
    (encoded w u ^ 2 * complementary w s a E).coeff F = 0 := by
  classical
  rw [complementary, Finset.mul_sum]
  simp only [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro p hp
  rw [encoded_square]
  simp only [Finset.sum_mul, finsetSum_coeff, monomial_mul_monomial]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [coeff_monomial, if_neg (hx p hp i j)]

noncomputable def combined (w : Fin (m + 1) → ℕ) (s : Fin r → Finset (PairIndex m))
    (a : Fin r → PairIndex m → R) (E : Fin r → ℕ) : R[X] :=
  ∑ j, complementary w (s j) (a j) (E j)

/-- One square and one combined kernel recover all rows, with arbitrary targets. -/
theorem coeff_square_mul_combined (w : Fin (m + 1) → ℕ)
    (s : Fin r → Finset (PairIndex m)) (a : Fin r → PairIndex m → R)
    (u : Fin (m + 1) → R) (E : Fin r → ℕ)
    (hE : ∀ k p, p ∈ s k → pairWeight w p ≤ E k)
    (hi : ∀ k p, p ∈ s k → Isolated w p)
    (hx : ∀ k l, k ≠ l → ∀ p ∈ s k, ∀ i j,
      w i + w j + (E k - pairWeight w p) ≠ E l) (l : Fin r) :
    (encoded w u ^ 2 * combined w s a E).coeff (E l) = 2 * rowValue (s l) (a l) u := by
  classical
  rw [combined, Finset.mul_sum, finsetSum_coeff, Finset.sum_eq_single l]
  · exact coeff_square_mul_complementary w (s l) (a l) u (E l) (hE l) (hi l)
  · intro k _ hkl
    exact coeff_at_other_target w (s k) (a k) u (E k) (E l) (hx k l hkl)
  · intro hl
    exact False.elim (hl (Finset.mem_univ l))

/-- Spacing one above the largest possible pair sum suffices for targets,
even though the complete row support intervals can overlap. -/
def regularTarget (W k : ℕ) : ℕ := (2 * W + 1) * (k + 1)

theorem regularTarget_separated (W : ℕ) {k l : ℕ} (hkl : k < l) :
    regularTarget W k + 2 * W < regularTarget W l := by
  have h := Nat.mul_le_mul_left (2 * W + 1) (by omega : k + 1 + 1 ≤ l + 1)
  rw [Nat.mul_add] at h
  simp only [Nat.mul_one] at h
  dsimp only [regularTarget]
  omega

theorem pairWeight_le_of_bound (w : Fin (m + 1) → ℕ) (W : ℕ)
    (hw : ∀ i, w i ≤ W) (p : PairIndex m) : pairWeight w p ≤ 2 * W := by
  have h1 := hw p.val.1
  have h2 := hw p.val.2
  dsimp only [pairWeight]
  omega

theorem pairWeight_le_regularTarget (w : Fin (m + 1) → ℕ) (W : ℕ)
    (hw : ∀ i, w i ≤ W) (p : PairIndex m) (k : ℕ) :
    pairWeight w p ≤ regularTarget W k := by
  have h := Nat.mul_le_mul_left (2 * W + 1) (by omega : 1 ≤ k + 1)
  rw [Nat.mul_one] at h
  exact (pairWeight_le_of_bound w W hw p).trans (by dsimp [regularTarget]; omega)

theorem cross_regularTarget (w : Fin (m + 1) → ℕ) (W : ℕ)
    (hw : ∀ i, w i ≤ W) {k l : ℕ} (hkl : k ≠ l) (p : PairIndex m)
    (i j : Fin (m + 1)) :
    w i + w j + (regularTarget W k - pairWeight w p) ≠ regularTarget W l := by
  have hp := pairWeight_le_of_bound w W hw p
  have hE := pairWeight_le_regularTarget w W hw p k
  have hi := hw i
  have hj := hw j
  rcases lt_or_gt_of_ne hkl with h | h
  · have hs := regularTarget_separated W h
    omega
  · have hs := regularTarget_separated W h
    omega

theorem coeff_square_mul_regular (w : Fin (m + 1) → ℕ) (W : ℕ)
    (hw : ∀ i, w i ≤ W) (s : Fin r → Finset (PairIndex m))
    (a : Fin r → PairIndex m → R) (u : Fin (m + 1) → R)
    (hi : ∀ k p, p ∈ s k → Isolated w p) (l : Fin r) :
    (encoded w u ^ 2 * combined w s a (fun k => regularTarget W k.val)).coeff
      (regularTarget W l.val) = 2 * rowValue (s l) (a l) u := by
  apply coeff_square_mul_combined
  · intro k p _
    exact pairWeight_le_regularTarget w W hw p k.val
  · exact hi
  · intro k l hkl p _ i j
    exact cross_regularTarget w W hw (fun h => hkl (Fin.ext h)) p i j

end DiophantineConsistency.SelectiveQuadraticCoding
