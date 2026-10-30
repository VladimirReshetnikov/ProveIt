import DiophantineConsistency.SelectiveQuadraticCoding

/-!
# Separate constant, linear and quadratic coefficient channels

Each channel is multiplied only by the corresponding degree of the input
word. Consequently labels from different degrees may coincide. Within each
channel, only the supported terms and tested row targets need isolation.
-/

namespace DiophantineConsistency.DegreeSeparatedCoding

open Polynomial SidonPositions SelectiveQuadraticCoding
open scoped BigOperators

variable {R : Type*} [CommRing R] {m r : ℕ}

theorem coeff_encoded (w : Fin (m + 1) → ℕ) (hw : Function.Injective w)
    (u : Fin (m + 1) → R) (i : Fin (m + 1)) :
    (encoded w u).coeff (w i) = u i := by
  classical
  simp only [encoded, finsetSum_coeff, coeff_monomial, hw.eq_iff]
  simp

def linearValue (s : Finset (Fin (m + 1))) (a : Fin (m + 1) → R)
    (u : Fin (m + 1) → R) : R := ∑ i ∈ s, a i * u i

noncomputable def linearComplementary (w : Fin (m + 1) → ℕ)
    (s : Finset (Fin (m + 1))) (a : Fin (m + 1) → R) (E : ℕ) : R[X] :=
  ∑ i ∈ s, monomial (E - w i) (2 * a i)

theorem coeff_mul_linearComplementary (w : Fin (m + 1) → ℕ)
    (hw : Function.Injective w) (s : Finset (Fin (m + 1)))
    (a : Fin (m + 1) → R) (u : Fin (m + 1) → R) (E : ℕ)
    (hE : ∀ i ∈ s, w i ≤ E) :
    (encoded w u * linearComplementary w s a E).coeff E = 2 * linearValue s a u := by
  classical
  simp only [linearComplementary, Finset.mul_sum, finsetSum_coeff]
  rw [linearValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hc := coeff_mul_monomial (encoded w u) (E - w i) (w i) (2 * a i)
  rw [Nat.add_sub_of_le (hE i hi)] at hc
  rw [hc, coeff_encoded w hw u i]
  ring

theorem coeff_at_other_linearTarget (w : Fin (m + 1) → ℕ)
    (s : Finset (Fin (m + 1))) (a : Fin (m + 1) → R)
    (u : Fin (m + 1) → R) (E F : ℕ)
    (hx : ∀ i ∈ s, ∀ j, w j + (E - w i) ≠ F) :
    (encoded w u * linearComplementary w s a E).coeff F = 0 := by
  classical
  rw [linearComplementary, Finset.mul_sum]
  simp only [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [encoded]
  simp only [Finset.sum_mul, finsetSum_coeff, monomial_mul_monomial]
  apply Finset.sum_eq_zero
  intro j _
  rw [coeff_monomial, if_neg (hx i hi j)]

noncomputable def linearCombined (w : Fin (m + 1) → ℕ)
    (s : Fin r → Finset (Fin (m + 1))) (a : Fin r → Fin (m + 1) → R)
    (E : Fin r → ℕ) : R[X] := ∑ k, linearComplementary w (s k) (a k) (E k)

theorem coeff_mul_linearCombined (w : Fin (m + 1) → ℕ)
    (hw : Function.Injective w) (s : Fin r → Finset (Fin (m + 1)))
    (a : Fin r → Fin (m + 1) → R) (u : Fin (m + 1) → R) (E : Fin r → ℕ)
    (hE : ∀ k i, i ∈ s k → w i ≤ E k)
    (hx : ∀ k l, k ≠ l → ∀ i ∈ s k, ∀ j, w j + (E k - w i) ≠ E l)
    (l : Fin r) :
    (encoded w u * linearCombined w s a E).coeff (E l) = 2 * linearValue (s l) (a l) u := by
  classical
  rw [linearCombined, Finset.mul_sum, finsetSum_coeff, Finset.sum_eq_single l]
  · exact coeff_mul_linearComplementary w hw (s l) (a l) u (E l) (hE l)
  · intro k _ hkl
    exact coeff_at_other_linearTarget w (s k) (a k) u (E k) (E l) (hx k l hkl)
  · intro hl
    exact False.elim (hl (Finset.mem_univ l))

noncomputable def constantCombined (a : Fin r → R) (E : Fin r → ℕ) : R[X] :=
  ∑ k, monomial (E k) (2 * a k)

theorem coeff_constantCombined (a : Fin r → R) (E : Fin r → ℕ)
    (hE : Function.Injective E) (l : Fin r) :
    (constantCombined a E).coeff (E l) = 2 * a l := by
  classical
  simp only [constantCombined, finsetSum_coeff, coeff_monomial, hE.eq_iff]
  simp

def value (a0 : R) (s1 : Finset (Fin (m + 1))) (a1 : Fin (m + 1) → R)
    (s2 : Finset (PairIndex m)) (a2 : PairIndex m → R) (u : Fin (m + 1) → R) : R :=
  a0 + linearValue s1 a1 u + rowValue s2 a2 u

/-- The three kernels are kept separate; no cross-degree exclusion is needed. -/
noncomputable def product (w : Fin (m + 1) → ℕ) (u : Fin (m + 1) → R)
    (a0 : Fin r → R) (s1 : Fin r → Finset (Fin (m + 1)))
    (a1 : Fin r → Fin (m + 1) → R) (s2 : Fin r → Finset (PairIndex m))
    (a2 : Fin r → PairIndex m → R) (E : Fin r → ℕ) : R[X] :=
  encoded w u ^ 2 * combined w s2 a2 E +
    encoded w u * linearCombined w s1 a1 E + constantCombined a0 E

theorem coeff_product (w : Fin (m + 1) → ℕ) (hw : Function.Injective w)
    (u : Fin (m + 1) → R) (a0 : Fin r → R)
    (s1 : Fin r → Finset (Fin (m + 1))) (a1 : Fin r → Fin (m + 1) → R)
    (s2 : Fin r → Finset (PairIndex m)) (a2 : Fin r → PairIndex m → R)
    (E : Fin r → ℕ) (hE : Function.Injective E)
    (hE1 : ∀ k i, i ∈ s1 k → w i ≤ E k)
    (hx1 : ∀ k l, k ≠ l → ∀ i ∈ s1 k, ∀ j, w j + (E k - w i) ≠ E l)
    (hE2 : ∀ k p, p ∈ s2 k → pairWeight w p ≤ E k)
    (hi2 : ∀ k p, p ∈ s2 k → Isolated w p)
    (hx2 : ∀ k l, k ≠ l → ∀ p ∈ s2 k, ∀ i j,
      w i + w j + (E k - pairWeight w p) ≠ E l) (l : Fin r) :
    (product w u a0 s1 a1 s2 a2 E).coeff (E l) =
      2 * value (a0 l) (s1 l) (a1 l) (s2 l) (a2 l) u := by
  rw [product, coeff_add, coeff_add,
    coeff_square_mul_combined w s2 a2 u E hE2 hi2 hx2 l,
    coeff_mul_linearCombined w hw s1 a1 u E hE1 hx1 l,
    coeff_constantCombined a0 E hE l, value]
  ring

end DiophantineConsistency.DegreeSeparatedCoding
