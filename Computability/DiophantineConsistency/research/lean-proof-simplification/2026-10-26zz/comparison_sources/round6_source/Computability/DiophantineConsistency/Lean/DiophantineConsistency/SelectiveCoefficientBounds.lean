import DiophantineConsistency.SelectiveCarry

/-!
# Coefficient magnitude bounds for selectively encoded quadratics

The bound depends on the magnitude of one kernel coefficient and the square
of the coordinate one-norm. It incurs no row-count factor and does not
require unused pair sums to be distinct.
-/

namespace DiophantineConsistency.SelectiveCoefficientBounds

open Polynomial Finset
open SelectiveQuadraticCoding
open scoped BigOperators

/-- The same isolation/exclusion certificate also prevents kernel terms from
colliding. Thus a coefficient bound is not multiplied by the number of rows. -/
theorem kernel_exponents_injective {m r : ℕ} (w : Fin (m + 1) → ℕ)
    (s : Fin r → Finset (SidonPositions.PairIndex m)) (E : Fin r → ℕ)
    (hE : ∀ k p, p ∈ s k → pairWeight w p ≤ E k)
    (hi : ∀ k p, p ∈ s k → Isolated w p)
    (hx : ∀ k l, k ≠ l → ∀ p ∈ s k, ∀ i j,
      w i + w j + (E k - pairWeight w p) ≠ E l)
    {k l : Fin r} {p q : SidonPositions.PairIndex m} (hp : p ∈ s k) (hq : q ∈ s l)
    (he : E k - pairWeight w p = E l - pairWeight w q) : k = l ∧ p = q := by
  have hkl : k = l := by
    by_contra hkl
    have hno := hx k l hkl p hp q.val.1 q.val.2
    have hqE := hE l q hq
    apply hno
    dsimp only [pairWeight] at *
    omega
  subst l
  refine ⟨rfl, ?_⟩
  have hpE := hE k p hp
  have hqE := hE k q hq
  have hweight : w q.val.1 + w q.val.2 = pairWeight w p := by
    change pairWeight w q = pairWeight w p
    omega
  rcases (hi k p hp q.val.1 q.val.2).mp hweight with h | h
  · exact Subtype.ext (Prod.ext h.1.symm h.2.symm)
  · have hle : p.val.2 ≤ p.val.1 := by simpa only [h.1, h.2] using q.property
    have hpq := le_antisymm p.property hle
    exact Subtype.ext (Prod.ext (hpq.trans h.1.symm) (hpq.symm.trans h.2.symm))

/-- An injectively placed kernel entry retains its exact coefficient. -/
theorem coeff_combined_at_entry {m r : ℕ} (w : Fin (m + 1) → ℕ)
    (s : Fin r → Finset (SidonPositions.PairIndex m))
    (a : Fin r → SidonPositions.PairIndex m → ℤ) (E : Fin r → ℕ)
    (hinj : ∀ k l p q, p ∈ s k → q ∈ s l →
      E k - pairWeight w p = E l - pairWeight w q → k = l ∧ p = q)
    (k : Fin r) (p : SidonPositions.PairIndex m) (hp : p ∈ s k) :
    (combined w s a E).coeff (E k - pairWeight w p) = QuadraticCoding.correction p * a k p := by
  classical
  simp only [combined, complementary, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single p]
    · simp
    · intro q hq hqp
      apply if_neg
      intro hqE
      exact hqp ((hinj k k q p hq hp hqE).2)
    · exact fun h => False.elim (h hp)
  · intro l _ hlk
    apply Finset.sum_eq_zero
    intro q hq
    apply if_neg
    intro hqE
    exact hlk ((hinj l k q p hq hp hqE).1)
  · exact fun h => False.elim (h (mem_univ k))

/-- Every kernel coefficient is either zero or one original weighted coefficient. -/
theorem abs_coeff_combined_le {m r : ℕ} (w : Fin (m + 1) → ℕ)
    (s : Fin r → Finset (SidonPositions.PairIndex m))
    (a : Fin r → SidonPositions.PairIndex m → ℤ) (E : Fin r → ℕ)
    (H : ℤ) (hH : 0 ≤ H)
    (hc : ∀ k p, p ∈ s k → |QuadraticCoding.correction p * a k p| ≤ H)
    (hinj : ∀ k l p q, p ∈ s k → q ∈ s l →
      E k - pairWeight w p = E l - pairWeight w q → k = l ∧ p = q)
    (n : ℕ) : |(combined w s a E).coeff n| ≤ H := by
  classical
  simp only [combined, complementary, finsetSum_coeff, coeff_monomial]
  by_cases hex : ∃ k p, p ∈ s k ∧ E k - pairWeight w p = n
  · obtain ⟨k, p, hp, he⟩ := hex
    rw [Finset.sum_eq_single k]
    · rw [Finset.sum_eq_single p]
      · simpa [he] using hc k p hp
      · intro q hq hqp
        apply if_neg
        intro hqE
        exact hqp ((hinj k k q p hq hp (hqE.trans he.symm)).2)
      · exact fun h => False.elim (h hp)
    · intro l _ hlk
      apply Finset.sum_eq_zero
      intro q hq
      apply if_neg
      intro hqE
      exact hlk ((hinj l k q p hq hp (hqE.trans he.symm)).1)
    · exact fun h => False.elim (h (mem_univ k))
  · have hz : (∑ k, ∑ p ∈ s k,
        if E k - pairWeight w p = n then QuadraticCoding.correction p * a k p else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      apply Finset.sum_eq_zero
      intro p hp
      apply if_neg
      intro he
      exact hex ⟨k, p, hp, he⟩
    rw [hz, abs_zero]
    exact hH

theorem abs_coeff_monomial_mul_le (p : ℤ[X]) (H : ℤ) (hH : 0 ≤ H)
    (hp : ∀ i, |p.coeff i| ≤ H) (e n : ℕ) (c : ℤ) :
    |(monomial e c * p).coeff n| ≤ |c| * H := by
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs with he
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hp _) (abs_nonneg _)
  · simp
    positivity

/-- A uniform bound on every coefficient of the product, including nontarget cells. -/
theorem abs_coeff_square_mul_le {m : ℕ} (w : Fin (m + 1) → ℕ)
    (u : Fin (m + 1) → ℤ) (p : ℤ[X]) (H : ℤ) (hH : 0 ≤ H)
    (hp : ∀ i, |p.coeff i| ≤ H) (n : ℕ) :
    |(encoded w u ^ 2 * p).coeff n| ≤ H * (∑ i, |u i|) ^ 2 := by
  classical
  rw [encoded_square]
  simp only [Finset.sum_mul, finsetSum_coeff]
  calc
    |∑ i, ∑ j, (monomial (w i + w j) (u i * u j) * p).coeff n| ≤
        ∑ i, |∑ j, (monomial (w i + w j) (u i * u j) * p).coeff n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |(monomial (w i + w j) (u i * u j) * p).coeff n| := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |u i| * |u j| * H := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [abs_mul] using abs_coeff_monomial_mul_le p H hH hp
        (w i + w j) n (u i * u j)
    _ = H * (∑ i, |u i|) ^ 2 := by
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The concrete `M(1+sum inputs)^2` bound with a dummy coordinate equal to one. -/
theorem abs_coeff_padded_square_mul_le {m : ℕ} (w : Fin (m + 1) → ℕ)
    (u : Fin m → ℕ) (p : ℤ[X]) (H : ℤ) (hH : 0 ≤ H)
    (hp : ∀ i, |p.coeff i| ≤ H) (n : ℕ) :
    |(encoded w (Fin.cases 1 (fun i => (u i : ℤ))) ^ 2 * p).coeff n| ≤
      H * (1 + ∑ i, (u i : ℤ)) ^ 2 := by
  have h := abs_coeff_square_mul_le w (Fin.cases 1 (fun i => (u i : ℤ))) p H hH hp n
  simpa only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
    abs_one, abs_of_nonneg (Int.natCast_nonneg _)] using h

/-- A dimension-dependent scale suffices for any number of source inputs.
The lower-bound form permits rounding the scale up to a power of two. -/
theorem half_base_bound {m : ℕ} (w : Fin (m + 1) → ℕ) (u : Fin m → ℕ) (p : ℤ[X])
    {H : ℤ} (hH : 0 < H) (hp : ∀ i, |p.coeff i| ≤ H)
    {b t : ℕ} (hb : 0 < b) (ht : 1 ≤ t) (hu : ∀ i, u i < b)
    (hbase : 4 * ((m : ℤ) + 1) ^ 2 * H * (b : ℤ) ^ 2 ≤ (2 : ℤ) ^ t) (n : ℕ) :
    |(encoded w (Fin.cases 1 (fun i => (u i : ℤ))) ^ 2 * p).coeff n| <
      2 ^ (t - 1) := by
  have hsum : (∑ i, (u i : ℤ)) ≤ (m : ℤ) * b := by
    calc
      (∑ i, (u i : ℤ)) ≤ ∑ _i : Fin m, (b : ℤ) := by
        apply Finset.sum_le_sum
        intro i _
        exact_mod_cast (hu i).le
      _ = _ := by simp
  have hbZ : 1 ≤ (b : ℤ) := by exact_mod_cast hb
  have hs0 : 0 ≤ 1 + ∑ i, (u i : ℤ) :=
    add_nonneg (by decide) (Finset.sum_nonneg (fun i _ => Int.natCast_nonneg (u i)))
  have hs : 1 + (∑ i, (u i : ℤ)) ≤ ((m : ℤ) + 1) * b := by
    calc
      _ ≤ (b : ℤ) + (m : ℤ) * b := add_le_add hbZ hsum
      _ = _ := by ring
  have hsq := pow_le_pow_left₀ hs0 hs 2
  have hc := (abs_coeff_padded_square_mul_le w u p H hH.le hp n).trans
    (mul_le_mul_of_nonneg_left hsq hH.le)
  have hscale : 4 * (H * (((m : ℤ) + 1) * b) ^ 2) ≤ (2 : ℤ) ^ t := by
    calc
      _ = 4 * ((m : ℤ) + 1) ^ 2 * H * (b : ℤ) ^ 2 := by ring
      _ ≤ _ := hbase
  have hpositive : 0 < H * (((m : ℤ) + 1) * b) ^ 2 := by positivity
  have hpow : (2 : ℤ) ^ t = 2 * 2 ^ (t - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow] at hscale
  linarith

/-- The paper's scale `B=4096 H b^2` gives the strict half-base bound on all
coefficients after decoding the 31 bounded input digits. -/
theorem half_base_bound_31 (w : Fin 32 → ℕ) (u : Fin 31 → ℕ) (p : ℤ[X])
    {H : ℤ} (hH : 0 < H) (hp : ∀ i, |p.coeff i| ≤ H)
    {b t : ℕ} (hb : 0 < b) (ht : 1 ≤ t) (hu : ∀ i, u i < b)
    (hbase : (2 : ℤ) ^ t = 4096 * H * (b : ℤ) ^ 2) (n : ℕ) :
    |(encoded w (Fin.cases 1 (fun i => (u i : ℤ))) ^ 2 * p).coeff n| <
      2 ^ (t - 1) := by
  exact half_base_bound w u p hH hp hb ht hu (by norm_num [hbase]) n

end DiophantineConsistency.SelectiveCoefficientBounds
