import Diophantine.Paper1982.ShortBase

/-!
# Eventual satisfaction of (D8) in Jones 1982, §5

For any fixed digits, the enlarged base eventually satisfies (D8).
No polynomial solution hypothesis is needed for this size assertion.
The proof uses a polynomial whose coefficient at `L = 5^(ν+1)` is positive:
the two additional terms have degree at most `1 + 4*5^ν < L` when `ν ≥ 1`.
An elementary coefficient-sum bound supplies a cutoff, without asymptotics.
-/

namespace Jones1982

open Polynomial Finset

/-- A positive coefficient at a positive degree bounding all other degrees
forces an integer polynomial to be positive at every sufficiently large
natural number. The cutoff is one plus the sum of the lower absolute coefficients. -/
theorem exists_eval_pos_cutoff (p : ℤ[X]) {n : ℕ} (hn : 0 < n)
    (hdeg : p.natDegree ≤ n) (hc : 0 < p.coeff n) :
    ∃ cutoff : ℕ, ∀ B : ℕ, cutoff ≤ B → 0 < p.eval (B : ℤ) := by
  let S : ℤ := ∑ i ∈ range n, |p.coeff i|
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨S.toNat + 1, ?_⟩
  intro B hB
  have hB1 : 1 ≤ B := by omega
  have hB0 : (0 : ℤ) < B := by exact_mod_cast hB1
  have hSB : S < (B : ℤ) := by
    have hSn := Int.toNat_of_nonneg hS
    have hB' : (S.toNat : ℤ) + 1 ≤ B := by exact_mod_cast hB
    omega
  have hsum : |∑ i ∈ range n, p.coeff i * (B : ℤ) ^ i| ≤ S * (B : ℤ) ^ (n - 1) := by
    calc |∑ i ∈ range n, p.coeff i * (B : ℤ) ^ i|
        ≤ ∑ i ∈ range n, |p.coeff i * (B : ℤ) ^ i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range n, |p.coeff i| * (B : ℤ) ^ (n - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_nonneg (pow_nonneg hB0.le _)]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact_mod_cast (Nat.pow_le_pow_right hB1 (by have := mem_range.1 hi; omega) :
          B ^ i ≤ B ^ (n - 1))
      _ = S * (B : ℤ) ^ (n - 1) := by rw [← Finset.sum_mul]
  have hhead : (B : ℤ) ^ n ≤ p.coeff n * (B : ℤ) ^ n := by
    have hc1 : (1 : ℤ) ≤ p.coeff n := by omega
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 (pow_nonneg hB0.le n)
  have hpow : (B : ℤ) ^ n = B * (B : ℤ) ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hgap : 0 < ((B : ℤ) - S) * (B : ℤ) ^ (n - 1) :=
    mul_pos (by omega) (pow_pos hB0 _)
  have hlow := (abs_le.1 hsum).1
  rw [eval_eq_sum_range' (by omega : p.natDegree < n + 1), sum_range_succ]
  nlinarith

/-- The polynomial used to dominate (D8), replacing `b*l(B)` by `B*l(B)`. -/
noncomputable def shortMargin (ν : ℕ) (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (z : ℕ) (zs : Fin (ν + 1) → ℕ) : ℤ[X] :=
  C (2 * (z : ℤ)) * X ^ (L4 ν) - epoly ν 4 P z -
    C (2 * (z : ℤ)) * X * lpoly ν 4 -
    C (2 * (z : ℤ)) * X * cpoly ν 4 zs ^ 4

/-- The lower-degree terms in the margin vanish at exponent `L`. -/
theorem shortMargin_degree_and_coeff {ν : ℕ} (hν : 1 ≤ ν)
    (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ) (zs : Fin (ν + 1) → ℕ) :
    (shortMargin ν P z zs).natDegree ≤ L4 ν ∧
      (shortMargin ν P z zs).coeff (L4 ν) =
        2 * (z : ℤ) - (epoly ν 4 P z).coeff (L4 ν) := by
  have h5 : 5 ≤ 5 ^ ν := by
    calc 5 = 5 ^ 1 := by norm_num
      _ ≤ 5 ^ ν := Nat.pow_le_pow_right (by norm_num) hν
  have hL : L4 ν = 5 * 5 ^ ν := by rw [L4_eq, pow_succ]; ring
  have hCX : (C (2 * (z : ℤ)) * X : ℤ[X]).natDegree ≤ 1 := by
    exact (natDegree_C_mul_le _ _).trans (by simp)
  have hcpow : (cpoly ν 4 zs ^ 4).natDegree ≤ 4 * 5 ^ ν :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left _ (natDegree_cpoly_le ν 4 zs))
  have hl : (C (2 * (z : ℤ)) * X * lpoly ν 4).natDegree < L4 ν := by
    have := (natDegree_mul_le (p := C (2 * (z : ℤ)) * X) (q := lpoly ν 4)).trans
      (Nat.add_le_add hCX (natDegree_lpoly_le ν))
    omega
  have hc : (C (2 * (z : ℤ)) * X * cpoly ν 4 zs ^ 4).natDegree < L4 ν := by
    have := (natDegree_mul_le (p := C (2 * (z : ℤ)) * X) (q := cpoly ν 4 zs ^ 4)).trans
      (Nat.add_le_add hCX hcpow)
    omega
  constructor
  · unfold shortMargin
    refine (natDegree_sub_le _ _).trans (max_le ?_ hc.le)
    refine (natDegree_sub_le _ _).trans (max_le ?_ hl.le)
    exact (natDegree_sub_le _ _).trans
      (max_le (natDegree_C_mul_X_pow_le _ _) (natDegree_epoly_le ν 4 P z))
  · unfold shortMargin
    rw [coeff_sub, coeff_sub, coeff_sub, coeff_eq_zero_of_natDegree_lt hl,
      coeff_eq_zero_of_natDegree_lt hc]
    simp only [coeff_C_mul_X_pow, if_true, sub_zero]

/-- For fixed code digits, (D8) holds at every sufficiently large enlarged base.
This is a size theorem and does not assume that the digits solve `P = 0`. -/
theorem exists_short_D8_cutoff {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ}
    {z u y : ℕ} (hν : 1 ≤ ν) (hI : Index ν P z u y) (zs : Fin (ν + 1) → ℕ) :
    ∃ cutoff : ℕ, ∀ b : ℕ, cutoff ≤ b →
      let B : ℤ := shortBase ν z b
      (epoly ν 4 P z).eval B + 2 * z * b * (lpoly ν 4).eval B +
        2 * z * B * ((cpoly ν 4 zs).eval B) ^ 4 < 2 * z * B ^ (L4 ν) := by
  obtain ⟨hdeg, hcoeff⟩ := shortMargin_degree_and_coeff hν P z zs
  have hpos : 0 < (shortMargin ν P z zs).coeff (L4 ν) := by
    rw [hcoeff]
    have := (hI.coeff_epoly_bounds (L4 ν)).2
    omega
  obtain ⟨cutoff, hcutoff⟩ := exists_eval_pos_cutoff (shortMargin ν P z zs)
    (by positivity : 0 < L4 ν) hdeg hpos
  refine ⟨max cutoff 1, ?_⟩
  intro b hb
  dsimp only
  have hb1 : 1 ≤ b := by omega
  have hbB := (shortBase_bounds hI.two_le hb1 (ν := ν)).1
  have hmargin := hcutoff (shortBase ν z b) (by omega)
  have hl0 : 0 ≤ (lpoly ν 4).eval (shortBase ν z b : ℤ) := by
    rw [eval_lpoly]
    exact Finset.sum_nonneg fun i _ => pow_nonneg (by positivity) _
  have hbBZ : (b : ℤ) ≤ shortBase ν z b := by exact_mod_cast hbB.le
  have hmul : 2 * (z : ℤ) * b * (lpoly ν 4).eval (shortBase ν z b : ℤ) ≤
      2 * z * (shortBase ν z b : ℤ) * (lpoly ν 4).eval (shortBase ν z b : ℤ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbBZ (by positivity)) hl0
  simp only [shortMargin, eval_sub, eval_mul, eval_C, eval_pow, eval_X] at hmargin
  linarith

/-- The eventual inequality transferred to natural witnesses with the intended
polynomial evaluations. This is the form used to construct `ShortEqs.D8`. -/
theorem exists_short_D8_cutoff_nat {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ}
    {z u y : ℕ} (hν : 1 ≤ ν) (hI : Index ν P z u y) (zs : Fin (ν + 1) → ℕ) :
    ∃ cutoff : ℕ, ∀ b c e l : ℕ, cutoff ≤ b →
      (c : ℤ) = (cpoly ν 4 zs).eval (shortBase ν z b : ℤ) →
      (e : ℤ) = (epoly ν 4 P z).eval (shortBase ν z b : ℤ) →
      (l : ℤ) = (lpoly ν 4).eval (shortBase ν z b : ℤ) →
      e + 2 * z * b * l + 2 * z * shortBase ν z b * c ^ 4 <
        2 * z * shortBase ν z b ^ (L4 ν) := by
  obtain ⟨cutoff, hcutoff⟩ := exists_short_D8_cutoff hν hI zs
  refine ⟨cutoff, ?_⟩
  intro b c e l hb hc he hl
  have h := hcutoff b hb
  dsimp only at h
  rw [← hc, ← he, ← hl] at h
  exact_mod_cast h

/-- Arbitrarily large powers of two satisfy the size condition (D8). -/
theorem exists_short_D8_pow_two_above {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ}
    {z u y : ℕ} (hν : 1 ≤ ν) (hI : Index ν P z u y) (zs : Fin (ν + 1) → ℕ)
    (bound : ℕ) :
    ∃ w : ℕ, bound < 2 ^ w ∧
      let B : ℤ := shortBase ν z (2 ^ w)
      (epoly ν 4 P z).eval B + 2 * z * (2 ^ w : ℕ) * (lpoly ν 4).eval B +
        2 * z * B * ((cpoly ν 4 zs).eval B) ^ 4 < 2 * z * B ^ (L4 ν) := by
  obtain ⟨cutoff, hcutoff⟩ := exists_short_D8_cutoff hν hI zs
  have hpow : bound + cutoff + 1 < 2 ^ (bound + cutoff + 1) := Nat.lt_two_pow_self
  exact ⟨bound + cutoff + 1, by omega, hcutoff _ (by omega)⟩

end Jones1982
