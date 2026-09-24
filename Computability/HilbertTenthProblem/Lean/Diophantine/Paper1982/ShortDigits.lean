import Diophantine.Paper1982.ShortCoding
import Diophantine.Paper1982.ShortBase

/-!
# The coefficient digit test in Jones 1982, §5

The enlarged base makes every coefficient of the shorter polynomial
strictly smaller than half the base. The shifted `2L`-digit expansion
therefore has no carries, and the third carry condition detects exactly
the vanishing of the original polynomial on the encoded tuple.
-/

namespace Jones1982

open Polynomial Finset

section

variable {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y : ℕ}

/-- The explicit half-base bound in §5, with no requirement that `b > y`. -/
theorem coeff_shortHpoly_lt (hI : Index ν P z u y) (hν : 1 ≤ ν) {b : ℕ}
    (zs : Fin (ν + 1) → ℕ) (hzs : ∀ i, zs i < b) (i : ℕ) :
    2 * |(shortHpoly ν 4 P z zs).coeff i| < (shortBase ν z b : ℤ) := by
  have h1 := abs_coeff_shortHpoly_le ν 4 P (fun k hk => hI.Pcoef_le hk) zs i
  have hb0 : 0 < b := by have := hzs 0; omega
  have hb1 : (1 : ℤ) ≤ b := by exact_mod_cast hb0
  have hsum : ∑ j, (zs j : ℤ) ≤ (ν + 1) * (b : ℤ) - (ν + 1) := by
    have : ∑ j : Fin (ν + 1), (zs j : ℤ) ≤ ∑ j : Fin (ν + 1), ((b : ℤ) - 1) :=
      Finset.sum_le_sum fun j _ => by
        have hj : (zs j : ℤ) + 1 ≤ b := by exact_mod_cast hzs j
        linarith
    simpa using this
  have h2 : 1 + ∑ j, (zs j : ℤ) < (ν + 2) * b := by
    have : (0 : ℤ) ≤ ν := by positivity
    nlinarith
  have h3 : (1 + ∑ j, (zs j : ℤ)) ^ 4 < ((ν + 2) * (b : ℤ)) ^ 4 :=
    pow_lt_pow_left₀ h2 (by positivity) (by norm_num)
  have h4 : 2 * (z : ℤ) * (ν + 2) ^ 4 < y := by exact_mod_cast hI.y_big hν
  have h5 : (y : ℤ) < (2 * z : ℤ) ^ (L4 ν + 1) := by exact_mod_cast hI.y_lt
  have hb4 : (0 : ℤ) < (b : ℤ) ^ 4 := by positivity
  have hZ : (0 : ℤ) < (2 * z : ℤ) ^ (L4 ν + 1) := by have := hI.two_le; positivity
  calc 2 * |(shortHpoly ν 4 P z zs).coeff i|
      ≤ 2 * ((z : ℤ) * (1 + ∑ j, (zs j : ℤ)) ^ 4) := by linarith
    _ ≤ 2 * ((z : ℤ) * ((ν + 2) * (b : ℤ)) ^ 4) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3.le (by positivity)) (by norm_num)
    _ = (2 * (z : ℤ) * (ν + 2) ^ 4) * (b : ℤ) ^ 4 := by ring
    _ < (y : ℤ) * (b : ℤ) ^ 4 := mul_lt_mul_of_pos_right h4 hb4
    _ < (2 * z : ℤ) ^ (L4 ν + 1) * (b : ℤ) ^ 4 := mul_lt_mul_of_pos_right h5 hb4
    _ < (shortBase ν z b : ℤ) := by unfold shortBase; push_cast; nlinarith

/-- The two shorter geometric blocks concatenate without overlap. -/
theorem shortLam_mul_one_add (B : ℤ) (L : ℕ) :
    (∑ i ∈ range L, B ^ i) * (1 + B ^ L) = ∑ i ∈ range (2 * L), B ^ i := by
  rw [show 2 * L = L + L by omega, Finset.sum_range_add, mul_add, mul_one, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_add]
  ring

/-- The exact shifted-digit expansion of the third block in (D15). -/
theorem shortS3_eq {B c e Q lam k : ℕ} (hB : B = 2 ^ k) (hk : 1 ≤ k)
    (z : ℕ) (zs : Fin (ν + 1) → ℕ)
    (he : (e : ℤ) = (epoly ν 4 P z).eval (B : ℤ))
    (hc : (c : ℤ) = (cpoly ν 4 zs).eval (B : ℤ))
    (hlam : (lam : ℤ) = ∑ i ∈ range (L4 ν), (B : ℤ) ^ i) (hQ : Q = B ^ (L4 ν)) :
    shortS3 z B c e Q lam = 2 * ∑ i ∈ range (2 * L4 ν),
      ((shortHpoly ν 4 P z zs).coeff i + 2 ^ (k - 1)) * (2 ^ k : ℤ) ^ i := by
  have hBZ : (B : ℤ) = 2 ^ k := by exact_mod_cast hB
  have hQZ : (Q : ℤ) = (B : ℤ) ^ (L4 ν) := by exact_mod_cast hQ
  have h2k : (2 : ℤ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hH := eval_eq_sum_range' (natDegree_shortHpoly_lt ν 4 P z zs) (B : ℤ)
  have hH' := eval_shortHpoly ν 4 P z zs (B : ℤ)
  rw [Finset.sum_range_succ, ← hlam, ← hQZ, ← he, ← hc] at hH'
  have hG : (lam : ℤ) * (1 + Q) = ∑ i ∈ range (2 * L4 ν), (B : ℤ) ^ i := by
    rw [hlam, hQZ]
    exact shortLam_mul_one_add _ _
  calc
    shortS3 z B c e Q lam =
        2 * (∑ i ∈ range (2 * L4 ν), (shortHpoly ν 4 P z zs).coeff i * (B : ℤ) ^ i) +
          B * (∑ i ∈ range (2 * L4 ν), (B : ℤ) ^ i) := by
            rw [← hH, ← hG, hH']
            unfold shortS3
            ring
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hBZ, h2k]
      ring

/-- The third carry test of §5 is equivalent to the original equation
for the bounded tuple encoded by `c`. -/
theorem short_tau3_iff (hI : Index ν P z u y) (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4)
    {b B c e Q lam k : ℕ} (hbase : B = shortBase ν z b) (hB : B = 2 ^ k) (hk : 1 ≤ k)
    (zs : Fin (ν + 1) → ℕ) (hzs : ∀ i, zs i < b)
    (he : (e : ℤ) = (epoly ν 4 P z).eval (B : ℤ))
    (hc : (c : ℤ) = (cpoly ν 4 zs).eval (B : ℤ))
    (hlam : (lam : ℤ) = ∑ i ∈ range (L4 ν), (B : ℤ) ^ i) (hQ : Q = B ^ (L4 ν)) :
    τ 2 (shortS3 z B c e Q lam).toNat ((B - 2) * Q) = 0 ↔
      MvPolynomial.eval (fun j => (zs j : ℤ)) P = 0 := by
  have hBZ : (B : ℤ) = 2 ^ k := by exact_mod_cast hB
  have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  have h2kZ : (2 : ℤ) ^ k = 2 * 2 ^ (k - 1) := by exact_mod_cast h2k
  have hbound : ∀ i < 2 * L4 ν, |(shortHpoly ν 4 P z zs).coeff i| < 2 ^ (k - 1) := by
    intro i _
    have h := coeff_shortHpoly_lt hI hν zs hzs i
    rw [← hbase, hBZ, h2kZ] at h
    linarith
  have hL : L4 ν < 2 * L4 ν := by
    have : 0 < L4 ν := by positivity
    omega
  have hT : (B - 2) * Q = 2 * ((2 ^ (k - 1) - 1) * (2 ^ k) ^ (L4 ν)) := by
    rw [hQ, hB]
    have : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
    rw [show 2 ^ k - 2 = 2 * (2 ^ (k - 1) - 1) by omega]
    ring
  rw [shortS3_eq hB hk z zs he hc hlam hQ, hT,
    tau_shifted_iff hk hL _ hbound, coeff_shortHpoly_Lexp ν 4 P hP z zs]
  norm_num

end

end Jones1982
