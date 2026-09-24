import Diophantine.Paper1976.Factorial
import Diophantine.Paper1976.Lemma23

/-!
# JSWW 1976, Lemma 2.11: the factorial is definable from three exponentials

> **Lemma 2.11.** For any positive integers `k` and `f`, in order that `f = k!` it is
> necessary and sufficient that there exist nonnegative integers `j, h, n, p, q, w, z`
> such that
> (I) `q = wz + h + j`, (II) `z = f(h+j) + h`, (III) `(2k)³(2k+2)(n+1)² + 1 = □`,
> (IV) `p = (n+1)^k`, (V) `q = (p+1)^n`, (VI) `z = p^(k+1)`.
-/

namespace JSWW1976

/-- The six conditions of Lemma 2.11 (`x` is the square-root witness for (III)). -/
def Lemma211System (k f j h n p q w z x : ℕ) : Prop :=
  q = w * z + h + j ∧
  z = f * (h + j) + h ∧
  (2 * k) ^ 3 * (2 * k + 2) * (n + 1) ^ 2 + 1 = x * x ∧
  p = (n + 1) ^ k ∧
  q = (p + 1) ^ n ∧
  z = p ^ (k + 1)

/-- From condition (III) and Lemma 2.3: `(2k)^k ≤ n`. -/
theorem two_k_pow_le_of_III {k n x : ℕ} (hk : 1 ≤ k)
    (h : (2 * k) ^ 3 * (2 * k + 2) * (n + 1) ^ 2 + 1 = x * x) : (2 * k) ^ k ≤ n := by
  have h23 := lemma_2_3 (e := 2 * k) (n := n) (x := x) (by omega) h
  -- 2k - 1 + (2k)^(2k-2) ≤ n and (2k)^k ≤ 2k - 1 + (2k)^(2k-2)
  rcases Nat.lt_or_ge k 2 with h1 | h2
  · have : k = 1 := by omega
    subst this; simpa using h23
  · have : (2 * k) ^ k ≤ (2 * k) ^ (2 * k - 2) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- Lemma 2.11, sufficiency. -/
theorem lemma_2_11_of {k f j h n p q w z x : ℕ} (hk : 1 ≤ k) (hf : 1 ≤ f)
    (hs : Lemma211System k f j h n p q w z x) : f = k.factorial := by
  obtain ⟨hI, hII, hIII, hIV, hV, hVI⟩ := hs
  have hn : (2 * k) ^ k ≤ n := two_k_pow_le_of_III hk hIII
  have hp : n ^ k < p := by rw [hIV]; exact Nat.pow_lt_pow_left (by omega) (by omega)
  obtain ⟨hR0, hR1, hR2⟩ := lemma_2_10 hk hn hp
  -- z = (n+1)^k p^k and R = q % z
  have hz : (n + 1) ^ k * p ^ k = z := by rw [hVI, ← hIV]; ring
  rw [hz, ← hV, ← hVI] at hR1 hR2
  rw [← hV, ← hVI] at hR0
  set R := q % z with hR
  -- h + j = R
  have hz0 : 0 < z := by rw [hVI, hIV]; positivity
  have hhj : h + j ≤ z := by rw [hII]; nlinarith
  have hmod : q % z = (h + j) % z := by
    rw [hI, Nat.add_assoc, Nat.mul_comm, Nat.mul_add_mod]
  have hlt : h + j < z := by
    rcases Nat.lt_or_ge (h + j) z with hlt | hge
    · exact hlt
    · have : h + j = z := le_antisymm hhj hge
      rw [hmod, this, Nat.mod_self] at hR
      omega
  have hRhj : R = h + j := by rw [hR, hmod, Nat.mod_eq_of_lt hlt]
  -- f R ≤ z ≤ (f+1) R, together with k! R < z < (k!+1) R
  have hfz : f * R ≤ z := by rw [hRhj, hII]; omega
  have hzf : z ≤ (f + 1) * R := by rw [hRhj, hII]; nlinarith
  have h1 : k.factorial ≤ f := by
    have : k.factorial * R < (f + 1) * R := lt_of_lt_of_le hR1 hzf
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  have h2 : f ≤ k.factorial := by
    have : f * R < (k.factorial + 1) * R := lt_of_le_of_lt hfz hR2
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  omega

/-- Lemma 2.11, necessity. -/
theorem lemma_2_11_exists {k : ℕ} (hk : 1 ≤ k) :
    ∃ j h n p q w z x, Lemma211System k k.factorial j h n p q w z x := by
  obtain ⟨n, x, hIII, -⟩ := lemma_2_3_converse (e := 2 * k) (t := 1) (by omega) le_rfl
  have hn : (2 * k) ^ k ≤ n := two_k_pow_le_of_III hk hIII
  set p := (n + 1) ^ k with hp
  have hnp : n ^ k < p := Nat.pow_lt_pow_left (by omega) (by omega)
  set q := (p + 1) ^ n with hq
  set z := p ^ (k + 1) with hz
  obtain ⟨hR0, hR1, hR2⟩ := lemma_2_10 hk hn hnp
  have hz' : (n + 1) ^ k * p ^ k = z := by rw [hz, hp]; ring
  rw [hz'] at hR1 hR2
  set R := q % z with hR
  have hdiv : q = q / z * z + R := by rw [hR, Nat.div_add_mod' q z]
  have hA : k.factorial * R ≤ z := hR1.le
  have hB : z ≤ k.factorial * R + R := by
    have : (k.factorial + 1) * R = k.factorial * R + R := by ring
    omega
  refine ⟨R - (z - k.factorial * R), z - k.factorial * R, n, p, q, q / z, z, x, ?_, ?_, hIII, rfl, rfl, rfl⟩
  · generalize hM : k.factorial * R = M at hA hB ⊢
    omega
  · have hsum : z - k.factorial * R + (R - (z - k.factorial * R)) = R := by
      generalize hM : k.factorial * R = M at hA hB ⊢
      omega
    rw [hsum]
    generalize hM : k.factorial * R = M at hA hB ⊢
    omega

/-- Lemma 2.11 (both directions). -/
theorem lemma_2_11 {k f : ℕ} (hk : 1 ≤ k) (hf : 1 ≤ f) :
    f = k.factorial ↔ ∃ j h n p q w z x, Lemma211System k f j h n p q w z x := by
  constructor
  · rintro rfl; exact lemma_2_11_exists hk
  · rintro ⟨j, h, n, p, q, w, z, x, hs⟩; exact lemma_2_11_of hk hf hs

end JSWW1976
