import Std

/-! Integer estimates for the strict form of Bertrand's postulate.
    All constants and comparisons are natural numbers. -/
namespace Bertrand.Bounds

/-- Integer square root, by primitive recursion on its input. -/
def root : Nat → Nat
  | 0 => 0
  | x + 1 =>
    let s := root x
    if (s + 1) * (s + 1) ≤ x + 1 then s + 1 else s

theorem root_spec (x : Nat) :
    root x * root x ≤ x ∧ x < (root x + 1) * (root x + 1) := by
  induction x with
  | zero => decide
  | succ x ih =>
    obtain ⟨lo, hi⟩ := ih
    unfold root
    dsimp only
    split <;> rename_i h
    · constructor
      · exact h
      · simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at hi ⊢
        omega
    · exact ⟨by omega, by omega⟩

/-- A fixed-ratio induction replaces real logarithms in the growth estimate. -/
theorem sixth_bound_index (j : Nat) : (j + 39)^6 ≤ 2^(j + 36) := by
  induction j with
  | zero => decide
  | succ j ih =>
    have step : 9 * ((j+1) + 39) ≤ 10 * (j+39) := by omega
    have scaled := Nat.pow_le_pow_left step 6
    rw [Nat.mul_pow, Nat.mul_pow] at scaled
    have num : 10^6 ≤ 9^6 * 2 := by decide
    have h := Nat.le_trans scaled (Nat.mul_le_mul_right ((j+39)^6) num)
    rw [Nat.mul_assoc] at h
    have growth := Nat.le_of_mul_le_mul_left h (by decide : 0 < 9^6)
    calc
      _ ≤ 2 * (j + 39)^6 := growth
      _ ≤ 2 * 2^(j+36) := Nat.mul_le_mul_left 2 ih
      _ = _ := by rw [Nat.mul_comm]; exact (Nat.pow_succ 2 (j+36)).symm

/-- The strict integer inequality obtained after cubing the gap estimate. -/
theorem cube_margin {n s : Nat} (hs : 38 ≤ s) (hlo : s*s ≤ 2*n)
    (hhi : 2*n < (s+1)*(s+1)) : (2*n+1)^(3*(s+2)) < 4^n := by
  let j := s - 38
  have he : s = j+38 := by dsimp [j]; omega
  have six : (s+1)^6 ≤ 2^(j+36) := by
    simpa only [he, Nat.add_assoc] using sixth_bound_index j
  have ex : (j+36)*(s+2) < 2*n := by
    rw [he] at hlo ⊢
    simp only [Nat.add_mul, Nat.mul_add] at hlo ⊢
    omega
  have hbase : 2*n+1 ≤ (s+1)^2 := by simpa [Nat.pow_succ] using hhi
  calc
    _ ≤ ((s+1)^2)^(3*(s+2)) := Nat.pow_le_pow_left hbase _
    _ = ((s+1)^6)^(s+2) := by rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.mul_assoc]
    _ ≤ (2^(j+36))^(s+2) := Nat.pow_le_pow_left six _
    _ = 2^((j+36)*(s+2)) := (Nat.pow_mul ..).symm
    _ < 2^(2*n) := by
      let t := (j+36)*(s+2)
      have step : 2^t < 2^(t+1) := by
        rw [Nat.pow_succ]
        have h : 0 < 2^t := Nat.pow_pos (by decide)
        omega
      exact Nat.lt_of_lt_of_le step (Nat.pow_le_pow_right (by decide) ex)
    _ = 4^n := Nat.pow_mul 2 2 n

/-- With the integer square root supplied, the gap bound contradicts the row sum. -/
theorem squeeze {n s B : Nat} (hn : 722 ≤ n)
    (hlo : s*s ≤ 2*n) (hhi : 2*n < (s+1)*(s+1))
    (lower : 4^n ≤ (2*n+1)*B)
    (gap : B ≤ (2*n)^(s+1)*4^(2*n/3)) : False := by
  have hs : 38 ≤ s := by
    by_cases h : 38 ≤ s
    · exact h
    · have a : s+1 ≤ 38 := by omega
      have b := Nat.mul_le_mul a a
      omega
  let u := 2*n+1
  let m := 2*n/3
  have src : 4^n ≤ u^(s+2)*4^m := by
    have grow := Nat.pow_le_pow_left (show 2*n ≤ u by dsimp [u]; omega) (s+1)
    calc
      _ ≤ u*B := lower
      _ ≤ u*((2*n)^(s+1)*4^m) := Nat.mul_le_mul_left _ gap
      _ ≤ u*(u^(s+1)*4^m) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ grow)
      _ = _ := by rw [← Nat.mul_assoc, Nat.mul_comm u (u^(s+1)), ← Nat.pow_succ]
  have cube := Nat.pow_le_pow_left src 3
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at cube
  have exp3 : n*3 = n + 2*n := by omega
  have big := Nat.pow_le_pow_right (by decide : 0 < 4) (Nat.div_mul_le_self (2*n) 3)
  have hc : 4^n * 4^(2*n) ≤ u^((s+2)*3) * 4^(2*n) := by
    rw [exp3, Nat.pow_add] at cube
    exact Nat.le_trans cube (Nat.mul_le_mul_left _ big)
  have bad := Nat.le_of_mul_le_mul_right hc (Nat.pow_pos (by decide : 0 < 4))
  have good := cube_margin hs hlo hhi
  rw [Nat.mul_comm 3 (s+2)] at good
  exact (Nat.not_lt_of_ge bad) good

theorem root_squeeze {n B : Nat} (hn : 722 ≤ n)
    (lower : 4^n ≤ (2*n+1)*B)
    (gap : B ≤ (2*n)^(root (2*n)+1)*4^(2*n/3)) : False := by
  obtain ⟨lo, hi⟩ := root_spec (2*n)
  exact squeeze hn lo hi lower gap

end Bertrand.Bounds
