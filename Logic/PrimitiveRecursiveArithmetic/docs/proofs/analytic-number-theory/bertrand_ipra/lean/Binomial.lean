import Std

/-!
Elementary estimates on Pascal rows, using only Lean's standard library.
All coefficients and sums are naturals. The public results are
`central_lower` and `odd_middle_upper`.
-/

namespace Bertrand.Binomial

def choose : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => choose n k + choose n (k + 1)

@[simp] theorem choose_zero (n : Nat) : choose n 0 = 1 := by
  cases n <;> rfl

theorem choose_vanish {n k : Nat} (hk : n < k) : choose n k = 0 := by
  induction n generalizing k with
  | zero => cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih => cases k with
    | zero => omega
    | succ k => rw [choose, ih (k := k) (by omega), ih (k := k+1) (by omega)]

@[simp] theorem choose_diag (n : Nat) : choose n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [choose, ih, choose_vanish (Nat.lt_succ_self n)]

theorem mirror (n k : Nat) (hk : k ≤ n) : choose n k = choose n (n - k) := by
  induction n generalizing k with
  | zero => simp [show k = 0 by omega]
  | succ n ih => cases k with
    | zero => simp
    | succ k =>
      by_cases he : k = n
      · subst k
        simp
      · have hks : k+1 ≤ n := by omega
        have hd : n+1-(k+1) = (n-(k+1))+1 := by omega
        rw [hd, choose, choose, ← ih (k+1) hks]
        have hs : n-(k+1)+1 = n-k := by omega
        rw [hs, ← ih k (by omega), Nat.add_comm]

theorem rising (n k : Nat) (hk : 2*k+1 ≤ n) :
    choose n k ≤ choose n (k+1) := by
  induction n generalizing k with
  | zero => omega
  | succ n ih => cases k with
    | zero => simp [choose]
    | succ j =>
      by_cases h : 2*(j+1)+1 ≤ n
      · have h₁ := ih j (by omega)
        have h₂ := ih (j+1) h
        simp only [choose]
        omega
      · have h₁ := mirror n j (by omega)
        have h₂ : n-j = j+1+1 := by omega
        rw [h₂] at h₁
        simp only [choose]
        omega

theorem rising_interval (n a b : Nat) (hab : a ≤ b) (hb : 2*b ≤ n+1) :
    choose n a ≤ choose n b := by
  induction b with
  | zero => simp [show a=0 by omega]
  | succ b ih =>
    by_cases he : a=b+1
    · simp [he]
    · exact Nat.le_trans (ih (by omega) (by omega)) (rising n b (by omega))

theorem even_max (n k : Nat) (hk : k ≤ 2*n) :
    choose (2*n) k ≤ choose (2*n) n := by
  by_cases h : k ≤ n
  · exact rising_interval _ _ _ h (by omega)
  · rw [mirror (2*n) k hk]
    exact rising_interval _ _ _ (by omega) (by omega)

/-- Sum over indices strictly less than the second argument. -/
def partialSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => partialSum f k + f k

theorem pascal_partialSum (n k : Nat) :
    partialSum (choose (n+1)) (k+1) = partialSum (choose n) (k+1) + partialSum (choose n) k := by
  induction k with
  | zero => simp [partialSum]
  | succ k ih =>
    change partialSum (choose (n+1)) (k+1) + choose (n+1) (k+1) =
      (partialSum (choose n) (k+1) + choose n (k+1)) + (partialSum (choose n) k + choose n k)
    rw [ih, choose]
    omega

theorem row_sum (n : Nat) : partialSum (choose n) (n+1) = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pascal_partialSum]
    change (partialSum (choose n) (n+1) + choose n (n+1)) + partialSum (choose n) (n+1) = _
    rw [choose_vanish (Nat.lt_succ_self n), ih, Nat.pow_succ]
    omega

theorem partialSum_upper (f : Nat → Nat) (k m : Nat) (h : ∀ j < k, f j ≤ m) :
    partialSum f k ≤ k*m := by
  induction k with
  | zero => simp [partialSum]
  | succ k ih =>
    have h₁ := ih (fun j hj => h j (by omega))
    have h₂ := h k (by omega)
    rw [partialSum, Nat.succ_mul]
    omega

theorem central_lower (n : Nat) : 4^n ≤ (2*n+1)*choose (2*n) n := by
  have h := partialSum_upper (choose (2*n)) (2*n+1) (choose (2*n) n)
    (fun j hj => even_max n j (by omega))
  rw [row_sum, Nat.pow_mul] at h
  exact h

theorem partialSum_mono (f : Nat → Nat) {a b : Nat} (h : a ≤ b) :
    partialSum f a ≤ partialSum f b := by
  induction b with
  | zero => simp [show a=0 by omega]
  | succ b ih =>
    by_cases he : a=b+1
    · simp [he]
    · have hx := ih (by omega)
      rw [partialSum]
      omega

theorem odd_middle_upper (n : Nat) : choose (2*n+1) n ≤ 4^n := by
  cases n with
  | zero => decide
  | succ k =>
    let m := 2*(k+1)
    change choose (m+1) (k+1) ≤ 4^(k+1)
    have hp : partialSum (choose m) (k+2) ≤ partialSum (choose m) (m+1) :=
      partialSum_mono _ (by dsimp [m]; omega)
    rw [row_sum] at hp
    change partialSum (choose m) k + choose m k + choose m (k+1) ≤ 2^m at hp
    rw [choose]
    have he : 2^m = 4^(k+1) := by dsimp [m]; rw [Nat.pow_mul]
    omega

/-- A factorial for connecting Pascal coefficients to prime divisibility. -/
def fac : Nat → Nat
  | 0 => 1
  | k+1 => (k+1)*fac k

@[simp] theorem fac_pos (n : Nat) : 0 < fac n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (by omega) ih

theorem factorial_choose (a b : Nat) :
    choose (a+b) a * (fac a * fac b) = fac (a+b) := by
  induction a generalizing b with
  | zero => simp [fac]
  | succ a ih =>
    induction b with
    | zero => simp [fac]
    | succ b ihb =>
      let t := a+b+1
      have ha : choose t a * (fac a * fac (b+1)) = fac t := by
        simpa [t, Nat.add_assoc] using ih (b+1)
      have hb : choose t (a+1) * (fac (a+1) * fac b) = fac t := by
        simpa [t, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ihb
      have ht : a+1+(b+1) = t+1 := by dsimp [t]; omega
      rw [ht, choose, Nat.add_mul]
      calc
        _ = (a+1)*(choose t a * (fac a * fac (b+1))) +
            (b+1)*(choose t (a+1) * (fac (a+1) * fac b)) := by
              simp [fac, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ = (a+1+(b+1))*fac t := by rw [ha, hb, ← Nat.add_mul]
        _ = fac (t+1) := by rw [ht]; rfl

theorem choose_pos (a b : Nat) : 0 < choose (a+b) a := by
  have hp := fac_pos (a+b)
  rw [← factorial_choose a b] at hp
  by_cases hz : choose (a+b) a = 0
  · simp [hz] at hp
  · omega

end Bertrand.Binomial
