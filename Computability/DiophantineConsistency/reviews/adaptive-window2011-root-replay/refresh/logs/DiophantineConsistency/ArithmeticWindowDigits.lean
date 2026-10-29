import DiophantineConsistency.ArithmeticRepunit
import DiophantineConsistency.ArithmeticBinaryCarry

/-! Internal radix-`2^w` digits at arbitrary internal positions, in every model
of IΣ1. `dig w X k = ⌊X/2^{wk}⌋ mod 2^w`. The module supplies the remainder
recursion, the digit laws of block concatenation, the periodic digits of a
block repeated by the represented repunit, the repunit bound of a number with
Boolean digits, the transfer of `NoCarry` to digits, and the two all-ones bit
patterns `2^m-1`, `2^{m+1}-2` used by the mask tests. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticWindowDigits
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticRepunit
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Bits as quotients -/

theorem fbit_eq_div (a i : V) : fbit a i = a / Exp.exp i % 2 := by
  by_cases hi : i < ‖a‖
  · have h : bexp a i = Exp.exp i := bexp_eq_of_exp hi (exponential_exp i)
    simp [fbit, h]
  · have hle : ‖a‖ ≤ i := not_lt.mp hi
    rw [fbit_eq_zero_of_le hle]
    have ha : a < Exp.exp i :=
      lt_of_lt_of_le (lt_exp_len_self (exponential_exp ‖a‖)) (exp_monotone_le.mpr hle)
    simp [div_eq_zero_of_lt _ ha]

theorem fbit_div_exp (a i j : V) : fbit (a / Exp.exp i) j = fbit a (i+j) := by
  rw [fbit_eq_div, fbit_eq_div, ← Arithmetic.div_mul, ← exp_add]

theorem fbit_succ_eq_half (a i : V) : fbit a (1+i) = fbit (a/2) i := by
  rw [← fbit_div_exp, exp_one]

private theorem lt_one_eq_zero {x : V} (h : x < 1) : x = 0 := lt_one_iff_eq_zero.mp h

/-- A number below `2^m` whose low `m` bits vanish is zero. -/
theorem eq_zero_of_fbit (m : V) : ∀ x < Exp.exp m, (∀ i < m, fbit x i = 0) → x = 0 := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro x hx _
    exact lt_one_eq_zero (by simpa using hx)
  case succ m ih =>
    intro x hx h
    have h0 : x % 2 = 0 := by
      have := h 0 (by simp)
      simpa [fbit_eq_div] using this
    have hq : x / 2 < Exp.exp m := by
      apply div_lt_of_lt_mul
      simpa [exp_succ, mul_comm] using hx
    have hz : x / 2 = 0 := ih (x/2) hq (fun i hi => by
      rw [← fbit_succ_eq_half]
      exact h (1+i) (by rw [add_comm 1 i]; exact (add_lt_add_iff_right 1).mpr hi))
    have hd := div_add_mod x 2
    rw [hz, h0] at hd
    simpa using hd.symm

private theorem exp_split_bits (k j : V) (h : k < j) :
    Exp.exp j = Exp.exp k * 2 * Exp.exp (j - (k+1)) := by
  have hj : k + 1 + (j - (k+1)) = j := add_tsub_cancel_of_le (lt_iff_succ_le.mp h)
  conv_lhs => rw [← hj]
  rw [exp_add, exp_add, exp_one]

/-- Every bit of `2^m-1` below `m` is one. -/
theorem fbit_exp_sub_one (m i : V) (hi : i < m) : fbit (Exp.exp m - 1) i = 1 := by
  obtain ⟨e, he⟩ : ∃ e, Exp.exp i = e + 1 :=
    ⟨Exp.exp i - 1, (tsub_add_cancel_of_le (one_le_exp i)).symm⟩
  obtain ⟨g, hg⟩ : ∃ g, Exp.exp (m - (i+1)) = g + 1 :=
    ⟨Exp.exp (m - (i+1)) - 1, (tsub_add_cancel_of_le (one_le_exp _)).symm⟩
  have hm : Exp.exp m - 1 = (e+1)*(2*g+1) + e := by
    rw [exp_split_bits i m hi, he, hg]
    have : (e+1)*2*(g+1) = ((e+1)*(2*g+1) + e) + 1 := by ring
    rw [this, add_tsub_cancel_right]
  rw [fbit_eq_div, hm, ← he, div_mul_add' _ _ (by rw [he]; exact lt_add_one e)]
  rw [show 2*g+1 = g*2+1 by ring, mod_mul_add_of_lt _ _ one_lt_two]

theorem noCarry_comm (a b : V) : NoCarry a b ↔ NoCarry b a := by
  simp only [noCarry_iff]
  exact forall_congr' fun i => by rw [add_comm]

private theorem zero_of_add_one_le {a : V} (h : a + 1 ≤ 1) : a = 0 := by
  simpa using h

/-- Below `2^m`, no carry against `2^m-1` forces zero. -/
theorem noCarry_ones (m x : V) (hx : x < Exp.exp m) (h : NoCarry x (Exp.exp m - 1)) : x = 0 :=
  eq_zero_of_fbit m x hx fun i hi => by
    have := (noCarry_iff _ _).mp h i
    rw [fbit_exp_sub_one m i hi] at this
    exact zero_of_add_one_le this

/-- Below `2^{m+1}`, no carry against `2^{m+1}-2` forces a Boolean value. -/
theorem noCarry_ones_two (m x : V) (hx : x < Exp.exp (m+1))
    (h : NoCarry x (Exp.exp (m+1) - 2)) : x ≤ 1 := by
  obtain ⟨e, he⟩ : ∃ e, Exp.exp m = e + 1 :=
    ⟨Exp.exp m - 1, (tsub_add_cancel_of_le (one_le_exp m)).symm⟩
  have h2 : Exp.exp (m+1) - 2 = 2*(Exp.exp m - 1) := by
    rw [exp_succ, he, add_tsub_cancel_right, show (2:V)*(e+1) = 2*e+2 by ring,
      add_tsub_cancel_right]
  have hq : x / 2 < Exp.exp m := by
    apply div_lt_of_lt_mul
    simpa [exp_succ, mul_comm] using hx
  have hz : x / 2 = 0 := eq_zero_of_fbit m (x/2) hq fun i hi => by
    have := (noCarry_iff _ _).mp h (1+i)
    rw [h2, add_comm 1 i, fbit_mul_two_mul, fbit_exp_sub_one m i hi] at this
    rw [← fbit_succ_eq_half, add_comm 1 i]
    exact zero_of_add_one_le this
  have hd := div_add_mod x 2
  rw [hz] at hd
  rw [← hd]
  simpa using lt_two_iff_le_one.mp (mod_lt x (by simp : (0:V) < 2))

/-! ### Digits -/

/-- The radix-`2^w` digit at internal position `k`. -/
noncomputable def dig (w X k : V) : V := X / Exp.exp (w*k) % Exp.exp w

def digDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y w X k. ∃ m, ∃ p, ∃ r, ∃ q, m = w*k ∧ !expDef p m ∧ !expDef r w ∧ !divDef q X p ∧ !remDef y q r”
def digDeltaDef : 𝚫₁.Semisentence 4 := digDef.graphDelta
instance dig_defined : 𝚺₁-Function₃[V] dig via digDef := .mk fun e => by
  simp [digDef, dig]
instance dig_defined_delta : 𝚫₁-Function₃[V] dig via digDeltaDef := dig_defined.graph_delta
instance dig_definable : 𝚺₁-Function₃[V] dig := dig_defined.to_definable

theorem dig_lt (w X k : V) : dig w X k < Exp.exp w := mod_lt _ (exp_pos w)

@[simp] theorem dig_zero_index (w X : V) : dig w X 0 = X % Exp.exp w := by simp [dig]

theorem exp_mul_succ (w k : V) : Exp.exp (w*(k+1)) = Exp.exp (w*k) * Exp.exp w := by
  rw [mul_add, mul_one, exp_add]

theorem exp_mul_add (w a b : V) : Exp.exp (w*(a+b)) = Exp.exp (w*a) * Exp.exp (w*b) := by
  rw [mul_add, exp_add]

theorem exp_mul_split (w k j : V) (h : k < j) :
    Exp.exp (w*j) = Exp.exp (w*k) * Exp.exp w * Exp.exp (w*(j-(k+1))) := by
  have hj : k + 1 + (j - (k+1)) = j := add_tsub_cancel_of_le (lt_iff_succ_le.mp h)
  conv_lhs => rw [← hj]
  rw [exp_mul_add, exp_mul_succ]

/-- Remainder modulo a product. -/
theorem mod_mul_split (X P Q : V) (hP : 0 < P) (hQ : 0 < Q) :
    X % (P*Q) = X % P + (X / P % Q) * P := by
  have h1 := div_add_mod X P
  have h2 := div_add_mod (X/P) Q
  have hr : X / P % Q + 1 ≤ Q := lt_iff_succ_le.mp (mod_lt _ hQ)
  have hlt : X % P + (X / P % Q) * P < P*Q := calc
    X % P + X / P % Q * P < P + X / P % Q * P := by
        have := mod_lt X hP
        exact add_lt_add_of_lt_of_le this le_rfl
    _ = (X / P % Q + 1) * P := by ring
    _ ≤ Q * P := mul_le_mul_of_nonneg_right hr (by simp)
    _ = P * Q := mul_comm _ _
  have hX : (X / P / Q) * (P*Q) + (X % P + (X/P%Q)*P) = X := calc
    _ = P * (Q * (X / P / Q) + X / P % Q) + X % P := by ring
    _ = X := by rw [h2, h1]
  have e : X % (P*Q) = ((X / P / Q) * (P*Q) + (X % P + (X/P%Q)*P)) % (P*Q) :=
    congrArg (fun t => t % (P*Q)) hX.symm
  rw [e, mod_mul_add_of_lt _ _ hlt]

/-- The remainder recursion: one more digit. -/
theorem mod_exp_succ (w X k : V) :
    X % Exp.exp (w*(k+1)) = X % Exp.exp (w*k) + dig w X k * Exp.exp (w*k) := by
  rw [exp_mul_succ]
  exact mod_mul_split X _ _ (exp_pos _) (exp_pos _)

theorem div_exp_succ (w X k : V) :
    X / Exp.exp (w*(k+1)) = X / Exp.exp (w*k) / Exp.exp w := by
  rw [exp_mul_succ, Arithmetic.div_mul]

/-- Adding a multiple of `P·ρ·R` does not change the `P`-digit modulo `ρ`. -/
theorem div_mod_add_mul (Y Z P ρ R : V) (hP : 0 < P) (hρ : 0 < ρ) :
    (Y + Z*(P*ρ*R)) / P % ρ = Y / P % ρ := by
  have e : Y + Z*(P*ρ*R) = Y + (Z*ρ*R)*P := by ring
  rw [e, div_add_mul_self _ _ hP, show Z*ρ*R = (Z*R)*ρ by ring, mod_add_mul _ _ hρ]

/-- Digits strictly below `j` ignore multiples of `2^{wj}`. -/
theorem dig_add_mul_high (w Y Z k j : V) (h : k < j) :
    dig w (Y + Z * Exp.exp (w*j)) k = dig w Y k := by
  unfold dig
  rw [exp_mul_split w k j h]
  exact div_mod_add_mul _ _ _ _ _ (exp_pos _) (exp_pos _)

theorem dig_mul_add_low (w A B k j : V) (h : k < j) :
    dig w (A * Exp.exp (w*j) + B) k = dig w B k := by
  rw [add_comm]
  exact dig_add_mul_high w B A k j h

/-- Digits at or above `j` of a concatenation are digits of the high block. -/
theorem dig_mul_add_high (w A B j k : V) (hB : B < Exp.exp (w*j)) (h : j ≤ k) :
    dig w (A * Exp.exp (w*j) + B) k = dig w A (k - j) := by
  have hk : j + (k - j) = k := add_tsub_cancel_of_le h
  unfold dig
  conv_lhs => rw [← hk, exp_mul_add, Arithmetic.div_mul, div_mul_add _ _ hB]

theorem dig_mod (w X k n : V) (h : k < n) : dig w (X % Exp.exp (w*n)) k = dig w X k := by
  have e : X % Exp.exp (w*n) + (X / Exp.exp (w*n)) * Exp.exp (w*n) = X := by
    calc X % Exp.exp (w*n) + (X / Exp.exp (w*n)) * Exp.exp (w*n)
        = Exp.exp (w*n) * (X / Exp.exp (w*n)) + X % Exp.exp (w*n) := by ring
      _ = X := div_add_mod X _
  conv_rhs => rw [← e]
  exact (dig_add_mul_high w _ _ k n h).symm

/-- A remainder at a smaller radix power. -/
theorem mod_mod_of_le (w X j n : V) (h : j ≤ n) :
    X % Exp.exp (w*n) % Exp.exp (w*j) = X % Exp.exp (w*j) := by
  have hn : j + (n - j) = n := add_tsub_cancel_of_le h
  have hP : (0:V) < Exp.exp (w*j) := exp_pos _
  have hd := div_add_mod X (Exp.exp (w*n))
  rw [← hn, exp_mul_add] at hd ⊢
  set P := Exp.exp (w*j)
  set R := Exp.exp (w*(n-j))
  have hX : X % (P*R) + (R * (X/(P*R))) * P = X := calc
    _ = P * R * (X / (P*R)) + X % (P*R) := by ring
    _ = X := hd
  conv_rhs => rw [← hX]
  exact (mod_add_mul _ _ hP).symm

/-- `X mod 2^{wn} = X mod 2^{wj} + 2^{wj}·Z` for `j ≤ n`. -/
theorem mod_eq_mod_add (w X j n : V) (h : j ≤ n) :
    X % Exp.exp (w*n) = X % Exp.exp (w*j) + Exp.exp (w*j) * (X % Exp.exp (w*n) / Exp.exp (w*j)) := by
  have hd := div_add_mod (X % Exp.exp (w*n)) (Exp.exp (w*j))
  rw [mod_mod_of_le w X j n h] at hd
  rw [add_comm]; exact hd.symm

/-! ### Units and the repunit -/

theorem rep_succ_add (d N : V) : rep d (N+1) = rep d N + Exp.exp (d*N) := by
  induction N using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using rep_succ d 0
  case succ N ih =>
    conv_lhs => rw [rep_succ, ih]
    conv_rhs => rw [rep_succ, mul_add, mul_one, exp_add]
    ring

/-- A number whose first `k` digits are Boolean has remainder at most the unit `rep w k`. -/
theorem mod_le_rep (w X k : V) : (∀ i < k, dig w X i ≤ 1) → X % Exp.exp (w*k) ≤ rep w k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro _; simp
  case succ k ih =>
    intro h
    rw [mod_exp_succ, rep_succ_add]
    apply add_le_add (ih fun i hi => h i (lt_trans hi (lt_add_one k)))
    calc dig w X k * Exp.exp (w*k) ≤ 1 * Exp.exp (w*k) :=
          mul_le_mul_of_nonneg_right (h k (lt_add_one k)) (by simp)
      _ = Exp.exp (w*k) := one_mul _

/-- Digits of a block repeated `N` times by the represented repunit. -/
theorem dig_mul_rep (w m a : V) (ha : a < Exp.exp (w*m)) (N : V) :
    ∀ k < m*N, dig w (a * rep (w*m) N) k = dig w a (k % m) := by
  induction N using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro k hk; simp at hk
  case succ N ih =>
    intro k hk
    have e : a * rep (w*m) (N+1) = (a * rep (w*m) N) * Exp.exp (w*m) + a := by
      rw [rep_succ]; ring
    rw [e]
    by_cases hkm : k < m
    · rw [dig_mul_add_low _ _ _ _ _ hkm, mod_eq_self_of_lt hkm]
    · have hmk : m ≤ k := not_lt.mp hkm
      have hm : 0 < m :=
        pos_of_mul_pos_left (lt_of_le_of_lt (Arithmetic.zero_le k) hk) (by simp)
      rw [dig_mul_add_high _ _ _ _ _ ha hmk]
      have hk' : k - m < m*N := by
        have hkk : k - m + m = k := tsub_add_cancel_of_le hmk
        have : k - m + m < m*N + m := by rw [hkk]; simpa [mul_add] using hk
        exact (add_lt_add_iff_right _).mp this
      rw [ih (k-m) hk']
      congr 1
      conv_rhs => rw [← tsub_add_cancel_of_le hmk]
      exact (mod_add_remove_right hm).symm

/-! ### Digits around the least digit -/

theorem dig_succ_pos (w Q r k : V) (hr : r < Exp.exp w) (hk : 0 < k) :
    dig w (Q * Exp.exp w + r) k = dig w Q (k-1) := by
  simpa using dig_mul_add_high w Q r 1 k (by simpa using hr) (pos_iff_one_le.mp hk)

theorem dig_succ_zero (w Q r : V) (hr : r < Exp.exp w) :
    dig w (Q * Exp.exp w + r) 0 = r := by
  simp [mod_mul_add_of_lt _ _ hr]

/-- Replacing the low digit by a value below the radix leaves higher digits unchanged. -/
private theorem dig_replace_low (w X s : V) (hs : s < Exp.exp w) :
    dig w ((X / Exp.exp w) * Exp.exp w + s) 0 = s ∧
      ∀ k, 0 < k → dig w ((X / Exp.exp w) * Exp.exp w + s) k = dig w X k := by
  refine ⟨dig_succ_zero _ _ _ hs, fun k hk => ?_⟩
  rw [dig_succ_pos _ _ _ _ hs hk]
  conv_rhs => rw [← div_add_mod X (Exp.exp w), mul_comm (Exp.exp w) (X / Exp.exp w)]
  rw [dig_succ_pos _ _ _ _ (mod_lt X (exp_pos w)) hk]

/-- Subtracting one from a number with a nonzero least digit touches only that digit. -/
theorem dig_sub_one (w X : V) (h : 1 ≤ dig w X 0) :
    dig w (X - 1) 0 = dig w X 0 - 1 ∧ ∀ k, 0 < k → dig w (X - 1) k = dig w X k := by
  set ρ := Exp.exp w
  have hρ : 0 < ρ := exp_pos w
  set r := X % ρ
  have hr : r < ρ := mod_lt X hρ
  have h1 : 1 ≤ r := by simpa using h
  have hX1 : X - 1 = (X/ρ) * ρ + (r - 1) := by
    conv_lhs => rw [← div_add_mod X ρ, mul_comm ρ (X/ρ), add_tsub_assoc_of_le h1]
  have hr1 : r - 1 < ρ := lt_of_le_of_lt tsub_le_self hr
  rw [hX1]
  simpa only [dig_zero_index] using dig_replace_low w X (r - 1) hr1

/-- Adding one below a non-saturated least digit touches only that digit. -/
theorem dig_add_one (w X : V) (h : dig w X 0 + 1 < Exp.exp w) :
    dig w (X + 1) 0 = dig w X 0 + 1 ∧ ∀ k, 0 < k → dig w (X + 1) k = dig w X k := by
  set ρ := Exp.exp w
  set r := X % ρ
  have hr1 : r + 1 < ρ := by simpa using h
  have hX1 : X + 1 = (X/ρ) * ρ + (r + 1) := by
    nth_rewrite 1 [← div_add_mod X ρ]
    ring
  rw [hX1]
  simpa only [dig_zero_index] using dig_replace_low w X (r + 1) hr1

/-! ### Bits inside a digit -/

theorem fbit_dig (w X k r : V) (hr : r < w) : fbit (dig w X k) r = fbit X (w*k + r) := by
  rw [← fbit_div_exp, fbit_eq_div, fbit_eq_div]
  unfold dig
  set Y := X / Exp.exp (w*k)
  have e : Y % Exp.exp w + (Y / Exp.exp w) * (Exp.exp r * 2 * Exp.exp (w - (r+1))) = Y := by
    rw [← exp_split_bits r w hr, mul_comm, add_comm]; exact div_add_mod Y _
  conv_rhs => rw [← e]
  exact (div_mod_add_mul _ _ _ _ _ (exp_pos r) (by simp)).symm

theorem fbit_dig_high (w X k r : V) (hr : w ≤ r) : fbit (dig w X k) r = 0 := by
  rw [fbit_eq_div, div_eq_zero_of_lt _ (lt_of_lt_of_le (dig_lt w X k) (exp_monotone_le.mpr hr))]
  simp

/-- No carry between numbers passes to every digit. -/
theorem noCarry_dig (w X Y k : V) (h : NoCarry X Y) : NoCarry (dig w X k) (dig w Y k) := by
  rw [noCarry_iff] at h ⊢
  intro r
  by_cases hr : r < w
  · rw [fbit_dig w X k r hr, fbit_dig w Y k r hr]; exact h _
  · rw [fbit_dig_high w X k r (not_lt.mp hr), fbit_dig_high w Y k r (not_lt.mp hr)]; simp

/-- A Boolean digit is the bit at the start of its block. -/
theorem dig_eq_fbit (w X k : V) (hw : 0 < w) (h : dig w X k ≤ 1) : dig w X k = fbit X (w*k) := by
  have := fbit_dig w X k 0 hw
  rw [add_zero, fbit_eq_div] at this
  rw [← this]
  simp [mod_eq_self_of_lt (lt_two_iff_le_one.mpr h)]

end DiophantineConsistency.ArithmeticWindowDigits
