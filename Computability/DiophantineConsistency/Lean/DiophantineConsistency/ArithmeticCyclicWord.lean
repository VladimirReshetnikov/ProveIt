import DiophantineConsistency.ArithmeticWindowDigits
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Internal cyclic word identities modulo `M = 2^{wn}-1`, in every model of IΣ1.
Words are numbers below `2^{wn}`; their radix-`2^w` digits are the coefficients.
Cyclic rotation by an arbitrary internal shift is the explicit number
`rot w n X e`, congruent to `2^{we}·X` modulo `M`, whose digit `k` is the digit
`k-e (mod n)` of `X`. Finite (standard-length) weighted sums of such
congruences are added termwise. No represented iterated sum is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticCyclicWord
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Cyclic indices -/

/-- The cyclic index `k - e (mod n)`. -/
noncomputable def cyc (n k e : V) : V := (k + n - e % n) % n

instance cyc_definable : 𝚺₀-Function₃ (cyc : V → V → V → V) := by
  unfold cyc
  definability

theorem cyc_lt {n : V} (hn : 0 < n) (k e : V) : cyc n k e < n := mod_lt _ hn

theorem mod_mod_self (e n : V) (hn : 0 < n) : e % n % n = e % n :=
  mod_eq_self_of_lt (mod_lt e hn)

theorem cyc_mod (n k e : V) (hn : 0 < n) : cyc n k (e % n) = cyc n k e := by
  simp only [cyc, mod_mod_self e n hn]

theorem cyc_of_le {n k e : V} (hk : k < n) (he : e < n) (hek : e ≤ k) : cyc n k e = k - e := by
  unfold cyc
  rw [mod_eq_self_of_lt he]
  have h1 : k + n - e = (k - e) + n := (tsub_add_eq_add_tsub hek).symm
  have hn : 0 < n := lt_of_le_of_lt (Arithmetic.zero_le k) hk
  rw [h1, mod_add_remove_right hn, mod_eq_self_of_lt (lt_of_le_of_lt tsub_le_self hk)]

theorem cyc_of_lt {n k e : V} (he : e < n) (hke : k < e) : cyc n k e = n - e + k := by
  unfold cyc
  rw [mod_eq_self_of_lt he]
  have hen : e ≤ n := le_of_lt he
  have h1 : k + n - e = n - e + k := by
    rw [add_comm k n]; exact (tsub_add_eq_add_tsub hen).symm
  rw [h1]
  apply mod_eq_self_of_lt
  simpa only [tsub_add_cancel_of_le hen] using (add_lt_add_iff_left (n-e)).mpr hke

/-- The predecessor index. -/
theorem cyc_one {n k : V} (hk : k < n) :
    (k = 0 → cyc n k 1 = n - 1) ∧ (0 < k → cyc n k 1 = k - 1) := by
  have hn : 0 < n := lt_of_le_of_lt (Arithmetic.zero_le k) hk
  constructor
  · rintro rfl
    rcases lt_or_eq_of_le (pos_iff_one_le.mp hn) with h1 | h1
    · rw [cyc_of_lt h1 (by simp : (0:V) < 1), add_zero]
    · subst h1
      simp [cyc]
  · intro hk0
    have h1 : 1 < n := lt_of_le_of_lt (pos_iff_one_le.mp hk0) hk
    exact cyc_of_le hk h1 (pos_iff_one_le.mp hk0)

/-! ### Rotation -/

/-- Rotation of an `n`-digit word by `e ≤ n` positions. -/
noncomputable def rot (w n X e : V) : V :=
  (X % Exp.exp (w*(n-e))) * Exp.exp (w*e) + X / Exp.exp (w*(n-e))

private theorem exp_complement (w n e : V) (he : e ≤ n) :
    Exp.exp (w*n) = Exp.exp (w*(n-e)) * Exp.exp (w*e) := by
  rw [← exp_mul_add, tsub_add_cancel_of_le he]

theorem rot_lt (w n X e : V) (he : e ≤ n) (hX : X < Exp.exp (w*n)) :
    rot w n X e < Exp.exp (w*n) := by
  unfold rot
  set L := X % Exp.exp (w*(n-e))
  set P := Exp.exp (w*e)
  have hH : X / Exp.exp (w*(n-e)) < P := by
    apply div_lt_of_lt_mul
    rw [mul_comm, ← exp_complement w n e he]; exact hX
  have hL : L + 1 ≤ Exp.exp (w*(n-e)) := lt_iff_succ_le.mp (mod_lt _ (exp_pos _))
  calc L * P + X / Exp.exp (w*(n-e)) < L * P + P := (add_lt_add_iff_left _).mpr hH
    _ = (L + 1) * P := by ring
    _ ≤ Exp.exp (w*(n-e)) * P := mul_le_mul_of_nonneg_right hL (by simp)
    _ = Exp.exp (w*n) := (exp_complement w n e he).symm

/-- Rotation is multiplication by the radix power modulo `2^{wn}-1`. -/
theorem rot_mod (w n X e : V) (he : e ≤ n) (hM : 0 < Exp.exp (w*n) - 1) :
    (Exp.exp (w*e) * X) % (Exp.exp (w*n) - 1) = rot w n X e % (Exp.exp (w*n) - 1) := by
  have hPM : Exp.exp (w*n) = (Exp.exp (w*n) - 1) + 1 :=
    (tsub_add_cancel_of_le (one_le_exp _)).symm
  have hc := exp_complement w n e he
  have e1 : Exp.exp (w*e) * X =
      rot w n X e + X / Exp.exp (w*(n-e)) * (Exp.exp (w*n) - 1) := by
    unfold rot
    have hX := div_add_mod X (Exp.exp (w*(n-e)))
    calc
      _ = Exp.exp (w*e) * (Exp.exp (w*(n-e)) * (X / Exp.exp (w*(n-e))) +
          X % Exp.exp (w*(n-e))) := by rw [hX]
      _ = X % Exp.exp (w*(n-e)) * Exp.exp (w*e) +
          X / Exp.exp (w*(n-e)) * ((Exp.exp (w*n) - 1) + 1) := by
            rw [← hPM, hc]; ring
      _ = _ := by ring
  rw [e1, mod_add_mul _ _ hM]

/-- The digits of a rotation. -/
theorem dig_rot (w n X e k : V) (he : e < n) (hk : k < n) (hX : X < Exp.exp (w*n)) :
    dig w (rot w n X e) k = dig w X (cyc n k e) := by
  unfold rot
  have hH : X / Exp.exp (w*(n-e)) < Exp.exp (w*e) := by
    apply div_lt_of_lt_mul
    rw [mul_comm, ← exp_complement w n e (le_of_lt he)]; exact hX
  by_cases hke : k < e
  · rw [dig_mul_add_low _ _ _ _ _ hke, cyc_of_lt he hke]
    unfold dig
    rw [← Arithmetic.div_mul, ← exp_mul_add]
  · have hek : e ≤ k := not_lt.mp hke
    rw [dig_mul_add_high _ _ _ _ _ hH hek, cyc_of_le hk he hek]
    exact dig_mod w X (k-e) (n-e) (tsub_lt_tsub_right_of_le hek hk)

/-- A rotation of a word with Boolean digits has Boolean digits. -/
theorem rot_boolean (w n X e : V) (he : e < n) (hX : X < Exp.exp (w*n))
    (hb : ∀ k < n, dig w X k ≤ 1) : ∀ k < n, dig w (rot w n X e) k ≤ 1 := by
  intro k hk
  have hn : 0 < n := lt_of_le_of_lt (Arithmetic.zero_le k) hk
  rw [dig_rot w n X e k he hk hX]
  exact hb _ (cyc_lt hn k e)

/-! ### Congruences modulo `2^{wn}-1` -/

theorem exp_period (w n M : V) (hM : 0 < M) (hPM : Exp.exp (w*n) = M + 1) (t : V) :
    Exp.exp (w*(n*t)) % M = 1 % M := by
  induction t using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ t ih =>
    rw [mul_add, mul_one, exp_mul_add, mod_mul hM, ih, hPM, mod_add_remove_left hM,
      ← mod_mul hM, one_mul]

/-- Radix powers are periodic modulo `2^{wn}-1`. -/
theorem exp_mod_period (w n e X : V) (hn : 0 < n) (hM : 0 < Exp.exp (w*n) - 1) :
    (Exp.exp (w*e) * X) % (Exp.exp (w*n) - 1) =
      (Exp.exp (w*(e % n)) * X) % (Exp.exp (w*n) - 1) := by
  set M := Exp.exp (w*n) - 1
  have hPM : Exp.exp (w*n) = M + 1 := (tsub_add_cancel_of_le (one_le_exp _)).symm
  have he : e = n * (e / n) + e % n := (div_add_mod e n).symm
  conv_lhs => rw [he, exp_mul_add, mul_assoc, mod_mul hM, exp_period w n M hM hPM,
    ← mod_mul hM, one_mul]

/-- Multiplication by `2^{we}` for an arbitrary internal `e` is the rotation by `e mod n`. -/
theorem exp_mul_mod_rot (w n e X : V) (hn : 0 < n) (hM : 0 < Exp.exp (w*n) - 1) :
    (Exp.exp (w*e) * X) % (Exp.exp (w*n) - 1) =
      rot w n X (e % n) % (Exp.exp (w*n) - 1) := by
  rw [exp_mod_period w n e X hn hM]
  exact rot_mod w n X (e % n) (le_of_lt (mod_lt e hn)) hM

/-- Finite weighted sums of congruences. -/
theorem sum_mod_congr {ι : Type*} (s : Finset ι) (a f g : ι → V) (M : V) (hM : 0 < M)
    (h : ∀ i ∈ s, f i % M = g i % M) :
    (∑ i ∈ s, a i * f i) % M = (∑ i ∈ s, a i * g i) % M := by
  classical
  have hadd : ∀ x y x' y' : V, x % M = x' % M → y % M = y' % M → (x+y) % M = (x'+y') % M := by
    intro x y x' y' hx hy
    rw [mod_add hM, hx, hy, ← mod_add hM]
  have hmul : ∀ c x x' : V, x % M = x' % M → (c*x) % M = (c*x') % M := by
    intro c x x' hx
    rw [mod_mul hM, hx, ← mod_mul hM]
  revert h
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro j s hj ih h
  rw [Finset.sum_insert hj, Finset.sum_insert hj]
  exact hadd _ _ _ _ (hmul _ _ _ (h j (Finset.mem_insert_self j s)))
    (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Cyclic word identity.** A finite family of radix-power multipliers acting on a word
`X < 2^{wn}` is congruent, modulo `2^{wn}-1`, to the same combination of rotations. -/
theorem kernel_rotation_congr {ι : Type*} [Fintype ι] (w n X : V) (a e : ι → V)
    (hn : 0 < n) (hM : 0 < Exp.exp (w*n) - 1) :
    ((∑ i, a i * Exp.exp (w * e i)) * X) % (Exp.exp (w*n) - 1) =
      (∑ i, a i * rot w n X (e i % n)) % (Exp.exp (w*n) - 1) := by
  simp only [Finset.sum_mul, mul_assoc]
  exact sum_mod_congr Finset.univ a (fun i => Exp.exp (w * e i) * X)
    (fun i => rot w n X (e i % n)) _ hM fun i _ => exp_mul_mod_rot w n (e i) X hn hM

end DiophantineConsistency.ArithmeticCyclicWord
