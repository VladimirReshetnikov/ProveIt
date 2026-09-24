import Mathlib.Tactic

/-!
# A small calculus for size bounds `|a| ≤ c · Z^k · R^m`

Used for the "rather tedious estimation" `|A(y)B(y)C(y)| ≤ Z^90` of Lemma 3.5 (Jones 1978):
the unknowns `y, b, e, g, s, w` are below `Z`, the parameters `R, β, x` are at most `R`, and
`R³ ≤ Z`.  Bounds of the form `|a| ≤ c Z^k R^m` compose under `+`, `−`, `·`, squaring, and at
the end `R^m ≤ Z^⌈m/3⌉` and `c ≤ Z^e` (for `Z ≥ 30`) turn the bound into a power of `Z`.
-/

namespace Jones1978

/-- `|a| ≤ c Z^k R^m`. -/
def Bd (Z R : ℤ) (c k m : ℕ) (a : ℤ) : Prop := |a| ≤ c * Z ^ k * R ^ m

namespace Bd

variable {Z R : ℤ} {c c' k k' m m' : ℕ} {a b : ℤ}

theorem nonneg_bound (hR : 1 ≤ R) (hZ : R ≤ Z) (c k m : ℕ) : 0 ≤ (c : ℤ) * Z ^ k * R ^ m := by
  have : (1 : ℤ) ≤ Z := le_trans hR hZ
  positivity

theorem le_max_left' (hR : 1 ≤ R) (hZ : R ≤ Z) (h : Bd Z R c k m a) :
    |a| ≤ c * Z ^ max k k' * R ^ max m m' := by
  have hZ1 : (1 : ℤ) ≤ Z := le_trans hR hZ
  calc |a| ≤ c * Z ^ k * R ^ m := h
    _ ≤ c * Z ^ max k k' * R ^ max m m' := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ1 (le_max_left _ _))
          (by positivity)) (pow_le_pow_right₀ hR (le_max_left _ _)) (by positivity) (by positivity)

theorem le_max_right' (hR : 1 ≤ R) (hZ : R ≤ Z) (h : Bd Z R c' k' m' b) :
    |b| ≤ c' * Z ^ max k k' * R ^ max m m' := by
  have hZ1 : (1 : ℤ) ≤ Z := le_trans hR hZ
  calc |b| ≤ c' * Z ^ k' * R ^ m' := h
    _ ≤ c' * Z ^ max k k' * R ^ max m m' := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ1 (le_max_right _ _))
          (by positivity)) (pow_le_pow_right₀ hR (le_max_right _ _)) (by positivity) (by positivity)

theorem add (hR : 1 ≤ R) (hZ : R ≤ Z) (ha : Bd Z R c k m a) (hb : Bd Z R c' k' m' b) :
    Bd Z R (c + c') (max k k') (max m m') (a + b) := by
  unfold Bd
  calc |a + b| ≤ |a| + |b| := abs_add_le a b
    _ ≤ c * Z ^ max k k' * R ^ max m m' + c' * Z ^ max k k' * R ^ max m m' :=
        _root_.add_le_add (le_max_left' hR hZ ha) (le_max_right' hR hZ hb)
    _ = ((c + c' : ℕ) : ℤ) * Z ^ max k k' * R ^ max m m' := by push_cast; ring

theorem sub (hR : 1 ≤ R) (hZ : R ≤ Z) (ha : Bd Z R c k m a) (hb : Bd Z R c' k' m' b) :
    Bd Z R (c + c') (max k k') (max m m') (a - b) := by
  have hb' : Bd Z R c' k' m' (-b) := by unfold Bd at hb ⊢; rwa [abs_neg]
  rw [sub_eq_add_neg]
  exact add hR hZ ha hb'

theorem mul (hR : 1 ≤ R) (hZ : R ≤ Z) (ha : Bd Z R c k m a) (hb : Bd Z R c' k' m' b) :
    Bd Z R (c * c') (k + k') (m + m') (a * b) := by
  unfold Bd at ha hb ⊢
  have := nonneg_bound hR hZ c k m
  have := nonneg_bound hR hZ c' k' m'
  rw [abs_mul]
  calc |a| * |b| ≤ (c * Z ^ k * R ^ m) * (c' * Z ^ k' * R ^ m') :=
        mul_le_mul ha hb (abs_nonneg _) (by assumption)
    _ = ((c * c' : ℕ) : ℤ) * Z ^ (k + k') * R ^ (m + m') := by push_cast; ring

theorem sq (hR : 1 ≤ R) (hZ : R ≤ Z) (ha : Bd Z R c k m a) :
    Bd Z R (c * c) (k + k) (m + m) (a ^ 2) := by
  rw [pow_two]; exact mul hR hZ ha ha

theorem const {n : ℕ} (h : |a| ≤ n) : Bd Z R n 0 0 a := by
  unfold Bd; simpa using h

theorem ofZ (h : |a| ≤ Z) : Bd Z R 1 1 0 a := by
  unfold Bd; simpa using h

theorem ofR (h : |a| ≤ R) : Bd Z R 1 0 1 a := by
  unfold Bd; simpa using h

/-- `R^m ≤ Z^((m+2)/3)` when `R³ ≤ Z`. -/
theorem pow_R_le (hR : 1 ≤ R) (hR3 : R ^ 3 ≤ Z) (m : ℕ) : R ^ m ≤ Z ^ ((m + 2) / 3) := by
  have h1 : R ^ m ≤ R ^ (3 * ((m + 2) / 3)) := pow_le_pow_right₀ hR (by omega)
  have h2 : R ^ (3 * ((m + 2) / 3)) = (R ^ 3) ^ ((m + 2) / 3) := by rw [pow_mul]
  have h3 : (R ^ 3) ^ ((m + 2) / 3) ≤ Z ^ ((m + 2) / 3) :=
    pow_le_pow_left₀ (by positivity) hR3 _
  linarith

/-- The final conversion: `Bd Z R c k m a` with `c ≤ 30^e`, `k + (m+2)/3 + e ≤ N`, `30 ≤ Z`,
`R³ ≤ Z` gives `|a| ≤ Z^N`. -/
theorem to_pow (hR : 1 ≤ R) (hR3 : R ^ 3 ≤ Z) (hZ30 : 30 ≤ Z) (h : Bd Z R c k m a) (e N : ℕ)
    (hc : c ≤ 30 ^ e) (hN : k + (m + 2) / 3 + e ≤ N) : |a| ≤ Z ^ N := by
  have hZ1 : (1 : ℤ) ≤ Z := by linarith
  have hcZ : (c : ℤ) ≤ Z ^ e := by
    calc (c : ℤ) ≤ ((30 ^ e : ℕ) : ℤ) := by exact_mod_cast hc
      _ = (30 : ℤ) ^ e := by push_cast; ring
      _ ≤ Z ^ e := pow_le_pow_left₀ (by norm_num) hZ30 e
  have hRm := pow_R_le hR hR3 m
  calc |a| ≤ c * Z ^ k * R ^ m := h
    _ ≤ Z ^ e * Z ^ k * Z ^ ((m + 2) / 3) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hcZ (by positivity)) hRm (by positivity)
          (by positivity)
    _ = Z ^ (e + k + (m + 2) / 3) := by rw [pow_add, pow_add]
    _ ≤ Z ^ N := pow_le_pow_right₀ hZ1 (by omega)

end Bd

end Jones1978
