import Diophantine.Paper1982.ShortDefs

/-!
# The enlarged base in Jones 1982, §5

The base in (D2) dominates the digit and exponent bounds and is a power
of two whenever `b` and `z` are. The geometric equation determines the
shorter mask exactly once the intended exponential equation is retained.
-/

namespace Jones1982

/-- The basic size consequences of (D2). -/
theorem shortBase_bounds {ν z b : ℕ} (hz : 2 ≤ z) (hb : 1 ≤ b) :
    b < shortBase ν z b ∧ 4 * z < shortBase ν z b ∧
      3 * L4 ν ≤ shortBase ν z b := by
  have hL : 0 < L4 ν := by positivity
  have hb4 : 1 ≤ b ^ 4 := Nat.one_le_pow _ _ hb
  have hbb4 : b ≤ b ^ 4 := Nat.le_self_pow (by norm_num) b
  have hZ : 1 ≤ (2 * z) ^ (L4 ν + 1) := Nat.one_le_pow _ _ (by omega)
  have hZsq : (2 * z) ^ 2 ≤ (2 * z) ^ (L4 ν + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hbase : 2 * (2 * z) ^ (L4 ν + 1) ≤ shortBase ν z b := by
    unfold shortBase
    nlinarith
  refine ⟨?_, by nlinarith, ?_⟩
  · unfold shortBase
    nlinarith
  · have hLpow : L4 ν < 2 ^ (L4 ν) := Nat.lt_two_pow_self
    have hpow : 2 ^ (L4 ν) ≤ (2 * z) ^ (L4 ν) := Nat.pow_le_pow_left (by omega) _
    have hZeq : (2 * z) ^ (L4 ν + 1) = (2 * z) ^ (L4 ν) * (2 * z) := pow_succ _ _
    nlinarith

/-- (D2) preserves the power-of-two requirement, with its exponent explicit. -/
theorem shortBase_pow_two {ν z b s w : ℕ} (hz : z = 2 ^ s) (hb : b = 2 ^ w) :
    shortBase ν z b = 2 ^ (1 + w * 4 + (s + 1) * (L4 ν + 1)) := by
  unfold shortBase
  rw [hz, hb, show 2 * 2 ^ s = 2 ^ (s + 1) by rw [pow_succ]; ring,
    ← pow_mul, ← pow_mul]
  rw [show 2 * 2 ^ (w * 4) = 2 ^ (1 + w * 4) by rw [pow_add, pow_one]]
  rw [← pow_add]

/-- The coefficient encoding `y` lies below the new base. -/
theorem Index.y_lt_shortBase {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ}
    {z u y b : ℕ} (hI : Index ν P z u y) (hb : 1 ≤ b) : y < shortBase ν z b := by
  have hy := hI.y_lt
  have hb4 : 1 ≤ b ^ 4 := Nat.one_le_pow _ _ hb
  have hZ : 0 < (2 * z) ^ (L4 ν + 1) := by have := hI.two_le; positivity
  unfold shortBase
  nlinarith

/-- The intended power equation and (D7) determine the shortened geometric sum. -/
theorem ShortEqs.lam_eq {ν x z u y b B c e g l m Q t lam ε : ℕ}
    (hB : 2 ≤ B) (h : ShortEqs ν x z u y b B c e g l m Q t lam ε) :
    lam = shortLam ν B := by
  apply geom_of_eq hB
  have hmul : lam ≤ lam * B := Nat.le_mul_of_pos_right _ (by omega)
  have hD7 := h.D7
  rw [Nat.mul_sub, mul_one, h.power] at hD7
  omega

/-- The shortening still gives a nonempty geometric mask. -/
theorem ShortEqs.lam_pos {ν x z u y b B c e g l m Q t lam ε : ℕ}
    (hB : 2 ≤ B) (h : ShortEqs ν x z u y b B c e g l m Q t lam ε) : 0 < lam := by
  have hQ : B ≤ Q := by rw [h.power]; exact Nat.le_self_pow (by positivity) B
  have hD7 := h.D7
  by_contra hzero
  have : lam = 0 := by omega
  simp only [this, zero_mul, add_zero] at hD7
  omega

end Jones1982
