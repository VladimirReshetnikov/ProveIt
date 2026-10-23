import DiophantineConsistency.NearSquareFinalizer

/-!
# The margin-first finalizer of package 52

Unconditional strict majorants first recover the positive margin from the
norm equation. Only on that positive branch is separation of the radicands
needed to reconstruct their integer roots. The offset and margin are the
literal `V₀ + V₁` and `m`, without the different `2*m-1` construction.
-/

namespace DiophantineConsistency.MarginFinalizer

open NearSquareFinalizer

/-- Outside the sum of two strict majorants, the two-square norm is positive.
This algebraic bound needs no square-root integrality assumption. -/
theorem norm_pos_of_nonpositive_scale {a b U V omega E : ℤ}
    (_ha : 0 ≤ a) (hb : 0 ≤ b) (hU : 0 < U) (hV : 0 < V)
    (haU : a < U ^ 2) (hbV : b < V ^ 2)
    (homega : omega ≤ 0) (hE : 0 < E) :
    0 < norm (E - omega * (U + V)) omega a 1 b := by
  let theta := E - omega * (U + V)
  have hbase : 0 ≤ -omega * (U + V) :=
    mul_nonneg (neg_nonneg.mpr homega) (le_of_lt (add_pos hU hV))
  have htheta : -omega * (U + V) < theta := by dsimp [theta]; nlinarith
  have htheta0 : 0 < theta := by omega
  have hsq : (-omega * (U + V)) ^ 2 < theta ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr htheta) (by omega : 0 < theta + -omega * (U + V))]
  have hrad : omega ^ 2 * (a + b) ≤ omega ^ 2 * (U ^ 2 + V ^ 2) :=
    mul_le_mul_of_nonneg_left (by omega) (sq_nonneg omega)
  have hgap : 2 * omega ^ 2 * U * V < theta ^ 2 - omega ^ 2 * (a + b) := by
    nlinarith [hsq, hrad]
  have hgap0 : 0 ≤ 2 * omega ^ 2 * U * V := by positivity
  have hgapSq : (2 * omega ^ 2 * U * V) ^ 2 <
      (theta ^ 2 - omega ^ 2 * (a + b)) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hgap)
      (by linarith : 0 < theta ^ 2 - omega ^ 2 * (a + b) + 2 * omega ^ 2 * U * V)]
  have hprod : a * b ≤ U ^ 2 * V ^ 2 :=
    mul_le_mul (le_of_lt haU) (le_of_lt hbV) hb (sq_nonneg U)
  have hprod' := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 4 * omega ^ 4)
  dsimp [NearSquareFinalizer.norm]
  change 0 < (theta ^ 2 - omega ^ 2 * (a + 1 ^ 2 * b)) ^ 2 -
    4 * omega ^ 4 * 1 ^ 2 * a * b
  nlinarith [hgapSq, hprod']

/-- Separated integer radicands reconstruct signed integer roots. -/
theorem integer_roots_of_separated_norm_zero {theta omega a b w : ℤ}
    (homega : omega ≠ 0) (hw : w ≠ 0) (hsep : a ≠ w ^ 2 * b)
    (hz : norm theta omega a w b = 0) :
    ∃ r s : ℤ, r ^ 2 = a ∧ s ^ 2 = b ∧ theta = omega * (r + w * s) := by
  have htheta : theta ≠ 0 := by
    intro ht
    rw [ht] at hz
    dsimp [NearSquareFinalizer.norm] at hz
    have he : omega ^ 4 * (a - w ^ 2 * b) ^ 2 = 0 := by
      linear_combination hz
    rcases mul_eq_zero.mp he with he | he
    · exact (pow_ne_zero 4 homega) he
    · exact hsep (sub_eq_zero.mp (eq_zero_of_pow_eq_zero he))
  have hwQ : (w : ℚ) ≠ 0 := by exact_mod_cast hw
  have hoQ : (omega : ℚ) ≠ 0 := by exact_mod_cast homega
  have htQ : (theta : ℚ) ≠ 0 := by exact_mod_cast htheta
  have hzQ : norm ((theta : ℚ) / omega) 1 a w b = 0 := by
    have h : norm (theta : ℚ) omega a w b = 0 := by
      dsimp [NearSquareFinalizer.norm] at hz ⊢
      exact_mod_cast hz
    dsimp [NearSquareFinalizer.norm] at h ⊢
    field_simp
    nlinarith [h]
  obtain ⟨r, s, hr, hs, hsum⟩ :=
    rational_roots_of_norm_zero hwQ (div_ne_zero htQ hoQ) hzQ
  have hsa : IsSquare a := Rat.isSquare_intCast_iff.mp ⟨r, by nlinarith [hr]⟩
  have hsb : IsSquare b := Rat.isSquare_intCast_iff.mp ⟨s, by nlinarith [hs]⟩
  obtain ⟨r₀, hr₀⟩ := hsa
  obtain ⟨s₀, hs₀⟩ := hsb
  have hr₀' : r₀ ^ 2 = a := by nlinarith [hr₀]
  have hs₀' : s₀ ^ 2 = b := by nlinarith [hs₀]
  have hrootsr : r = (r₀ : ℚ) ∨ r = -(r₀ : ℚ) := by
    have : r ^ 2 = (r₀ : ℚ) ^ 2 := by exact_mod_cast hr.trans (by exact_mod_cast hr₀'.symm)
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp this
  have hrootss : s = (s₀ : ℚ) ∨ s = -(s₀ : ℚ) := by
    have : s ^ 2 = (s₀ : ℚ) ^ 2 := by exact_mod_cast hs.trans (by exact_mod_cast hs₀'.symm)
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp this
  rcases hrootsr with hrsgn | hrsgn <;> rcases hrootss with hssgn | hssgn
  all_goals rw [hrsgn, hssgn] at hsum
  · refine ⟨r₀, s₀, hr₀', hs₀', ?_⟩
    exact_mod_cast ((div_eq_iff hoQ).mp hsum).trans (mul_comm _ _)
  · refine ⟨r₀, -s₀, hr₀', by simpa using hs₀', ?_⟩
    exact_mod_cast ((div_eq_iff hoQ).mp hsum).trans (mul_comm _ _)
  · refine ⟨-r₀, s₀, by simpa using hr₀', hs₀', ?_⟩
    exact_mod_cast ((div_eq_iff hoQ).mp hsum).trans (mul_comm _ _)
  · refine ⟨-r₀, -s₀, by simpa using hr₀', by simpa using hs₀', ?_⟩
    exact_mod_cast ((div_eq_iff hoQ).mp hsum).trans (mul_comm _ _)

/-- Literal package-52 finalizer with one natural witness. -/
def value (a b V₀ V₁ J Q m n : ℤ) : ℤ :=
  let omega := J * m
  let theta := J * n + Q - omega * (V₀ + V₁)
  norm theta omega a 8 b

theorem value_eq (a b V₀ V₁ J Q m n : ℤ) :
    value a b V₀ V₁ J Q m n =
      ((J * n + Q - (J * m) * (V₀ + V₁)) ^ 2 -
        (J * m) ^ 2 * (a + 64 * b)) ^ 2 - 256 * (J * m) ^ 4 * a * b := by
  dsimp [value, NearSquareFinalizer.norm]
  ring

/-- The unconditional majorants recover the strict margin before roots. -/
theorem margin_pos_of_value_zero {a b V₀ V₁ J Q m : ℤ} {n : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hV₀ : 0 < V₀) (hV₁ : 0 < V₁)
    (haV : a < V₀ ^ 2) (hbV : 64 * b < V₁ ^ 2)
    (hJ : 0 < J) (hQ : 0 < Q)
    (hz : value a b V₀ V₁ J Q m n = 0) : 0 < m := by
  by_contra hm
  have hm : m ≤ 0 := by omega
  have ho : J * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hJ) hm
  have hE : 0 < J * n + Q := by positivity
  have hp := norm_pos_of_nonpositive_scale ha (by omega : 0 ≤ 64 * b)
    hV₀ hV₁ haV hbV ho hE
  have heq : norm (J * n + Q - J * m * (V₀ + V₁)) (J * m) a 1 (64 * b) =
      value a b V₀ V₁ J Q m n := by dsimp [value, NearSquareFinalizer.norm]; ring
  rw [heq, hz] at hp
  omega

theorem conditions_of_value_zero {a b V₀ V₁ J Q m : ℤ} {n : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hV₀ : 0 < V₀) (hV₁ : 0 < V₁)
    (haV : a < V₀ ^ 2) (hbV : 64 * b < V₁ ^ 2)
    (hJ : 0 < J) (hQ : 0 < Q) (hsep : 0 < m → a < 64 * b)
    (hz : value a b V₀ V₁ J Q m n = 0) :
    IsSquare a ∧ IsSquare b ∧ J ∣ Q ∧ 0 < m := by
  have hm := margin_pos_of_value_zero ha hb hV₀ hV₁ haV hbV hJ hQ hz
  have ho : J * m ≠ 0 := ne_of_gt (mul_pos hJ hm)
  obtain ⟨r, s, hr, hs, htheta⟩ := integer_roots_of_separated_norm_zero ho
    (by norm_num : (8 : ℤ) ≠ 0) (by have := hsep hm; norm_num; omega) hz
  refine ⟨⟨r, by nlinarith [hr]⟩, ⟨s, by nlinarith [hs]⟩, ?_, hm⟩
  refine ⟨m * (V₀ + V₁ + r + 8 * s) - n, ?_⟩
  linear_combination htheta

theorem exists_value_zero_of_conditions {a b V₀ V₁ J Q m : ℤ}
    (hV₀ : 0 < V₀) (hV₁Q : Q < V₁) (hJ : 0 < J) (hQ : 0 < Q)
    (ha : IsSquare a) (hb : IsSquare b) (hdiv : J ∣ Q) (hm : 0 < m) :
    ∃ n : ℕ, value a b V₀ V₁ J Q m n = 0 := by
  obtain ⟨r, hr⟩ := ha
  obtain ⟨s, hs⟩ := hb
  obtain ⟨k, hk⟩ := hdiv
  have hk0 : 0 < k := by nlinarith [hk]
  have hkQ : k ≤ Q := by nlinarith [hk]
  let Z := V₀ + V₁ + |r| + 8 * |s|
  have hZ : Q < Z := by dsimp [Z]; have := abs_nonneg r; have := abs_nonneg s; omega
  have hZ0 : 0 ≤ Z := by omega
  have hmZ : Z ≤ m * Z := by nlinarith [mul_nonneg (show 0 ≤ m - 1 by omega) hZ0]
  have hn : 0 ≤ m * Z - k := by omega
  refine ⟨(m * Z - k).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hn]
  have hr' : |r| ^ 2 = a := by nlinarith [sq_abs r, hr]
  have hs' : |s| ^ 2 = b := by nlinarith [sq_abs s, hs]
  dsimp [value, NearSquareFinalizer.norm, Z]
  rw [hk, ← hr', ← hs']
  ring

/-- Exact one-natural-witness encoding with separation required only after
the margin is positive. -/
theorem exists_value_zero_iff {a b V₀ V₁ J Q m : ℤ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hV₀ : 0 < V₀) (hV₁ : 0 < V₁)
    (haV : a < V₀ ^ 2) (hbV : 64 * b < V₁ ^ 2)
    (hJ : 0 < J) (hQ : 0 < Q) (hV₁Q : Q < V₁)
    (hsep : 0 < m → a < 64 * b) :
    (∃ n : ℕ, value a b V₀ V₁ J Q m n = 0) ↔
      IsSquare a ∧ IsSquare b ∧ J ∣ Q ∧ 0 < m := by
  constructor
  · rintro ⟨n, hn⟩
    exact conditions_of_value_zero ha hb hV₀ hV₁ haV hbV hJ hQ hsep hn
  · rintro ⟨ha, hb, hd, hm⟩
    exact exists_value_zero_of_conditions hV₀ hV₁Q hJ hQ ha hb hd hm

end DiophantineConsistency.MarginFinalizer
