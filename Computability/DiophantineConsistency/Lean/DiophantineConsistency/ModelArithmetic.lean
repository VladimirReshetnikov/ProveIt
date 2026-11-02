import Mathlib.Tactic.LinearCombination
import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.DiscreteOrderedRingFacts
import DiophantineConsistency.ArithmeticNegativeNorms
/-! # Integer-like structure of the ring of differences of a model of `𝗜𝚺₁`

For a model `V` of `𝗜𝚺₁`, `DiffRing V` is discrete, has division with
remainder by every positive standard `n` (so reduction modulo `n` is a ring
homomorphism to `ZMod n`), and satisfies the two Pell-norm exclusions used by
the carrier equations:

* `near_square_ne_zero`: `x² - (A²-1)y² ≠ 0` for `A ≥ 2`, `y ≠ 0`, by a new
  bounded internal descent (`near_ne`), mirroring `NearSquareNormZero`;
* `consecutive_ne_neg_one`: `x² - n(n+1)y² ≠ -1` for `n ≥ 2`, from the
  existing internal descent `ArithmeticNegativeNorms.consecutive_ne_negative`. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiophantineConsistency.ModelArithmetic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing DiscreteOrderedRingFacts

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem model_one_le (a : V) (h : 0 < a) : 1 ≤ a := pos_iff_one_le.mp h

theorem model_discrete : Discrete (DiffRing V) := fun _ hx => one_le_of_pos model_one_le hx

theorem ι_two : ι (2 : V) = (2 : DiffRing V) := by
  rw [← one_add_one_eq_two, map_add, map_one, one_add_one_eq_two]

/-- Elements of the model below a standard numeral are standard. -/
theorem exists_nat_of_lt (r : V) : ∀ n : ℕ, r < n → ∃ m : ℕ, m < n ∧ r = m
  | 0, h => absurd h (by simp)
  | n + 1, h => by
    have hle : r ≤ n := by
      have h' : ι r < ι (n : V) + 1 := by
        rw [← map_one ι, ← map_add, ι_lt_ι]; exact_mod_cast h
      have := le_of_lt_add_one model_discrete h'
      exact ι_le_ι.mp this
    rcases hle.lt_or_eq with hlt | heq
    · obtain ⟨m, hm, rfl⟩ := exists_nat_of_lt r n hlt
      exact ⟨m, by omega, rfl⟩
    · exact ⟨n, by omega, heq⟩

theorem model_residues (n : ℕ) [NeZero n] : HasResidues n (DiffRing V) := by
  have hn : (0 : V) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hV : ∀ a : V, ∃ q : V, ∃ m : ℕ, m < n ∧ a = n * q + m := by
    intro a
    obtain ⟨m, hm, hr⟩ := exists_nat_of_lt (a % (n : V)) n (mod_lt a hn)
    exact ⟨a / n, m, hm, by rw [← hr]; exact (div_add_mod a n).symm⟩
  intro x
  rcases nonneg_or_nonpos x with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · obtain ⟨q, m, hm, rfl⟩ := hV a
    exact ⟨ι q, m, hm, by simp⟩
  · obtain ⟨q, m, hm, rfl⟩ := hV a
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      exact ⟨-ι q, 0, Nat.pos_of_ne_zero (NeZero.ne n), by simp⟩
    · refine ⟨-ι q - 1, n - m, by omega, ?_⟩
      simp only [map_add, map_mul, map_natCast]
      push_cast [Nat.cast_sub hm.le]
      ring

/-- Reduction modulo four in the model's ring of differences. -/
def mod4 : DiffRing V →+* ZMod 4 := residueHom model_discrete (model_residues 4)

theorem ι_pos {a : V} (h : 0 < a) : (0 : DiffRing V) < ι a := by
  rw [← map_zero ι]; exact ι_lt_ι.mpr h

theorem two_le_ι {a : V} (h : 2 ≤ a) : (2 : DiffRing V) ≤ ι a := by
  rw [← ι_two]; exact ι_le_ι.mpr h

theorem two_le_of_ι {a : V} (h : (2 : DiffRing V) ≤ ι a) : 2 ≤ a := by
  rw [← ι_two] at h; exact ι_le_ι.mp h

/-- One step of the near-square descent. -/
theorem near_descent (A x y : V) (hA : 2 ≤ A) (hy : 0 < y) (h : x*x + y*y = A*A*y*y) :
    ∃ u v : V, 0 < v ∧ v < y ∧ u ≤ A*v ∧ u*u + v*v = A*A*v*v := by
  have hR : ι x ^ 2 + ι y ^ 2 = ι A ^ 2 * ι y ^ 2 := by
    have := congrArg (ι : V →+* DiffRing V) h
    simp only [map_add, map_mul] at this
    linear_combination this
  have ha : (2 : DiffRing V) ≤ ι A := two_le_ι hA
  have hY : 1 ≤ ι y := model_discrete _ (ι_pos hy)
  have hX : 0 ≤ ι x := ι_nonneg x
  have hY2 : 0 < ι y ^ 2 := pow_pos (by linarith) 2
  have hupper : ι x < ι A * ι y := by
    by_contra hc; push_neg at hc
    have h0 : 0 ≤ ι A * ι y := mul_nonneg (by linarith) (by linarith)
    have hsq := pow_le_pow_left₀ h0 hc 2
    have key : (ι A * ι y) ^ 2 = ι A ^ 2 * ι y ^ 2 := by ring
    linarith
  have hlower : (ι A - 1) * ι y < ι x := by
    by_contra hc; push_neg at hc
    have hsq := pow_le_pow_left₀ hX hc 2
    have key : ((ι A - 1) * ι y) ^ 2 = ι A ^ 2 * ι y ^ 2 - 2 * (ι A * ι y ^ 2) + ι y ^ 2 := by ring
    have hay : 2 * ι y ^ 2 ≤ ι A * ι y ^ 2 := mul_le_mul_of_nonneg_right ha hY2.le
    linarith
  have hY'pos : 0 < ι A * ι y - ι x := by linarith
  have hY'lt : ι A * ι y - ι x < ι y := by linarith
  have hnorm : (ι A * ι x - (ι A ^ 2 - 1) * ι y) ^ 2 + (ι A * ι y - ι x) ^ 2 =
      ι A ^ 2 * (ι A * ι y - ι x) ^ 2 := by linear_combination hR
  obtain ⟨v, hv⟩ := nonneg_iff.mp hY'pos.le
  obtain ⟨u, hu⟩ := nonneg_iff.mp (abs_nonneg (ι A * ι x - (ι A ^ 2 - 1) * ι y))
  have hnorm' : (ι u) ^ 2 + (ι v) ^ 2 = ι A ^ 2 * (ι v) ^ 2 := by
    rw [← hu, ← hv, sq_abs]; exact hnorm
  refine ⟨u, v, ?_, ?_, ?_, ?_⟩
  · exact ι_lt_ι.mp (by rw [map_zero, ← hv]; exact hY'pos)
  · exact ι_lt_ι.mp (by rw [← hv]; exact hY'lt)
  · apply ι_le_ι.mp
    rw [map_mul]
    have hu0 : 0 ≤ ι u := ι_nonneg u
    have hv0 : 0 ≤ ι v := ι_nonneg v
    by_contra hc; push_neg at hc
    have h0 : 0 ≤ ι A * ι v := mul_nonneg (by linarith) hv0
    have hsq := pow_lt_pow_left₀ hc h0 two_ne_zero
    have key : (ι A * ι v) ^ 2 = ι A ^ 2 * ι v ^ 2 := by ring
    have hv2 : 0 ≤ ι v ^ 2 := sq_nonneg _
    linarith
  · apply ι_injective
    simp only [map_add, map_mul]
    linear_combination hnorm'

/-- Bounded Δ₀ root quantification supports internal order induction. -/
theorem near_ne (A x y : V) (hA : 2 ≤ A) (hy : 0 < y) : x*x + y*y ≠ A*A*y*y := by
  have bounded (y : V) : ∀ x ≤ A*y, x*x + y*y = A*A*y*y → y = 0 := by
    induction y using ISigma1.sigma1_order_induction
    · definability
    case ind y ih =>
      intro x _ hx
      by_contra hy0
      obtain ⟨u, v, hv0, hvy, hu, hnew⟩ := near_descent A x y hA (pos_iff_ne_zero.mpr hy0) hx
      exact hv0.ne' (ih v hvy u hu hnew)
  intro h
  have hx : x ≤ A*y := by
    apply (mul_self_le_mul_self_iff (a := x) (b := A*y) _root_.zero_le _root_.zero_le).mpr
    calc x*x ≤ x*x + y*y := le_self_add
      _ = A*A*y*y := h
      _ = (A*y)*(A*y) := by ring
  exact hy.ne' (bounded y x hx h)

/-- No nontrivial zero norm for the nonsquare `A²-1`, in the ring of differences. -/
theorem near_square_ne_zero (A x y : DiffRing V) (hA : 2 ≤ A) (hy : y ≠ 0) :
    x ^ 2 - (A ^ 2 - 1) * y ^ 2 ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ := nonneg_iff.mp (show (0 : DiffRing V) ≤ A by linarith)
  obtain ⟨p, hp⟩ := nonneg_iff.mp (abs_nonneg x)
  obtain ⟨q, hq⟩ := nonneg_iff.mp (abs_nonneg y)
  have hq0 : 0 < q := ι_lt_ι.mp (by rw [map_zero, ← hq]; exact abs_pos.mpr hy)
  apply near_ne a p q (two_le_of_ι (ha ▸ hA)) hq0
  apply ι_injective
  simp only [map_add, map_mul]
  rw [← ha, ← hp, ← hq]
  have hx2 : |x| * |x| = x ^ 2 := by rw [← sq, sq_abs]
  have hy2 : |y| * |y| = y ^ 2 := by rw [← sq, sq_abs]
  linear_combination h + hx2 + (1 - A ^ 2) * hy2

/-- A consecutive-product discriminant excludes the negative unit. -/
theorem consecutive_ne_neg_one (n x y : DiffRing V) (hn : 2 ≤ n) :
    x ^ 2 - n * (n + 1) * y ^ 2 ≠ -1 := by
  intro h
  obtain ⟨c, hc⟩ := nonneg_iff.mp (show (0 : DiffRing V) ≤ n by linarith)
  obtain ⟨p, hp⟩ := nonneg_iff.mp (abs_nonneg x)
  obtain ⟨q, hq⟩ := nonneg_iff.mp (abs_nonneg y)
  apply ArithmeticNegativeNorms.consecutive_ne_negative c p q (two_le_of_ι (hc ▸ hn))
  apply ι_injective
  simp only [map_add, map_mul, map_one]
  rw [← hc, ← hp, ← hq]
  have hx2 : |x| * |x| = x ^ 2 := by rw [← sq, sq_abs]
  have hy2 : |y| * |y| = y ^ 2 := by rw [← sq, sq_abs]
  linear_combination h + hx2 - n * (n + 1) * hy2

end DiophantineConsistency.ModelArithmetic
