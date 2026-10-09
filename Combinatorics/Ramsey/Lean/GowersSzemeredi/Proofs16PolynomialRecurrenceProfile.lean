import GowersSzemeredi.Proofs16SimultaneousRecurrence

/-! Root-width form of the simultaneous Section 16 recurrence.

For each dimension k, integer constants K >= 2 and p > 0 give
  epsilon(q) = 1 / (2*p*(q+1)^(2^(k+2)))
and threshold
  (K*(q+1))^(2*p*(q+1)^(2^(k+2))).
Above that threshold, an input box of width at least m admits a common
proper partition of minimum width m^epsilon(q), with every common-difference
product bounded by 2*m^(-epsilon(q))*N.

Ceiling the real root retains the lower width and improves the inverse
error scale. Doubling the exponent denominator covers the rounding in the
input-width budget. K and p are existential dimension constants; this
module supplies the recurrence profile, not the missing structural inputs
or the printed explicit all-length threshold.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Ceiling a square-root of the target power preserves the integer scale
budget. The factor two in the exponent accounts for rounding. -/
theorem exists_rounded_power_scale (C E m : Nat) (hC : 2 ≤ C) (hE : 0 < E)
    (hm : C ^ (2 * E) ≤ m) :
    ∃ H : Nat, 0 < H ∧ C ≤ H ∧ H ^ E ≤ m ∧
      (m : Real) ^ (((2 * E : Nat) : Real)⁻¹) ≤ H := by
  have hm0 : 0 < m := (pow_pos (by omega : 0 < C) _).trans_le hm
  have hmR : (0 : Real) < m := by exact_mod_cast hm0
  have hEr : ((2 * E : Nat) : Real) ≠ 0 := by exact_mod_cast (by omega : 2 * E ≠ 0)
  let x := (m : Real) ^ (((2 * E : Nat) : Real)⁻¹)
  have hx : 0 < x := Real.rpow_pos_of_pos hmR _
  have hroot : x ^ (2 * E) = m := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmR.le, inv_mul_cancel₀ hEr, Real.rpow_one]
  have hCx : (C : Real) ≤ x := by
    apply le_of_pow_le_pow_left₀ (by omega : 2 * E ≠ 0) hx.le
    rw [hroot]
    exact_mod_cast hm
  have hx2 : (2 : Real) ≤ x := (by exact_mod_cast hC : (2 : Real) ≤ C).trans hCx
  let H := Nat.ceil x
  have hxH : x ≤ (H : Real) := Nat.le_ceil x
  have hH : 0 < H := Nat.ceil_pos.mpr hx
  have hHx : (H : Real) ≤ x ^ 2 := by
    have hc := (Nat.ceil_lt_add_one hx.le).le
    change (H : Real) ≤ x + 1 at hc
    nlinarith
  refine ⟨H, hH, by exact_mod_cast hCx.trans hxH, ?_, hxH⟩
  have hh : (H : Real) ^ E ≤ m := by
    calc
      _ ≤ (x ^ 2) ^ E := pow_le_pow_left₀ (by positivity) hHx _
      _ = m := by rw [← pow_mul, hroot]
  exact_mod_cast hh

/-- Reciprocal-polynomial family-size exponent for the new box recurrence. -/
def section16SimultaneousExponent (k p q : Nat) : Real :=
  ((2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1)))) : Nat) : Real)⁻¹

/-- Integer threshold for the reciprocal-polynomial width exponent. -/
def section16SimultaneousThreshold (k K p q : Nat) : Nat :=
  (K * (q + 1)) ^ (2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1)))))

theorem section16SimultaneousExponent_pos (k p q : Nat) (hp : 0 < p) :
    0 < section16SimultaneousExponent k p q := by
  unfold section16SimultaneousExponent
  positivity

/-- The statement of `exists_polynomial_section16_recurrence_profile` at
fixed constants. -/
def PolynomialSection16RecurrenceProfileAt (k : Nat) (K p : Nat) : Prop :=
      ∀ (N q m : Nat) [NeZero N] (P : Box N k), P.IsProper →
        ∀ mu : Fin q → Point N k → ZMod N, (∀ i, IsMultilinear (mu i)) →
        section16SimultaneousThreshold k K p q ≤ m → m ≤ P.width →
        ∃ M : Nat, ∃ Q : Fin M → Box N k,
          IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
          (∀ j, (m : Real) ^ section16SimultaneousExponent k p q ≤ (Q j).width) ∧
          ∀ i j x, x ∈ (Q j).carrier →
            (centeredAbs (mu i x * (Q j).commonDiff) : Real) ≤
              2 * (m : Real) ^ (-section16SimultaneousExponent k p q) * N

/-- The root-width recurrence profile; the partition constant enters as `⌈K⌉`. -/
theorem polynomialSection16RecurrenceProfileAt_of (k : Nat) {K : Real} {p : Nat} (hK : 2 ≤ K)
    (hp : 0 < p) (hpartition : CommonDiffPartitionTwoBoundAt k K p) :
    PolynomialSection16RecurrenceProfileAt k (Nat.ceil K) p := by
  unfold PolynomialSection16RecurrenceProfileAt
  let C := Nat.ceil K
  have hKC : K ≤ (C : Real) := Nat.le_ceil K
  have hC : 2 ≤ C := by exact_mod_cast hK.trans hKC
  intro N q m _ P hP mu hmu hm hmP
  let E := p * (q + 1) ^ (2 * (2 ^ (k + 1)))
  have hE : 0 < E := Nat.mul_pos hp (by positivity)
  have hCq : 2 ≤ C * (q + 1) := hC.trans (Nat.le_mul_of_pos_right C (by omega))
  obtain ⟨H, hH, hCH, hHm, hrootH⟩ := exists_rounded_power_scale (C * (q + 1)) E m hCq hE hm
  have hscale : K * ((q : Real) + 1) ≤ H := by
    calc
      _ ≤ (C : Real) * ((q : Real) + 1) := mul_le_mul_of_nonneg_right hKC (by positivity)
      _ ≤ H := by exact_mod_cast hCH
  obtain ⟨M, Q, hpart, hproper, hwidth, hsmall⟩ :=
    hpartition N q P hP mu hmu H hH hscale (hHm.trans hmP)
  refine ⟨M, Q, hpart, hproper, fun j => hrootH.trans (hwidth j), ?_⟩
  intro i j x hx
  have hm0 : 0 < m := (pow_pos hH _).trans_le hHm
  have hmR : (0 : Real) < m := by exact_mod_cast hm0
  have hrootpos : 0 < (m : Real) ^ section16SimultaneousExponent k p q := Real.rpow_pos_of_pos hmR _
  have hinv : (H : Real)⁻¹ ≤ (m : Real) ^ (-section16SimultaneousExponent k p q) := by
    rw [Real.rpow_neg hmR.le]
    exact inv_anti₀ hrootpos hrootH
  calc
    _ ≤ (2 / H : Real) * N := hsmall i j x hx
    _ ≤ _ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv (by norm_num)) (Nat.cast_nonneg N)

/-- The new simultaneous recurrence expressed in the root-width notation
of Lemma 16.1, including an integer threshold and all rounding losses. -/
theorem exists_polynomial_section16_recurrence_profile (k : Nat) :
    ∃ K p : Nat, 2 ≤ K ∧ 0 < p ∧
      ∀ (N q m : Nat) [NeZero N] (P : Box N k), P.IsProper →
        ∀ mu : Fin q → Point N k → ZMod N, (∀ i, IsMultilinear (mu i)) →
        section16SimultaneousThreshold k K p q ≤ m → m ≤ P.width →
        ∃ M : Nat, ∃ Q : Fin M → Box N k,
          IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
          (∀ j, (m : Real) ^ section16SimultaneousExponent k p q ≤ (Q j).width) ∧
          ∀ i j x, x ∈ (Q j).carrier →
            (centeredAbs (mu i x * (Q j).commonDiff) : Real) ≤
              2 * (m : Real) ^ (-section16SimultaneousExponent k p q) * N := by
  obtain ⟨K, p, hK, hp, hpartition⟩ := exists_simultaneous_commonDiff_partition_two_bound k
  exact ⟨Nat.ceil K, p, by exact_mod_cast hK.trans (Nat.le_ceil K), hp,
    polynomialSection16RecurrenceProfileAt_of k hK hp hpartition⟩

end LeanProofs.GowersSzemeredi
