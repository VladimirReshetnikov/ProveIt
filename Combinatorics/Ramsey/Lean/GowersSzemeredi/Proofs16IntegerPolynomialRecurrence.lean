import GowersSzemeredi.Proofs16PolynomialRecurrenceProfile
import GowersSzemeredi.Proofs16IntegerSimultaneousRecurrence

/-! Root-width polynomial recurrence profiles with ascending integer axes.
Rounding and constants are identical to the existing modular profiles. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The statement of `exists_ascending_polynomial_section16_recurrence_profile` at
fixed constants. -/
def AscendingPolynomialSection16RecurrenceProfileAt (k : Nat) (K p : Nat) : Prop :=
      ∀ (N q m : Nat) [NeZero N] (P : Box N k), P.IsAscendingInteger →
        ∀ mu : Fin q → Point N k → ZMod N, (∀ i, IsMultilinear (mu i)) →
        section16SimultaneousThreshold k K p q ≤ m → m ≤ P.width →
        ∃ M : Nat, ∃ Q : Fin M → Box N k,
          IsBoxPartition Q P ∧ (∀ j, (Q j).IsAscendingInteger) ∧
          (∀ j, (m : Real) ^ section16SimultaneousExponent k p q ≤ (Q j).width) ∧
          ∀ i j x, x ∈ (Q j).carrier →
            (centeredAbs (mu i x * (Q j).commonDiff) : Real) ≤
              2 * (m : Real) ^ (-section16SimultaneousExponent k p q) * N

/-- The root-width recurrence profile; the partition constant enters as `⌈K⌉`. -/
theorem ascendingPolynomialSection16RecurrenceProfileAt_of (k : Nat) {K : Real} {p : Nat} (hK : 2 ≤ K)
    (hp : 0 < p) (hpartition : AscendingCommonDiffPartitionTwoBoundAt k K p) :
    AscendingPolynomialSection16RecurrenceProfileAt k (Nat.ceil K) p := by
  unfold AscendingPolynomialSection16RecurrenceProfileAt
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
theorem exists_ascending_polynomial_section16_recurrence_profile (k : Nat) :
    ∃ K p : Nat, 2 ≤ K ∧ 0 < p ∧
      ∀ (N q m : Nat) [NeZero N] (P : Box N k), P.IsAscendingInteger →
        ∀ mu : Fin q → Point N k → ZMod N, (∀ i, IsMultilinear (mu i)) →
        section16SimultaneousThreshold k K p q ≤ m → m ≤ P.width →
        ∃ M : Nat, ∃ Q : Fin M → Box N k,
          IsBoxPartition Q P ∧ (∀ j, (Q j).IsAscendingInteger) ∧
          (∀ j, (m : Real) ^ section16SimultaneousExponent k p q ≤ (Q j).width) ∧
          ∀ i j x, x ∈ (Q j).carrier →
            (centeredAbs (mu i x * (Q j).commonDiff) : Real) ≤
              2 * (m : Real) ^ (-section16SimultaneousExponent k p q) * N := by
  obtain ⟨K, p, hK, hp, hpartition⟩ := exists_ascending_simultaneous_commonDiff_partition_two_bound k
  exact ⟨Nat.ceil K, p, by exact_mod_cast hK.trans (Nat.le_ceil K), hp,
    ascendingPolynomialSection16RecurrenceProfileAt_of k hK hp hpartition⟩

end LeanProofs.GowersSzemeredi
