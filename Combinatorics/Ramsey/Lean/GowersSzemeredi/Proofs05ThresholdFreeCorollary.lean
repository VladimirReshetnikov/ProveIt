import GowersSzemeredi.Section05

/-! The full Corollary 5.8 interface follows from an explicit local analytic
input. The variance and high-correlation branches need no extra scale
assumption. The localization property below is not asserted unconditionally. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The localization budget sufficient for the original Corollary 5.8
length. It is weaker than Report277's all-degree local budget, leaving
room for its affine base case under one uniform interface. -/
def ThresholdFreePolynomialLocalization (k : Nat) : Prop :=
  ∀ (N : Nat) [NeZero N] (P : ModAP N) (phi : ZMod N → ZMod N) (L : Nat),
    P.IsProper → PolynomialOn k Finset.univ phi → 2 ≤ L →
    (2 * L) ^ (polynomialPartitionConstant k / 2) ≤ P.length →
    ∃ m : Nat, ∃ R : Fin m → ModAP N, ∃ z : Fin m → Complex,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      ∀ j, (R j).IsProper ∧ L ≤ (R j).length ∧ ‖z j‖ = 1 ∧
        ∀ x, x ∈ (R j).carrier → ‖exponential (-(phi x)) - z j‖ ≤ 1 / (4 * L)

theorem polynomialPartitionConstant_ge_four {k : Nat} (hk : 1 ≤ k) :
    4 ≤ polynomialPartitionConstant k := by
  have hf : 1 ≤ (Nat.factorial k) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have he : 2 ≤ (k + 1) ^ 2 := by nlinarith
  have hp : 4 ≤ 2 ^ ((k + 1) ^ 2) :=
    (by norm_num : (4 : Nat) = 2 ^ 2) ▸ Nat.pow_le_pow_right (by omega : 1 ≤ 2) he
  exact hp.trans (Nat.le_mul_of_pos_left _ (by omega))

/-- The full Corollary 5.8 interface in one fixed positive degree. -/
def Corollary58At (k : Nat) : Prop :=
  ∀ (N M : Nat) [NeZero N] (A : Finset (ZMod N))
      (P : Fin M → ModAP N) (phi : Fin M → ZMod N → ZMod N) (delta alpha : Real),
    0 < M → 0 < alpha → (A.card : Real) = delta * N →
    (∀ i, (P i).IsProper ∧ PolynomialOn k Finset.univ (phi i)) →
    (∀ x, x ∈ A → ∃ i, x ∈ (P i).carrier) →
    (∀ i j, i != j → Disjoint (P i).carrier (P j).carrier) →
    (∀ i j, (P i).carrier.card ≤ 2 * (P j).carrier.card) →
    alpha * N ≤ ∑ i, ‖∑ s ∈ (P i).carrier, balanced A s * exponential (-(phi i s))‖ →
    ∃ Q : ModAP N, Q.IsProper ∧
      ((N : Real) / M) ^ (polynomialPartitionConstant k : Real)⁻¹ / 8 ≤ Q.carrier.card ∧
      (delta + alpha / 16) * Q.carrier.card ≤ (A ∩ Q.carrier).card

end LeanProofs.GowersSzemeredi
