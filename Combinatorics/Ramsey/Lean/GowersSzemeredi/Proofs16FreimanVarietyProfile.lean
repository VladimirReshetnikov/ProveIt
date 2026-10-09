import GowersSzemeredi.Proofs16OscillationPartitionInst
import GowersSzemeredi.Proofs16PolynomialRecurrenceProfile

/-! Power-width good partitions for local Freiman variety phases.

Two simultaneous partitions suffice. Their scale exponents multiply,
remaining polynomial in the linear and mixed phase counts. A rounded
root supplies both integer scales above an explicit radius-dependent
threshold. No global extension of the Freiman maps is assumed.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16FreimanVarietyDegree (p s r : Nat) : Nat :=
  (p * (r + 1) ^ 8) * (p * (s + 1) ^ 8)

def section16FreimanVarietyExponent (p s r : Nat) : Real :=
  ((2 * section16FreimanVarietyDegree p s r : Nat) : Real)⁻¹

def section16FreimanVarietyThreshold (C p s r : Nat) (rho : Real) : Nat :=
  (max (C * (s + r + 1)) (Nat.ceil (16 / rho))) ^
    (2 * section16FreimanVarietyDegree p s r)

theorem section16FreimanVarietyDegree_pos {p : Nat} (hp : 0 < p) (s r : Nat) :
    0 < section16FreimanVarietyDegree p s r := by
  unfold section16FreimanVarietyDegree
  positivity

theorem section16FreimanVarietyExponent_pos {p : Nat} (hp : 0 < p) (s r : Nat) :
    0 < section16FreimanVarietyExponent p s r := by
  have h := section16FreimanVarietyDegree_pos hp s r
  unfold section16FreimanVarietyExponent
  positivity

/-- The two-stage partition yields power-width good cells for all local
Freiman coordinate functions, above an explicit integer threshold. -/
theorem exists_freiman_variety_good_partition :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N : Nat) [NeZero N] [Fact N.Prime] (Gamma Psi : Finset (ZMod N)) (r : Nat)
    (L : Fin r → ZMod N → ZMod N) (rho : Real), 0 < rho →
    (∀ i, IsFreimanLinearOn (bohr Psi rho) (L i)) →
    ∀ P : Box N 2, P.IsProper →
      section16FreimanVarietyThreshold C p (Gamma.card + Psi.card) r rho ≤ P.width →
      ∃ M : Nat, ∃ Q : Fin M → Box N 2,
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
        (∀ j, (P.width : Real) ^ section16FreimanVarietyExponent p
          (Gamma.card + Psi.card) r ≤ (Q j).width) ∧
        ∀ j, CellGood (bilinearBohrVariety Gamma Psi L (rho / 2))
          (bilinearBohrVariety Gamma Psi L rho) (Q j) := by
  obtain ⟨K, p, hK, hp, hMD⟩ := exists_multilinearDiameterPartition
  let C := Nat.ceil K
  have hKC : K ≤ (C : Real) := Nat.le_ceil K
  have hC : 2 ≤ C := by exact_mod_cast hK.trans hKC
  refine ⟨C, p, hC, hp, ?_⟩
  intro N _ _ Gamma Psi r L rho hrho hL P hP hlarge
  let s := Gamma.card + Psi.card
  let d1 := p * (s + 1) ^ 8
  let d2 := p * (r + 1) ^ 8
  let E := section16FreimanVarietyDegree p s r
  let B := max (C * (s + r + 1)) (Nat.ceil (16 / rho))
  have hE : 0 < E := section16FreimanVarietyDegree_pos hp s r
  have hd2 : 0 < d2 := Nat.mul_pos hp (by positivity)
  have hB : 2 ≤ B := (hC.trans (Nat.le_mul_of_pos_right C (by omega))).trans (le_max_left _ _)
  obtain ⟨H, hH, hBH, hbudget, hroot⟩ := exists_rounded_power_scale B E P.width hB hE hlarge
  let H1 := H ^ d2
  have hHH1 : H ≤ H1 := le_self_pow₀ (by omega) hd2.ne'
  have hscale (u : Nat) (hu : u ≤ s + r) : K * ((u : Real) + 1) ≤ H := by
    calc
      _ ≤ (C : Real) * ((u : Real) + 1) := mul_le_mul_of_nonneg_right hKC (by positivity)
      _ ≤ H := by
        exact_mod_cast (Nat.mul_le_mul_left C (Nat.add_le_add_right hu 1)).trans
          ((le_max_left (C * (s + r + 1)) (Nat.ceil (16 / rho))).trans hBH)
  have hrad : 16 ≤ rho * (H : Real) := by
    have h : 16 / rho ≤ (H : Real) := (Nat.le_ceil _).trans
      (by exact_mod_cast (le_max_right (C * (s + r + 1)) (Nat.ceil (16 / rho))).trans hBH)
    simpa only [mul_comm] using (div_le_iff₀ hrho).mp h
  have hrad1 : 16 ≤ rho * (H1 : Real) :=
    hrad.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hHH1) hrho.le)
  have hwide : H1 ^ (p * (Gamma.card + Psi.card + 1) ^ (2 * (2 ^ 2))) ≤ P.width := by
    change (H ^ d2) ^ d1 ≤ P.width
    rw [← pow_mul]
    exact hbudget
  obtain ⟨M, Q, hpart, hproper, hw, hgood⟩ :=
    oscillation_partition_of_scales hL hMD P hP H1 H hH (hscale r (by omega))
      (by linarith) ((hscale s (by omega)).trans (by exact_mod_cast hHH1)) hrad1
      (by exact le_rfl) hHH1 hwide
  exact ⟨M, Q, hpart, hproper, fun j => hroot.trans (hw j),
    fun j => cellGood_of_small_oscillation (Q j) (hgood j)⟩

end LeanProofs.GowersSzemeredi
