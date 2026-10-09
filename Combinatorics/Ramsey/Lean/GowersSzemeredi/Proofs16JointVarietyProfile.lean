import GowersSzemeredi.Proofs16JointVarietyPartition
import GowersSzemeredi.Proofs16FreimanVarietyProfile

/-! Power-width common good partitions for a family of translated varieties.
The two scale exponents multiply once, regardless of the family size.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Uniform simultaneous good partitions above an explicit integer threshold.
The exponent has degree eight in each of the two total phase counts. -/
theorem exists_joint_freiman_variety_good_partition :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N n r : Nat) [NeZero N] [Fact N.Prime]
    (Gamma Psi : Fin n → Finset (ZMod N)) (L : Fin n → Fin r → ZMod N → ZMod N)
    (rho : Fin n → Real) (a b : Fin n → ZMod N) (delta : Real),
    0 < delta → (∀ i, delta ≤ rho i) →
    (∀ i k, IsFreimanLinearOn (bohr (Psi i) (rho i)) (L i k)) →
    ∀ P : Box N 2, P.IsProper →
      section16FreimanVarietyThreshold C p (jointVarietyLinearRank Gamma Psi) (n * r) delta ≤ P.width →
      ∃ m : Nat, ∃ R : Fin m → Box N 2,
        IsBoxPartition R P ∧ (∀ j, (R j).IsProper) ∧
        (∀ j, (P.width : Real) ^ section16FreimanVarietyExponent p
          (jointVarietyLinearRank Gamma Psi) (n * r) ≤ (R j).width) ∧
        ∀ j i, CellGood
          (shiftPairs (bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i / 2)) (a i) (b i))
          (shiftPairs (bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i)) (a i) (b i)) (R j) := by
  obtain ⟨K, p, hK, hp, hMD⟩ := exists_multilinearDiameterPartition
  let C := Nat.ceil K
  have hKC : K ≤ (C : Real) := Nat.le_ceil K
  have hC : 2 ≤ C := by exact_mod_cast hK.trans hKC
  refine ⟨C, p, hC, hp, ?_⟩
  intro N n r _ _ Gamma Psi L rho a b delta hd hdelta hL P hP hlarge
  let s := jointVarietyLinearRank Gamma Psi
  let R := n * r
  let d1 := p * (s + 1)^8
  let d2 := p * (R + 1)^8
  let E := section16FreimanVarietyDegree p s R
  let B := max (C * (s + R + 1)) (Nat.ceil (16 / delta))
  have hE : 0 < E := section16FreimanVarietyDegree_pos hp s R
  have hd2 : 0 < d2 := Nat.mul_pos hp (by positivity)
  have hB : 2 ≤ B := (hC.trans (Nat.le_mul_of_pos_right C (by omega))).trans (le_max_left _ _)
  obtain ⟨H, hH, hBH, hbudget, hroot⟩ := exists_rounded_power_scale B E P.width hB hE hlarge
  let H1 := H ^ d2
  have hHH1 : H ≤ H1 := le_self_pow₀ (by omega) hd2.ne'
  have hscale (u : Nat) (hu : u ≤ s + R) : K * ((u : Real) + 1) ≤ H := by
    calc
      _ ≤ (C : Real) * ((u : Real) + 1) := mul_le_mul_of_nonneg_right hKC (by positivity)
      _ ≤ H := by
        exact_mod_cast (Nat.mul_le_mul_left C (Nat.add_le_add_right hu 1)).trans
          ((le_max_left (C * (s + R + 1)) (Nat.ceil (16 / delta))).trans hBH)
  have hrad : 16 ≤ delta * (H : Real) := by
    have h : 16 / delta ≤ (H : Real) := (Nat.le_ceil _).trans
      (by exact_mod_cast (le_max_right (C * (s + R + 1)) (Nat.ceil (16 / delta))).trans hBH)
    simpa only [mul_comm] using (div_le_iff₀ hd).mp h
  have hrad_i : ∀ i, 16 ≤ rho i * (H : Real) := fun i =>
    hrad.trans (mul_le_mul_of_nonneg_right (hdelta i) (Nat.cast_nonneg H))
  have hrad1 : ∀ i, 16 ≤ rho i * (H1 : Real) := fun i =>
    (hrad_i i).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hHH1) (hd.trans_le (hdelta i)).le)
  have hwide : H1 ^ (p * (s + 1)^8) ≤ P.width := by
    change (H ^ d2) ^ d1 ≤ P.width
    rw [← pow_mul]
    exact hbudget
  obtain ⟨m, Q, hpart, hprop, hw, hg⟩ := joint_variety_partition_of_scales
    Gamma Psi L rho a b (fun i => hd.trans_le (hdelta i)) hL hMD P hP H1 H hH
    (hscale R (by omega)) (fun i => by linarith [hrad_i i])
    ((hscale s (by omega)).trans (by exact_mod_cast hHH1)) hrad1 le_rfl hHH1 hwide
  exact ⟨m, Q, hpart, hprop, fun j => hroot.trans (hw j), hg⟩

end LeanProofs.GowersSzemeredi
