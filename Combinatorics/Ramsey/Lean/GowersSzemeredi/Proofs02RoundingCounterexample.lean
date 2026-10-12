import GowersSzemeredi.Sections01_03
import GowersSzemeredi.ProofInfrastructure

/-! Refute the original unrounded Lemma2.3 length bounds. The corrected
sixteen-denominator statement has its separate constructive companion. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def lemma_2_3_without_rounding_correction : Prop :=
  ∀ (N r s : Nat), 0 < N → 0 < r → 0 < s → r ≤ N → s ≤ N → N ≤ r * s →
    ∀ phi : Nat → ZMod N, NatToZModLinear r phi →
      ∃ m : Nat, ∃ P : Fin m → NatAP,
        IsNatAPPartition P (Finset.range r) ∧
        (∀ j, (P j).IsProper ∧ diameterAtMost ((P j).carrier.image phi) s ∧
          Real.sqrt ((r : Real) * s / (4 * N)) ≤ (P j).length ∧
          ((P j).length : Real) ≤ Real.sqrt ((r : Real) * s / N))

theorem lemma_2_3_without_rounding_correction_counterexample :
    ¬ lemma_2_3_without_rounding_correction := by
  intro h
  obtain ⟨m, P, hpart, hdata⟩ := h 5 5 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun _ ↦ 0)
    ⟨0, 0, fun _ _ ↦ by simp⟩
  have hlow : (1 : Real) < Real.sqrt (5 / 4) :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  norm_num at hlow
  have hupp : Real.sqrt (5 : Real) < 3 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hlen (j : Fin m) : (P j).length = 2 := by
    have hl := (hdata j).2.2.1
    have hu := (hdata j).2.2.2
    norm_num at hl hu
    have hlR : (1 : Real) < (P j).length := hlow.trans_le hl
    have huR : ((P j).length : Real) < 3 := hu.trans_lt hupp
    have hlN : 1 < (P j).length := by exact_mod_cast hlR
    have huN : (P j).length < 3 := by exact_mod_cast huR
    omega
  have hcard (j : Fin m) : (P j).carrier.card = 2 := (hdata j).1.2.trans (hlen j)
  have hsum : (∑ j, (P j).carrier.card) = 5 := by
    simpa only [Finset.card_range] using hpart.sum_card
  have heven : m * 2 = 5 := by simpa [hcard] using hsum
  omega

end LeanProofs.GowersSzemeredi
