import GowersSzemeredi.Proofs16LocalizationBudget
import GowersSzemeredi.Proofs13ExplicitPowerThreshold

/-! Integer interval lengths and power scales for genuine product-property
slabs. The rounding and positive-power thresholds are explicit. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16SlabLength (N R : Nat) : Nat := Nat.floor ((N : Real) / (4 * R))

theorem section16SlabLength_bounds {N R : Nat} (hR : 0 < R) (hN : 8 * R ≤ N) :
    0 < section16SlabLength N R ∧ section16SlabLength N R ≤ N ∧
      4 * section16SlabLength N R * R ≤ N ∧
      (1 / (8 * (R : Real))) * N ≤ section16SlabLength N R := by
  have hR' : (0 : Real) < R := by exact_mod_cast hR
  have hN' : 8 * (R : Real) ≤ N := by exact_mod_cast hN
  have hR1 : (1 : Real) ≤ R := by exact_mod_cast hR
  have hden : (0 : Real) < 4 * R := by positivity
  have hx : (2 : Real) ≤ (N : Real) / (4 * R) := (le_div_iff₀ hden).mpr (by linarith)
  obtain ⟨hL, hhalf⟩ := floor_half_lower hx
  have hfloor : (section16SlabLength N R : Real) ≤ (N : Real) / (4 * R) :=
    Nat.floor_le (by positivity)
  have hupper : (section16SlabLength N R : Real) * (4 * R) ≤ N :=
    (le_div_iff₀ hden).mp hfloor
  refine ⟨hL, ?_, ?_, ?_⟩
  · exact_mod_cast hfloor.trans (div_le_self (by positivity) (by linarith))
  · exact_mod_cast (show 4 * (section16SlabLength N R : Real) * R ≤ N by
      nlinarith only [hupper])
  · have heq : (1 / (8 * (R : Real))) * N = ((N : Real) / (4 * R)) / 2 := by ring
    rw [heq]
    change (N : Real) / (4 * R) / 2 ≤ Nat.floor ((N : Real) / (4 * R))
    linarith only [hhalf]

/-- A fixed positive density in the original interval absorbs half of a
positive power exponent once the displayed threshold is passed. -/
theorem section16_slab_power_scale {N L : Nat} {theta e : Real}
    (ht : 0 < theta) (he : 0 < e) (hL : theta * N ≤ L)
    (hN : positivePowerThreshold 1 (theta ^ e) (e / 2) ≤ N) :
    (N : Real) ^ (e / 2) ≤ (L : Real) ^ e := by
  have hn1 : (1 : Real) ≤ N := (positivePowerThreshold_one_le _ _ _).trans hN
  have hn : (0 : Real) < N := zero_lt_one.trans_le hn1
  have hs : (1 : Real) ≤ theta ^ e * (N : Real) ^ (e / 2) :=
    positivePowerThreshold_spec (Real.rpow_pos_of_pos ht _) (by positivity) hN
  calc
    (N : Real) ^ (e / 2) ≤
        (N : Real) ^ (e / 2) * (theta ^ e * (N : Real) ^ (e / 2)) :=
      le_mul_of_one_le_right (by positivity) hs
    _ = (theta * N) ^ e := by
      rw [Real.mul_rpow ht.le hn.le]
      have heq : e = e / 2 + e / 2 := by ring
      conv_rhs => rw [heq, Real.rpow_add hn]
      simp only [← heq]
      ring
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hL he.le

end LeanProofs.GowersSzemeredi
