import DiophantineConsistency.ThirteenLVCarrier

set_option Elab.async false
set_option maxRecDepth 10000
namespace DiophantineConsistency.ThirteenLVCarrierChecks
open ThirteenLVCarrier ThirteenCarrierSoundness

theorem actual_changed_slot (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    toNew p v 11 = v 11 - G p v * ((data p v).V^2-L p v*(data p v).V) := rfl

theorem twelve_slots_unchanged (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (j : Fin 13) (hj : j ≠ 11) : toNew p v j = v j ∧ toOld p v j = v j := by
  simp [toNew, toOld, setM, hj]

theorem common_blocks_unchanged (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    data p (toNew p v) = data p v ∧ data p (toOld p v) = data p v := by
  simp [toNew, toOld]

theorem both_maps_are_inverse (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    toOld p (toNew p v) = v ∧ toNew p (toOld p v) = v := maps_inverse p v

theorem exact_seed_estimates : (2 : ℤ)+1 ≤ 7^2 ∧ (2 : ℤ)^2 < 12^2 :=
  seed_estimates (c := 2) (delta := 3) (i := 1) (f := 7) (S := 12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- A negative signed ordinate is permitted throughout the local argument. -/
theorem negative_ordinate_bounds :
    (1 : ℤ) ≠ 0 ∧ |(1 : ℤ)| ≤ 1*1 ∧ (1 : ℤ)*1 ≤ 1^2 :=
  mixed_bounds (c := 3) (f := 2) (S := 4) (L := 1) (V := 1) (ordinate := -1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem zero_L_excluded (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hz : value p v = 0) : L p v ≠ 0 :=
  (bounds_of_normal_zero p v (y p v) hb hv hz).1

theorem zero_transport_case : (0 : ℤ) < 1-0*(3^2-3) :=
  subtractive_positive (base := 1) (m := 1) (transport := 0)
    (A := 3) (V := 3) (ordinate := 5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem subtractive_negative_ordinate_case : (0 : ℤ) < 9-1*(3^2-3) :=
  subtractive_positive (base := 1) (m := 9) (transport := 1)
    (A := 3) (V := 3) (ordinate := -3) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Positivity on arbitrary assignments would be false: this is an actual
positive thirteen-input assignment, not a claimed zero of either equation. -/
def samplePorts (j : Fin 4) : ℤ := if j.val = 0 then 3 else 1

theorem sample_positive : (∀ j, 0 < samplePorts j) ∧
    (∀ j : Fin 13, (0 : ℤ) < (fun _ => 1) j) := by
  constructor
  · intro j; simp only [samplePorts]; split <;> norm_num
  · intro j; norm_num

theorem zero_premise_is_needed : toNew samplePorts (fun _ => 1) 11 = -59984 := by
  norm_num [toNew, correction, setM, L, G, data, parent, b, Carrier65.core, samplePorts]

theorem maps_all_positive_zeros (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hz : value p v = 0) :
    (∀ j, 0 < toOld p v j) ∧
      ThirteenCorrectedStrong.value p (toOld p v) = 0 := positive_toOld p v hb hv hz

theorem current_ports_exact :
    currentPolynomial = polynomial (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ)) := rfl

theorem current72_ports_exact :
    currentPolynomial72 = polynomial72 (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ)) := rfl

theorem same_two_mixed_zero_sets (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : value p v = 0 ↔ value72 p v = 0 :=
  positive_zero_iff72 p v hb hv

theorem normalized_maps_all_positive_zeros (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hz : value72 p v = 0) :
    (∀ j, 0 < toOld p v j) ∧ ThirteenCarrier.value71 p (toOld p v) = 0 :=
  positive72_toOld p v hb hv hz

#print axioms ThirteenLVCarrier.norms_of_zero
#print axioms seed_estimates
#print axioms mixed_bounds
#print axioms carrier_nonneg
#print axioms subtractive_positive
#print axioms bounds_of_normal_zero
#print axioms positive_toOld
#print axioms positive_toNew
#print axioms maps_inverse
#print axioms exists_positive_zero_iff
#print axioms no_current_positive_zero_iff_conZFC
#print axioms positive_zero_iff72
#print axioms positive72_toOld
#print axioms positive72_toNew
#print axioms exists_positive72_zero_iff
#print axioms no_current_positive72_zero_iff_conZFC

end DiophantineConsistency.ThirteenLVCarrierChecks
