import DiophantineConsistency.NativeQuadraticSource52

open DiophantineConsistency
open NativeQuadraticParent NativeQuadraticSource52

-- The actual seventh input is the units digit; the dummy remains separate.
example : code 2 (fun i : Fin 31 => if i = 6 then 1 else 0) = 1 := by decide
example : SelectiveCertificate52.weights 0 = 81 := rfl
example : inputWeights 6 = 0 := rfl

-- A bound of one permits only the shifted zero tuple. The literal fifth
-- source row rejects it, so the binomial contract cannot become vacuous.
example (ports : Fin 4 → ℤ) {H : ℤ} (hH : 0 < H)
    (hc : ∀ k p, p ∈ rowSupport k →
      |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ H)
    {g t : ℕ} (ht : 1 ≤ t) (hbase : (2 : ℤ) ^ t = 4096 * H * (1 : ℤ) ^ 2)
    (hcap : g < 4 * 1 * (2 ^ t) ^ 174) :
    ¬ N (2 ^ t) ^ 2 ∣
      (2 * rank ports (2 ^ t) 1 g).choose (rank ports (2 ^ t) 1 g) := by
  intro hd
  obtain ⟨x, hx, _, hs⟩ :=
    (source_contract ports hH hc (b := 1) (k := 0) (by decide) ht hbase hcap).mp hd
  have hz : x = fun _ => 0 := by
    funext i
    have hi := hx i
    omega
  have hguard := hs 4
  rw [hz] at hguard
  have hone : sourceRows ports (fun _ : Fin 31 => (1 : ℤ)) 4 = 1 := rfl
  change sourceRows ports (fun _ : Fin 31 => (1 : ℤ)) 4 = 0 at hguard
  rw [hone] at hguard
  norm_num at hguard

#print axioms encoded_padded_eval
#print axioms product_eval
#print axioms highInt_pos
#print axioms highInt_pos_of_scale
#print axioms highWord_cast_of_scale
#print axioms lowMask_cast
#print axioms highMask_cast
#print axioms S_cast_of_scale
#print axioms T_cast
#print axioms N_eq_packedBase
#print axioms rank_cast
#print axioms highWord_eq_doubled
#print axioms prebinary_bounds
#print axioms central_divisibility_iff
#print axioms low_mask_iff
#print axioms source_contract
