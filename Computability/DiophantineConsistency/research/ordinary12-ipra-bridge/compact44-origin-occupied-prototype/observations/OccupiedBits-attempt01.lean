import DiophantineConsistency.FixedGraphSelectedOrigin
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace OccupiedBits
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits CompactPartialBand
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem cast_sum_generic {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    ((∑ i ∈ s, f i : ℕ):V) = ∑ i ∈ s, (f i:V) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, Nat.cast_add, ih]

theorem high_bits_one (bits : Fin 41 → V) (hb : ∀ i, bits i≤1)
    (hbig : (2181843386368:V) ≤ ∑ i, (2:V)^i.val*bits i)
    (j : Fin 41) (hj : 34≤j.val) : bits j=1 := by
  classical
  have hnat : (∑ i:Fin 41, (2:ℕ)^i.val)=2199023255551 := by decide
  have hsum : (∑ i:Fin 41,(2:V)^i.val)=2199023255551 := by
    have h := congrArg (fun n:ℕ => (n:V)) hnat
    simp only [cast_sum_generic,Nat.cast_pow,Nat.cast_ofNat] at h
    exact h
  have hp : (17179869184:V)≤(2:V)^j.val := by
    have h := pow_le_pow_right₀ (show (1:V)≤2 by norm_num) hj
    norm_num only at h
    exact h
  have hnonzero : bits j≠0 := by
    intro hz
    have hs := Finset.sum_erase_add (Finset.univ : Finset (Fin 41))
      (fun i => (2:V)^i.val*bits i) (Finset.mem_univ j)
    have hw := Finset.sum_erase_add (Finset.univ : Finset (Fin 41))
      (fun i => (2:V)^i.val) (Finset.mem_univ j)
    have hrest : (∑ i ∈ Finset.univ.erase j, (2:V)^i.val*bits i) ≤
        ∑ i ∈ Finset.univ.erase j, (2:V)^i.val := by
      simpa only [mul_one] using Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hb i) (by simp : (0:V)≤(2:V)^i.val))
    have hsumle : (∑ i, (2:V)^i.val*bits i)+(2:V)^j.val ≤ 2199023255551 := by
      rw [← hs, hz, mul_zero, add_zero]
      calc
        _ ≤ (∑ i ∈ Finset.univ.erase j, (2:V)^i.val)+(2:V)^j.val := add_le_add_right hrest _
        _ = 2199023255551 := hw.trans hsum
    have hcontra : (2199023255552:V) ≤ (∑ i, (2:V)^i.val*bits i)+(2:V)^j.val := by
      calc
        _ = (2181843386368:V)+17179869184 := by norm_num
        _ ≤ _ := add_le_add hbig hp
    exact (not_le_of_gt (show (2199023255552:V)>2199023255551 by norm_num)) (le_trans hcontra hsumle)
  exact le_antisymm (hb j) (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hnonzero))
#print axioms OccupiedBits.high_bits_one
end OccupiedBits
