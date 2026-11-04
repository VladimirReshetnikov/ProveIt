import DiophantineConsistency.Compact44.ForeignBandGeometry
import DiophantineConsistency.Compact44.CyclicAnyPhase
import DiophantineConsistency.Compact44.TwoBand
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ForeignPhaseModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticCyclicWord ArithmeticStandardCasts
open CleanGeometry CompactSymbolicKernel ForeignBandGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem cast_sub (a b : ℕ) (h : b≤a) : ((a-b:ℕ):V)=(a:V)-(b:V) := by
  apply eq_tsub_of_add_eq
  exact_mod_cast (Nat.sub_add_cancel h)
private theorem cyc_cast (t q : ℕ) :
    cyc (8807:V) (t:V) (q:V) = (((t+8807-q%8807)%8807:ℕ):V) := by
  have hle : q%8807≤t+8807 := by have := Nat.mod_lt q (by omega : 0<8807); omega
  have hc : ((t+8807-q%8807:ℕ):V)=(t:V)+8807-((q%8807:ℕ):V) := by
    rw [cast_sub _ _ hle, Nat.cast_add]; simp only [Nat.cast_ofNat]
  have hm : (q:V)%8807 = ((q%8807:ℕ):V) := by
    simpa only [Nat.cast_ofNat] using (cast_mod (V:=V) q 8807).symm
  unfold cyc
  rw [hm, ←hc]
  simpa only [Nat.cast_ofNat] using (cast_mod (V:=V) (t+8807-q%8807) 8807).symm

theorem foreign (j : ℕ) (hj : Allowed j) :
    ¬Bad (cyc 8807 4393 (((5495-j):ℕ):V)) ∧
    ¬Bad (cyc 8807 5495 (((4393-j):ℕ):V)) := by
  have hf := shifted_safe j hj
  have h1 : cyc (8807:V) 4393 (((5495-j):ℕ):V) =
      (((4393+8807-(5495-j)%8807)%8807:ℕ):V) := by
    simpa only [Nat.cast_ofNat] using (cyc_cast (V:=V) 4393 (5495-j))
  have h2 : cyc (8807:V) 5495 (((4393-j):ℕ):V) =
      (((5495+8807-(4393-j)%8807)%8807:ℕ):V) := by
    simpa only [Nat.cast_ofNat] using (cyc_cast (V:=V) 5495 (4393-j))
  rw [h1,h2,bad_cast,bad_cast]
  exact hf

theorem bare (j : Fin 5) :
    ¬Bad (cyc 8807 4393 (TwoBand.bareOffset j:V)) ∧
    ¬Bad (cyc 8807 5495 (TwoBand.bareOffset j:V)) := by
  have hf := bare_safe j
  have h1 : cyc (8807:V) 4393 (TwoBand.bareOffset j:V) =
      (((4393+8807-(![30,62,1100,2201,8849] j)%8807)%8807:ℕ):V) := by
    simpa only [Nat.cast_ofNat,TwoBand.bareOffset] using (cyc_cast (V:=V) 4393 (![30,62,1100,2201,8849] j))
  have h2 : cyc (8807:V) 5495 (TwoBand.bareOffset j:V) =
      (((5495+8807-(![30,62,1100,2201,8849] j)%8807)%8807:ℕ):V) := by
    simpa only [Nat.cast_ofNat,TwoBand.bareOffset] using (cyc_cast (V:=V) 5495 (![30,62,1100,2201,8849] j))
  rw [h1,h2,bad_cast,bad_cast]
  exact hf
#print axioms ForeignPhaseModel.foreign
#print axioms ForeignPhaseModel.bare
end ForeignPhaseModel
