import DiophantineConsistency.ParityPhaseGeometry
import DiophantineConsistency.ForeignPhaseModel
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ParityPhaseModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticCyclicWord ArithmeticStandardCasts
open CleanGeometry ParityPhaseGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem cast_sub (a b : ℕ) (h : b≤a) : ((a-b:ℕ):V)=(a:V)-(b:V) := by
  apply eq_tsub_of_add_eq
  exact_mod_cast (Nat.sub_add_cancel h)
private theorem cyc_cast (t q : ℕ) :
    cyc (8807:V) (t:V) (q:V) = ((phase t q:ℕ):V) := by
  have hle : q%8807≤t+8807 := by have := Nat.mod_lt q (by omega : 0<8807); omega
  have hc : ((t+8807-q%8807:ℕ):V)=(t:V)+8807-((q%8807:ℕ):V) := by
    rw [cast_sub _ _ hle, Nat.cast_add]; simp only [Nat.cast_ofNat]
  have hm : (q:V)%8807 = ((q%8807:ℕ):V) := by
    simpa only [Nat.cast_ofNat] using (cast_mod (V:=V) q 8807).symm
  unfold cyc phase
  rw [hm, ←hc]
  simpa only [Nat.cast_ofNat] using (cast_mod (V:=V) (t+8807-q%8807) 8807).symm

theorem selectors (j : ℕ) (hj : j<943) :
    ¬Bad (cyc 8807 2195 (((4393-j):ℕ):V)) ∧ ¬Bad (cyc 8807 2195 (((5495-j):ℕ):V)) ∧
    ¬Bad (cyc 8807 3296 (((4393-j):ℕ):V)) ∧ ¬Bad (cyc 8807 3296 (((5495-j):ℕ):V)) := by
  have h := ParityPhaseGeometry.selectors j hj
  simpa only [←cyc_cast, Nat.cast_ofNat, bad_cast] using h

theorem bare2195 (j : Fin 5) (hj : j≠⟨2,by decide⟩) :
    ¬Bad (cyc 8807 2195 (TwoBand.bareOffset j:V)) := by
  have h := ParityPhaseGeometry.bare2195 j hj
  simpa only [TwoBand.bareOffset, ←cyc_cast, Nat.cast_ofNat, bad_cast] using h

theorem bare3296 (j : Fin 5) (hj : j≠⟨3,by decide⟩) :
    ¬Bad (cyc 8807 3296 (TwoBand.bareOffset j:V)) := by
  have h := ParityPhaseGeometry.bare3296 j hj
  simpa only [TwoBand.bareOffset, ←cyc_cast, Nat.cast_ofNat, bad_cast] using h
#print axioms ParityPhaseModel.selectors
#print axioms ParityPhaseModel.bare2195
#print axioms ParityPhaseModel.bare3296
end ParityPhaseModel
