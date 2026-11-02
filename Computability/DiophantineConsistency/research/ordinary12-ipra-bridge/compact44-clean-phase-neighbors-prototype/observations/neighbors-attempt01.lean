import DiophantineConsistency.CleanTargetPhase
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CleanPhaseNeighbors
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open CleanGeometry DiophantineConsistency.ArithmeticCyclicWord
open DiophantineConsistency.ArithmeticStandardCasts
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

theorem finite_neighbors (j : ℕ) (hj : j<8807) (hb : ¬BadNat j) :
    (j+8807-1)%8807≠1063 ∧ (j+8807-2)%8807≠1063 := by
  unfold BadNat at hb
  omega

theorem model_neighbors (x : V) (hx : x<8807) (hb : ¬Bad x) :
    cyc 8807 x 1≠1063 ∧ cyc 8807 x 2≠1063 := by
  obtain ⟨j,hj,hjv⟩ := bounded_standard 8807 x hx
  have hb' : ¬BadNat j := by intro h; apply hb; rw [hjv,bad_cast]; exact h
  have hn := finite_neighbors j hj hb'
  have hc1 : cyc (8807:V) (j:V) 1 = (((j+8807-1)%8807:ℕ):V) := by
    simpa only [Nat.cast_ofNat] using (cyc_cast (V:=V) j 1)
  have hc2 : cyc (8807:V) (j:V) 2 = (((j+8807-2)%8807:ℕ):V) := by
    simpa only [Nat.cast_ofNat] using (cyc_cast (V:=V) j 2)
  rw [hjv,hc1,hc2]
  constructor <;> intro he <;> exact_mod_cast he
#print axioms CleanPhaseNeighbors.finite_neighbors
#print axioms CleanPhaseNeighbors.model_neighbors
end CleanPhaseNeighbors
