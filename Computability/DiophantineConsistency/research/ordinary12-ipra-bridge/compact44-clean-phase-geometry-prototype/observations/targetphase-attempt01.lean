import DiophantineConsistency.CleanPhaseChoice
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CleanTargetPhase
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open CleanGeometry CleanPhaseChoice DiophantineConsistency.ArithmeticCyclicWord
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
  unfold cyc
  rw [← cast_mod (V:=V) q 8807, ←hc, ← cast_mod]
  simp only [Nat.cast_ofNat]

theorem finite_relation (q : ℕ) :
    (5495+8807-q%8807)%8807 = (((4393+8807-q%8807)%8807)+1102)%8807 := by
  have := Nat.mod_lt q (by omega : 0<8807)
  omega

theorem target_relation (q : V) :
    cyc 8807 5495 q = (cyc 8807 4393 q+1102)%8807 := by
  have hq : q%8807<8807 := mod_lt _ (by norm_num)
  obtain ⟨j,hj,hjv⟩ := bounded_standard 8807 (q%8807) hq
  rw [←cyc_mod 8807 5495 q (by norm_num), ←cyc_mod 8807 4393 q (by norm_num), hjv]
  rw [cyc_cast 5495 j,cyc_cast 4393 j]
  have h := congrArg (fun n : ℕ => (n:V)) (finite_relation j)
  rw [cast_mod] at h
  push_cast at h
  exact h

theorem target_choice (q : V) :
    ¬Bad (cyc 8807 4393 q) ∨ ¬Bad (cyc 8807 5495 q) := by
  rw [target_relation]
  exact choose_shifted q
#print axioms CleanTargetPhase.finite_relation
#print axioms CleanTargetPhase.target_relation
#print axioms CleanTargetPhase.target_choice
end CleanTargetPhase
