import Trace74Guarded

/-! Both coordinate maps preserve positive zeros on the explicit guard. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74GuardedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing Trace74Guarded
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem flip_involution (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hmask : v 1+v 2<q p v) : flip p (flip p v)=v := by
  have hq : q p (flip p v)=q p v := by simp [q,Trace74Guarded.flip]
  have ha : v 2≤q p v-v 1 := le_of_lt (lt_tsub_iff_right.mpr (by simpa [add_comm] using hmask))
  funext j
  fin_cases j <;> try rfl
  change q p (flip p v)-(flip p v) 1-(flip p v) 2=v 2
  rw [hq]
  change q p v-v 1-(q p v-v 1-v 2)=v 2
  exact tsub_tsub_cancel_of_le ha

theorem flip_guard (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hv : ∀j,0<v j) (hmask : v 1+v 2<q p v) :
    (flip p v) 1+(flip p v) 2<q p (flip p v) := by
  have hq : q p (flip p v)=q p v := by simp [q,Trace74Guarded.flip]
  have hf : v 1≤q p v := le_trans (by simp) (le_of_lt hmask)
  have ha : v 2≤q p v-v 1 := le_of_lt (lt_tsub_iff_right.mpr (by simpa [add_comm] using hmask))
  have hC : (q p v-v 1-v 2)+v 2=q p v-v 1 := tsub_add_cancel_of_le ha
  have hF : (q p v-v 1)+v 1=q p v := tsub_add_cancel_of_le hf
  rw [hq]
  change v 1+(q p v-v 1-v 2)<q p v
  calc
    v 1+(q p v-v 1-v 2)<(v 1+(q p v-v 1-v 2))+v 2 := lt_add_of_pos_right _ (hv 2)
    _=v 1+((q p v-v 1-v 2)+v 2) := by ring
    _=v 1+(q p v-v 1) := by rw [hC]
    _=q p v := by rw [add_comm,hF]

theorem old_to_guarded (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hv : ∀j,0<v j) (hmask : v 1+v 2<q p v)
    (hz : DiophantineConsistency.TenPositiveTrace75.value75
      (fun j => ((p j:ℕ):DiffRing V)) (fun j => ι (v j)) = 0) :
    (∀j,0<flip p v j) ∧ (flip p v) 1+(flip p v) 2<q p (flip p v) ∧
    Trace74Mask.value74 (fun j => ((p j:ℕ):DiffRing V)) (fun j => ι (flip p v j)) = 0 := by
  have hg := flip_guard p v hv hmask
  refine ⟨flip_positive p v hv hmask,hg,?_⟩
  have h := Trace74Mask.coordinate_identity (fun j => ((p j:ℕ):DiffRing V)) (fun j => ι (flip p v j))
  rw [oldVal_cast p (flip p v) hg,flip_involution p v hmask] at h
  rw [h]
  exact hz

theorem guarded_positive_zero_iff (p : Fin 4 → ℕ) :
    (∃v : Fin 10 → V, (∀j,0<v j) ∧ v 1+v 2<q p v ∧
      DiophantineConsistency.TenPositiveTrace75.value75
        (fun j => ((p j:ℕ):DiffRing V)) (fun j => ι (v j)) = 0) ↔
    (∃v : Fin 10 → V, (∀j,0<v j) ∧ v 1+v 2<q p v ∧
      Trace74Mask.value74 (fun j => ((p j:ℕ):DiffRing V)) (fun j => ι (v j)) = 0) := by
  constructor
  · rintro ⟨v,hv,hmask,hz⟩
    exact ⟨flip p v,old_to_guarded p v hv hmask hz⟩
  · rintro ⟨v,hv,hmask,hz⟩
    have hp := flip_positive p v hv hmask
    have hg := flip_guard p v hv hmask
    exact ⟨flip p v,hp,hg,(guarded_to_old p v hv hmask hz).2⟩

#print axioms Trace74GuardedIff.guarded_positive_zero_iff
end Trace74GuardedIff
