module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualProofCodeComplete
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.NativeCalculus.ActualBasis.Code
open M6.Source M6.Source.Cantor

private theorem bind_some {α β : Type} {o : Option α} {f : α → Option β} {b : β}
    (h : o.bind f = some b) : ∃ a, o=some a ∧ f a=some b := by
  cases o with
  | none => cases h
  | some a => exact ⟨a,rfl,h⟩

theorem ruleCheck_sound (rec : Nat → Option Nat)
    (hr : ∀ n a, rec n = some a → Nonempty (Proof a))
    (tag data a : Nat) (h : ruleCheck rec tag data = some a) : Nonempty (Proof a) := by
  unfold ruleCheck at h
  split at h
  · obtain ⟨⟨b,p,q⟩,_,h⟩ := bind_some h
    obtain ⟨x,hx,h⟩ := bind_some h
    obtain ⟨i,hi,h⟩ := bind_some h
    split at h
    · rename_i he
      cases h
      obtain ⟨px⟩ := hr p x hx
      obtain ⟨pi⟩ := hr q i hi
      rw [source_wim_eq] at he
      exact ⟨Proof.mp px (he ▸ pi)⟩
    · cases h
  · obtain ⟨⟨x,p⟩,_,h⟩ := bind_some h
    obtain ⟨b,hb,h⟩ := bind_some h
    cases h
    obtain ⟨pb⟩ := hr p b hb
    exact ⟨(source_wal_eq x b).symm ▸ Proof.all x pb⟩
  · obtain ⟨⟨x,y⟩,_,h⟩ := bind_some h
    cases h
    exact ⟨Proof.r1 x y⟩
  · obtain ⟨⟨x,y,z⟩,_,h⟩ := bind_some h
    cases h
    exact ⟨Proof.r2 x y z⟩
  · obtain ⟨⟨x,y,z⟩,_,h⟩ := bind_some h
    cases h
    exact ⟨Proof.r3 x y z⟩
  · obtain ⟨⟨x,y,z⟩,_,h⟩ := bind_some h
    cases h
    exact ⟨Proof.r4 x y z⟩
  · obtain ⟨⟨x,y,z⟩,_,h⟩ := bind_some h
    cases h
    exact ⟨Proof.r5 x y z⟩
  · obtain ⟨⟨x,y⟩,_,h⟩ := bind_some h
    cases h
    exact ⟨Proof.r6 x y⟩
  · obtain ⟨⟨x,y,z⟩,_,h⟩ := bind_some h
    cases h
    exact ⟨Proof.r7 x y z⟩
  · obtain ⟨⟨x,y,z,u⟩,_,h⟩ := bind_some h
    change (if u≤x then some (ActualAXCode.rho8 x y z u) else none) = some a at h
    by_cases hu : u≤x
    · rw [ite_eq_left hu] at h
      cases h
      exact ⟨Proof.r8 x y z u hu⟩
    · rw [ite_eq_right hu] at h
      cases h
  · obtain ⟨⟨x,y,z⟩,_,h⟩ := bind_some h
    change (if z≠x ∧ z≠y then some (ActualAXCode.bundle x y z) else none) = some a at h
    by_cases hz : z≠x ∧ z≠y
    · rw [ite_eq_left hz] at h
      cases h
      exact ⟨Proof.bundle x y z hz.1 hz.2⟩
    · rw [ite_eq_right hz] at h
      cases h
  · cases h

theorem check_sound (fuel code a : Nat) (h : check fuel code = some a) : Nonempty (Proof a) := by
  induction fuel generalizing code a with
  | zero => cases h
  | succ fuel ih => exact ruleCheck_sound (check fuel) ih _ _ a h

theorem verify_sound (code a : Nat) (h : verify code = some a) : Nonempty (Proof a) :=
  check_sound _ _ a h

theorem certificate_exists_iff (a : Nat) :
    (∃ code, verify code = some a) ↔ Nonempty (Proof a) := by
  constructor
  · rintro ⟨code,h⟩
    exact verify_sound code a h
  · rintro ⟨p⟩
    exact ⟨certificate p,verify_certificate p⟩

#print axioms check_sound
#print axioms verify_sound
#print axioms certificate_exists_iff
end M6.PA.NativeCalculus.ActualBasis.Code

