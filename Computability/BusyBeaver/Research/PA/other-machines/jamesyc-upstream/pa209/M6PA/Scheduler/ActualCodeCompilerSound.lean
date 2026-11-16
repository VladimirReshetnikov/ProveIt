module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCodeCompilerCanonical
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.NativeCalculus.ActualBasis.Code
open M6.Source M6.Source.Cantor M6.Source.Enumeration
open M6.Source.ActualCommandMacros
attribute [local irreducible] PUSH H genTail mpTail headWord head8Word gateWord
  commandsEval commandEval

private theorem bind_some {α β : Type} {o : Option α} {f : α → Option β} {b : β}
    (h : o.bind f=some b) : ∃ a,o=some a ∧ f a=some b := by
  cases o with
  | none => cases h
  | some a => exact ⟨a,rfl,h⟩
private theorem compile_transport {a b : Nat} (h : a=b) (p : Proof a) :
    compile (h ▸ p)=compile p := by cases h; rfl

/-- The witness is proved constructively from successful numeric checks, never
an input to the executable compiler and never selected using choice. -/
theorem ruleCompile_matches (rec : Nat → Option Nat) (words : Nat → List Command)
    (hr : ∀ n a,rec n=some a → ∃ p : Proof a,compile p=words n)
    (tag data a : Nat) (h : ruleCheck rec tag data=some a) :
    ∃ p : Proof a,compile p=ruleCompile words tag data := by
  unfold ruleCheck at h
  split at h
  · obtain ⟨⟨b,p,q⟩,hf,h⟩ := bind_some h
    obtain ⟨x,hx,h⟩ := bind_some h
    obtain ⟨i,hi,h⟩ := bind_some h
    split at h
    · rename_i he
      cases h
      obtain ⟨px,hpx⟩ := hr p x hx
      obtain ⟨pi,hpi⟩ := hr q i hi
      rw [source_wim_eq] at he
      subst i
      refine ⟨Proof.mp px pi,?_⟩
      change compile pi ++ PUSH ++ compile px ++ PUSH ++ mpTail _ = _
      rw [hpi,hpx]
      simp only [ruleCompile,hf]
    · cases h
  · obtain ⟨⟨x,p⟩,hf,h⟩ := bind_some h
    obtain ⟨b,hb,h⟩ := bind_some h
    cases h
    obtain ⟨pb,hpb⟩ := hr p b hb
    rw [source_wal_eq]
    refine ⟨Proof.all x pb,?_⟩
    change compile pb ++ genTail x = _
    rw [hpb]
    simp only [ruleCompile,hf]
  · obtain ⟨⟨x,y⟩,hf,h⟩ := bind_some h
    cases h
    exact ⟨Proof.r1 x y,by simp only [ruleCompile,hf]; rfl⟩
  · obtain ⟨⟨x,y,z⟩,hf,h⟩ := bind_some h
    cases h
    exact ⟨Proof.r2 x y z,by simp only [ruleCompile,hf]; rfl⟩
  · obtain ⟨⟨x,y,z⟩,hf,h⟩ := bind_some h
    cases h
    exact ⟨Proof.r3 x y z,by simp only [ruleCompile,hf]; rfl⟩
  · obtain ⟨⟨x,y,z⟩,hf,h⟩ := bind_some h
    cases h
    exact ⟨Proof.r4 x y z,by simp only [ruleCompile,hf]; rfl⟩
  · obtain ⟨⟨x,y,z⟩,hf,h⟩ := bind_some h
    cases h
    exact ⟨Proof.r5 x y z,by simp only [ruleCompile,hf]; rfl⟩
  · obtain ⟨⟨x,y⟩,hf,h⟩ := bind_some h
    cases h
    exact ⟨Proof.r6 x y,by simp only [ruleCompile,hf]; rfl⟩
  · obtain ⟨⟨x,y,z⟩,hf,h⟩ := bind_some h
    cases h
    exact ⟨Proof.r7 x y z,by simp only [ruleCompile,hf]; rfl⟩
  · obtain ⟨⟨x,y,z,u⟩,hf,h⟩ := bind_some h
    change (if u≤x then some (ActualAXCode.rho8 x y z u) else none)=some a at h
    by_cases hu : u≤x
    · rw [ite_eq_left hu] at h
      cases h
      exact ⟨Proof.r8 x y z u hu,by simp only [ruleCompile,hf,ite_eq_left hu]; rfl⟩
    · rw [ite_eq_right hu] at h
      cases h
  · obtain ⟨⟨x,y,z⟩,hf,h⟩ := bind_some h
    change (if z≠x ∧ z≠y then some (ActualAXCode.bundle x y z) else none)=some a at h
    by_cases hz : z≠x ∧ z≠y
    · rw [ite_eq_left hz] at h
      cases h
      exact ⟨Proof.bundle x y z hz.1 hz.2,by simp only [ruleCompile,hf,ite_eq_left hz]; rfl⟩
    · rw [ite_eq_right hz] at h
      cases h
  · cases h

theorem compileTree_matches (fuel tree a : Nat) (h : check fuel tree=some a) :
    ∃ p : Proof a,compile p=compileTree fuel tree := by
  induction fuel generalizing tree a with
  | zero => cases h
  | succ fuel ih => exact ruleCompile_matches (check fuel) (compileTree fuel) ih _ _ _ h

theorem compileCertificate_matches (code a : Nat) (h : verify code=some a) :
    ∃ p : Proof a,compile p=compileCertificate code := compileTree_matches _ _ _ h

theorem compileCertificate_result (code a t w : Nat) (h : verify code=some a) :
    commandsEval (compileCertificate code) ⟨t,w,0,0⟩=none ∨
    commandsEval (compileCertificate code) ⟨t,w,0,0⟩=some ⟨a,w,0,0⟩ := by
  obtain ⟨p,hp⟩ := compileCertificate_matches code a h
  rw [←hp]
  exact compile_result p t w

#print axioms compileTree_matches
#print axioms compileCertificate_result
end M6.PA.NativeCalculus.ActualBasis.Code

