module
public import M6.Source.AXMacroSound
@[expose] public section
namespace M6.Source.AXMacro
/-- Every macro carries its actual primitive-source semantic proof. -/
inductive Plan (sites : Array Site) : Nat → Nat → List Op → Prop
  | nil (pc) : Plan sites pc pc []
  | cons {pc next last op ops} : Realizes sites op pc next →
      Plan sites next last ops → Plan sites pc last (op::ops)

theorem Plan.sound (hp : Plan sites first last ops) (s s' : Store)
    (he : run ops s = some s') (bottom : Nat) (f : Registers) :
    ∃ n, Steps sites n (configAt first s bottom f) (configAt last s' bottom f) := by
  induction hp generalizing s with
  | nil pc =>
    simp only [run,Option.some.injEq] at he
    subst s'
    exact ⟨0,Steps.refl _⟩
  | @cons pc next last op ops hr hp ih =>
    cases hx : exec op s with
    | none => simp [run,hx] at he
    | some mid =>
      simp only [run,hx,Option.bind_some] at he
      obtain ⟨n,_,hs⟩ := hr s mid hx bottom f
      obtain ⟨m,ht⟩ := ih mid he
      exact ⟨n+m,hs.append ht⟩
#print axioms Plan.sound
end M6.Source.AXMacro

