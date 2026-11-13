module
public import M6.Source.CommandStore
public import M6.Logic.ActualAXBridge
@[expose] public section
namespace M6.ZeroStackSafety
open M6.Source M6.Source.Cantor M6.Source.Enumeration
open M6.PA.NativeCalculus

/-- Finite stacks of proved numeric formulas over a zero tail. Zero decodes
as another pair of zeros, so arbitrary underflow remains sound; no credit or
minimum stack depth assumption is required. -/
inductive SoundStack : Nat → Prop
  | zero : SoundStack 0
  | push {head tail : Nat} : Proved head → SoundStack tail → SoundStack (pair head tail)

theorem SoundStack.pop {w : Nat} (h : SoundStack w) :
    Proved (decode w).1 ∧ SoundStack (decode w).2 := by
  cases h with
  | zero => exact ⟨⟨.truth⟩,.zero⟩
  | push hp hs => rw [decode_pair]; exact ⟨hp,hs⟩

theorem SoundStack.prepend (heads : List Nat) (w : Nat)
    (hh : ∀ x ∈ heads, Proved x) (hw : SoundStack w) :
    SoundStack (heads.foldr pair w) := by
  induction heads with
  | nil => exact hw
  | cons a rest ih =>
    exact .push (hh a (by simp)) (ih (by intro x hx; exact hh x (by simp [hx])))

def SoundStore (s : CommandStore) : Prop := Proved s.t ∧ Proved s.h ∧ SoundStack s.w

def zeroStore : CommandStore := ⟨0,0,0,0⟩
theorem zero_sound : SoundStore zeroStore := ⟨⟨.truth⟩,⟨.truth⟩,.zero⟩

/-- Exact actual-profile command safety from a zero-tail proof stack.
The assumption is native-calculus non-refutation, not PA consistency; the
ordinary PA calibration is a separate theorem. -/
theorem command_safe (hn : ¬ Proved 1) (c : Command) (s : CommandStore)
    (hs : SoundStore s) :
    ∃ out, commandEval c s = some out ∧ SoundStore out := by
  rcases hs with ⟨ht,hh,hw⟩
  cases c with
  | shift =>
    have hne : s.t+s.h ≠ 1 := by
      intro he
      have hc : s.t = 1 ∨ s.h = 1 := by omega
      rcases hc with hc | hc
      · exact hn (hc ▸ ht)
      · exact hn (hc ▸ hh)
    refine ⟨⟨s.h,(decode s.w).2,s.d,(decode s.w).1⟩,?_,hh,hw.pop.1,hw.pop.2⟩
    simp [commandEval,hne]
  | mp x =>
    by_cases he : AXCode.wim s.t (s.d+x) = s.h
    · have hy : Proved (s.d+x) := by
        apply mp_proved ht
        simpa only [wim,AXCode.wim] using (he ▸ hh : Proved (AXCode.wim s.t (s.d+x)))
      refine ⟨⟨s.d+x,pair 0 s.w,s.d+x,0⟩,?_,hy,⟨.truth⟩,.push ⟨.truth⟩ hw⟩
      simp [commandEval,he]
    · refine ⟨⟨0,s.w,s.d+x,0⟩,?_,⟨.truth⟩,⟨.truth⟩,hw⟩
      simp [commandEval,he]
  | ax c x y =>
    refine ⟨_,rfl,actual_gate_proved _ _ _,⟨.truth⟩,?_⟩
    apply SoundStack.prepend _ _ _ hw
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact actual_heads_proved _ _ _ _ _ (by omega) hh v hv
    · exact (List.mem_singleton.mp hv) ▸ ht

theorem words_safe (hn : ¬ Proved 1) (cs : List Command) (s : CommandStore)
    (hs : SoundStore s) :
    ∃ out, commandsEval cs s = some out ∧ SoundStore out := by
  induction cs generalizing s with
  | nil => exact ⟨s,rfl,hs⟩
  | cons c cs ih =>
    obtain ⟨mid,hm,hi⟩ := command_safe hn c s hs
    obtain ⟨out,ho,hout⟩ := ih mid hi
    exact ⟨out,by simp [commandsEval,hm,ho],hout⟩

#print axioms command_safe
#print axioms words_safe
end M6.ZeroStackSafety
