module
public import PA196.Commands.Store
public import PA196.Logic.Deduction
public import PA196.Logic.Soundness
@[expose] public section

/-! Safety of the exact PA196 command interpreter from a proved zero-tail
stack. Underflow is covered: Cantor decode sends zero to the pair of zeros.
-/
namespace PA196.Logic.CommandSoundness
open M6.Source.Cantor PA196.Commands

def Proved (a : Nat) : Prop := Nonempty (Derivation a)

def truth : Derivation 0 := identity 0
theorem zero_proved : Proved 0 := ⟨truth⟩

theorem mp_proved {a b : Nat} (ha : Proved a) (hi : Proved (Code.I a b)) : Proved b := by
  rcases ha with ⟨p⟩
  rcases hi with ⟨q⟩
  exact ⟨.mp p q⟩

theorem gate_proved (a b c : Nat) : Proved (Code.gate a b c) := by
  unfold Code.gate
  split
  · exact zero_proved
  · rename_i h
    exact ⟨.gate a b c (fun ha => h (Or.inl ha)) (fun hb => h (Or.inr hb))⟩

theorem heads_proved (D H A d h : Nat) (hdom : d ≤ D) (hh : Proved h) :
    ∀ x ∈ Code.heads D H A d h, Proved x := by
  rcases hh with ⟨dh⟩
  intro x hx
  simp only [Code.heads,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.h6 D A H⟩
  · exact ⟨.h5 D H⟩
  · exact ⟨.h4 H D A⟩
  · exact ⟨.h3 H D A⟩
  · exact ⟨.h2 D A H⟩
  · exact ⟨.h1 D H⟩
  · exact ⟨.r8 D A H d hdom⟩
  · exact ⟨.all d dh⟩

inductive SoundStack : Nat → Prop
  | zero : SoundStack 0
  | push {head tail : Nat} : Proved head → SoundStack tail → SoundStack (pair head tail)

theorem SoundStack.pop {w : Nat} (h : SoundStack w) :
    Proved (decode w).1 ∧ SoundStack (decode w).2 := by
  cases h with
  | zero => exact ⟨zero_proved,.zero⟩
  | push hp hs => rw [decode_pair]; exact ⟨hp,hs⟩

theorem SoundStack.prepend (heads : List Nat) (w : Nat)
    (hh : ∀ x ∈ heads, Proved x) (hw : SoundStack w) :
    SoundStack (heads.foldr pair w) := by
  induction heads with
  | nil => exact hw
  | cons a rest ih =>
    exact .push (hh a (by simp)) (ih (by intro x hx; exact hh x (by simp [hx])))

def SoundStore (s : Store) : Prop := Proved s.t ∧ Proved s.h ∧ SoundStack s.w

def zeroStore : Store := ⟨0,0,0,0⟩
theorem zero_sound : SoundStore zeroStore := ⟨zero_proved,zero_proved,.zero⟩

/-- No arithmetic operation or Shift halt test fails on a sound store. -/
theorem command_safe (c : Command) (s : Store) (hs : SoundStore s) :
    ∃ out, step c s = some out ∧ SoundStore out := by
  rcases hs with ⟨ht,hh,hw⟩
  cases c with
  | shift =>
    have hne : s.t+s.h ≠ 1 := by
      intro he
      have hc : s.t = 1 ∨ s.h = 1 := by omega
      rcases hc with hc | hc
      · exact not_refutable (hc ▸ ht)
      · exact not_refutable (hc ▸ hh)
    refine ⟨⟨s.h,(decode s.w).2,s.d,(decode s.w).1⟩,?_,hh,hw.pop.1,hw.pop.2⟩
    simp [step,hne]
  | mp x =>
    by_cases he : Code.I s.t (s.d+x) = s.h
    · have hy : Proved (s.d+x) := mp_proved ht (he ▸ hh)
      refine ⟨⟨s.d+x,pair 0 s.w,s.d+x,0⟩,?_,hy,zero_proved,.push zero_proved hw⟩
      simp [step,he]
    · refine ⟨⟨0,s.w,s.d+x,0⟩,?_,zero_proved,zero_proved,hw⟩
      simp [step,he]
  | ax c x y =>
    refine ⟨_,rfl,gate_proved _ _ _,zero_proved,?_⟩
    apply SoundStack.prepend _ _ _ hw
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact heads_proved _ _ _ _ _ (by omega) hh v hv
    · exact (List.mem_singleton.mp hv) ▸ ht

theorem words_safe (cs : List Command) (s : Store) (hs : SoundStore s) :
    ∃ out, run cs s = some out ∧ SoundStore out := by
  induction cs generalizing s with
  | nil => exact ⟨s,rfl,hs⟩
  | cons c cs ih =>
    obtain ⟨mid,hm,hi⟩ := command_safe c s hs
    obtain ⟨out,ho,hout⟩ := ih mid hi
    exact ⟨out,by simp [run,hm,ho],hout⟩

theorem no_command_word_halts (cs : List Command) : run cs zeroStore ≠ none := by
  obtain ⟨out,ho,_⟩ := words_safe cs zeroStore zero_sound
  rw [ho]
  exact Option.some_ne_none out

#print axioms command_safe
#print axioms words_safe
#print axioms no_command_word_halts
end PA196.Logic.CommandSoundness
