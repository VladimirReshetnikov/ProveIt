import PA194CalculusTruth
import PA194Fairness
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194CalculusSoundness
open M6.Source.Cantor PA196.Commands PA196.Commands.Code PA194DerivationCompiler PA194CalculusTruth
open PA194CommandRun PA194CommandEquiv PA194FetchCommand PA194FetchSource

def Proved (a : Nat) : Prop := Nonempty (Derivation a)
theorem zero_proved : Proved 0 := ⟨truth⟩

theorem mp_proved {a b : Nat} (ha : Proved a) (hi : Proved (I a b)) : Proved b := by
  rcases ha with ⟨p⟩
  rcases hi with ⟨q⟩
  exact ⟨.mp p q⟩

theorem gate_proved (a b c : Nat) : Proved (PA194AXReadable.guardedOldBundle a b c) := by
  unfold PA194AXReadable.guardedOldBundle
  split
  · exact zero_proved
  · rename_i h
    exact ⟨.gate a b c (fun ha => h (Or.inr ha.symm)) (fun hb => h (Or.inl hb.symm))⟩

theorem heads_proved (D H A d h : Nat) (hdom : d ≤ D) (hh : Proved h) :
    ∀ x ∈ heads D H A d h, Proved x := by
  rcases hh with ⟨dh⟩
  intro x hx
  simp only [heads,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.h6 D A H⟩
  · exact ⟨.h5 D H⟩
  · exact ⟨.h4 H D A⟩
  · exact ⟨.h3 H D A⟩
  · exact ⟨.h2 D A H⟩
  · exact ⟨.h1 D H⟩
  · exact ⟨.r8 D A H d hdom⟩
  · exact ⟨.all d dh⟩

inductive SoundStack : Nat → Prop where
  | zero : SoundStack 0
  | push {head tail : Nat} : Proved head → SoundStack tail → SoundStack (pair head tail)

theorem SoundStack.pop {w : Nat} (h : SoundStack w) :
    Proved (decode w).1 ∧ SoundStack (decode w).2 := by
  cases h with
  | zero => exact ⟨zero_proved,.zero⟩
  | push hp hs => rw [decode_pair]; exact ⟨hp,hs⟩

theorem SoundStack.prepend (xs : List Nat) (w : Nat)
    (hh : ∀ x ∈ xs, Proved x) (hw : SoundStack w) : SoundStack (xs.foldr pair w) := by
  induction xs with
  | nil => exact hw
  | cons a rest ih =>
    exact .push (hh a (by simp)) (ih (by intro x hx; exact hh x (by simp [hx])))

def SoundStore (s : Store) : Prop := Proved s.t ∧ Proved s.h ∧ SoundStack s.w

theorem zero_sound : SoundStore ⟨0,0,0,0⟩ := ⟨zero_proved,zero_proved,.zero⟩

theorem command_safe (hc : ¬ Proved 1) (c : Command) (s : Store) (hs : SoundStore s) :
    ∃ out, PA194CommandTransfer.step c s = some out ∧ SoundStore out := by
  rcases hs with ⟨ht,hh,hw⟩
  cases c with
  | shift =>
    have hne : s.t+s.h ≠ 1 := by
      intro he
      have hd : s.t = 1 ∨ s.h = 1 := by omega
      rcases hd with hd | hd
      · exact hc (hd ▸ ht)
      · exact hc (hd ▸ hh)
    refine ⟨⟨s.h,(decode s.w).2,s.d,(decode s.w).1⟩,?_,hh,hw.pop.1,hw.pop.2⟩
    simp [PA194CommandTransfer.step,hne]
  | mp x =>
    by_cases he : I s.t (s.d+x) = s.h
    · have hy : Proved (s.d+x) := mp_proved ht (he ▸ hh)
      refine ⟨⟨s.d+x,pair 0 s.w,s.d+x,0⟩,?_,hy,zero_proved,.push zero_proved hw⟩
      simp [PA194CommandTransfer.step,he]
    · refine ⟨⟨0,s.w,s.d+x,0⟩,?_,zero_proved,zero_proved,hw⟩
      simp [PA194CommandTransfer.step,he]
  | ax c x y =>
    refine ⟨_,rfl,gate_proved _ _ _,zero_proved,?_⟩
    apply SoundStack.prepend _ _ _ hw
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · exact (List.mem_singleton.mp hv) ▸ (show Proved (PA194AXSymbolic.diagonal c) from ⟨.diagonal c⟩)
      · exact heads_proved _ _ _ _ _ (by omega) hh v hv
    · exact (List.mem_singleton.mp hv) ▸ ht

theorem advance_safe (hc : ¬ Proved 1) (s : State) (hs : SoundStore s.store) :
    ∃ out, PA194CommandRun.advance s = some out ∧ SoundStore out.store := by
  obtain ⟨v,hv,hvs⟩ := command_safe hc (parse (FetchDispatch.seed s.n s.l)).command s.store hs
  refine ⟨⟨FetchDispatch.nextN s.n s.l,(parse (FetchDispatch.seed s.n s.l)).next,v⟩,?_,hvs⟩
  simp only [PA194CommandRun.advance,hv]

theorem run_safe (hc : ¬ Proved 1) (k : Nat) (s : State) (hs : SoundStore s.store) :
    ∃ out, PA194CommandRun.run k s = some out ∧ SoundStore out.store := by
  induction k generalizing s with
  | zero => exact ⟨s,rfl,hs⟩
  | succ k ih =>
    obtain ⟨mid,hm,hmid⟩ := advance_safe hc s hs
    obtain ⟨out,ho,hout⟩ := ih mid hmid
    exact ⟨out,by simp [PA194CommandRun.run,hm,ho],hout⟩

theorem scheduler_safe (hc : ¬ Proved 1) (s : State) (hs : SoundStore s.store) : ¬ Halts s := by
  rintro ⟨k,last,hk,hlast⟩
  obtain ⟨out,ho,hsout⟩ := run_safe hc k s hs
  rw [hk] at ho
  cases ho
  obtain ⟨next,hnext,_⟩ := advance_safe hc last hsout
  rw [hlast] at hnext
  cases hnext

theorem initial_halts_iff_refutable :
    Halts ⟨2,0,⟨0,0,0,0⟩⟩ ↔ Proved 1 := by
  constructor
  · intro h
    by_cases hc : Proved 1
    · exact hc
    · exact False.elim (scheduler_safe hc ⟨2,0,⟨0,0,0,0⟩⟩ zero_sound h)
  · rintro ⟨p⟩
    exact PA194Fairness.derivation_halts_initial p

#print axioms command_safe
#print axioms initial_halts_iff_refutable
end PA194CalculusSoundness
