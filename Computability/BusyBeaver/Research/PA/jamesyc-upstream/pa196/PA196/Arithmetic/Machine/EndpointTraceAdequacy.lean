module
public import PA196.Arithmetic.Machine.PAHaltingFormula
@[expose] public section

namespace PA196.Arithmetic.Machine.PA.HaltingFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open NatTape StepFormula

/-- Encode a fixed finite prefix using the imported HFS pairing convention. -/
noncomputable def encodePrefix : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f 0 ∷ encodePrefix n (fun i => f (i + 1))

theorem nth_encodePrefix (n : Nat) (f : Nat → Nat) (i : Nat) (hi : i < n) :
    nth (encodePrefix n f) i = f i := by
  induction n generalizing f i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [encodePrefix]
    | succ i =>
      simpa only [encodePrefix,nth_adjoin_succ] using ih (fun j => f (j+1)) i (by omega)

def path (n : Nat) (c d : NatTape.Configuration) : Prop :=
  ∃ f : Nat → NatTape.Configuration, f 0 = c ∧ f n = d ∧
    ∀ i < n, NatTape.step (f i) = some (f (i + 1))

theorem run_iff_path (n : Nat) (c d : NatTape.Configuration) :
    NatTape.run n c = some d ↔ path n c d := by
  induction n generalizing c d with
  | zero =>
    simp only [NatTape.run, Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨fun _ => c,rfl,rfl,by omega⟩
    · rintro ⟨f,hc,hd,_⟩
      exact hc.symm.trans hd
  | succ n ih =>
    constructor
    · intro h
      cases hs : NatTape.step c with
      | none => simp [NatTape.run,hs] at h
      | some c1 =>
        simp only [NatTape.run,hs,Option.bind_some] at h
        rcases (ih c1 d).mp h with ⟨f,hf0,hfn,hf⟩
        refine ⟨fun i => Nat.casesOn i c f,rfl,hfn,?_⟩
        intro i hi
        cases i with
        | zero =>
          change NatTape.step c = some (f 0)
          simpa only [hf0] using hs
        | succ i => exact hf i (by omega)
    · rintro ⟨f,hf0,hfn,hf⟩
      have hs : NatTape.step c = some (f 1) := by simpa only [hf0] using hf 0 (by omega)
      have ht : NatTape.run n (f 1) = some d := (ih _ _).mpr
        ⟨fun i => f (i+1),rfl,hfn,fun i hi => hf (i+1) (by omega)⟩
      simp [NatTape.run,hs,ht]

theorem halts_encodedTrace (h : NatTape.Halts NatTape.blank) :
    ∃ n qs ls rs, encodedTrace n qs ls rs := by
  rcases h with ⟨n,d,hr,hd⟩
  rcases (run_iff_path n _ d).mp hr with ⟨f,hf0,hfn,hf⟩
  let qs := encodePrefix (n+1) (fun i => controlCode (f i).control)
  let ls := encodePrefix (n+1) (fun i => (f i).left)
  let rs := encodePrefix (n+1) (fun i => (f i).right)
  have hq i (hi : i ≤ n) : nth qs i = controlCode (f i).control :=
    nth_encodePrefix _ _ _ (by omega)
  have hl i (hi : i ≤ n) : nth ls i = (f i).left :=
    nth_encodePrefix _ _ _ (by omega)
  have hb i (hi : i ≤ n) : nth rs i = (f i).right :=
    nth_encodePrefix _ _ _ (by omega)
  refine ⟨n,qs,ls,rs,?_,?_,?_,?_,?_⟩
  · rw [hq 0 (by omega),hf0]; rfl
  · rw [hl 0 (by omega),hf0]; rfl
  · rw [hb 0 (by omega),hf0]; rfl
  · rw [hq n (by omega),hfn,hd]; rfl
  · intro i hi
    rw [hq i (by omega),hl i (by omega),hb i (by omega),
      hq (i+1) (by omega),hl (i+1) (by omega),hb (i+1) (by omega)]
    exact (relation_iff_step _ _).mpr (hf i hi)

def decodeControl (n : Nat) : Control :=
  if h : n < 215 then some ⟨n,h⟩ else none

theorem controlCode_decode {n : Nat} (h : n ≤ 215) :
    controlCode (decodeControl n) = n := by
  unfold decodeControl
  split <;> simp [controlCode]; omega

theorem relation_source_bound {q l r q' l' r' : Nat}
    (h : relation q l r q' l' r') : q < 215 := by
  rcases h with ⟨src,read,hq,_,_⟩
  rw [hq]
  exact src.isLt

theorem encodedTrace_halts {n qs ls rs : Nat} (h : encodedTrace n qs ls rs) :
    NatTape.Halts NatTape.blank := by
  rcases h with ⟨hq0,hl0,hr0,hqn,hsteps⟩
  let f : Nat → NatTape.Configuration := fun i =>
    ⟨decodeControl (nth qs i),nth ls i,nth rs i⟩
  have hb i (hi : i ≤ n) : nth qs i ≤ 215 := by
    by_cases hin : i < n
    · exact Nat.le_of_lt (relation_source_bound (hsteps i hin))
    · have : i = n := by omega
      simp [this,hqn]
  have hcodes i (hi : i ≤ n) : controlCode (f i).control = nth qs i :=
    controlCode_decode (hb i hi)
  have hf0 : f 0 = NatTape.blank := by
    simp only [f,hq0,hl0,hr0]
    rfl
  have hfn : (f n).control = halt := by
    simp [f,hqn,decodeControl,halt]
  refine ⟨n,f n,(run_iff_path n _ _).mpr ⟨f,hf0,rfl,?_⟩,hfn⟩
  intro i hi
  apply (relation_iff_step _ _).mp
  rw [hcodes i (by omega),hcodes (i+1) (by omega)]
  exact hsteps i hi

theorem traceSentence_iff_halts :
    (Nat ⊧/![] traceSentence) ↔ PA196.Arithmetic.Machine.Halts PA196.Arithmetic.Machine.blank := by
  rw [traceSentence_correct,← NatTape.blank_halts_iff]
  exact ⟨fun ⟨_,_,_,_,h⟩ => encodedTrace_halts h,halts_encodedTrace⟩

theorem nonhaltingSentence_iff :
    (Nat ⊧/![] nonhaltingSentence) ↔ ¬ PA196.Arithmetic.Machine.Halts PA196.Arithmetic.Machine.blank := by
  simpa [nonhaltingSentence] using not_congr traceSentence_iff_halts

#print axioms run_iff_path
#print axioms traceSentence_iff_halts
#print axioms nonhaltingSentence_iff
end PA196.Arithmetic.Machine.PA.HaltingFormula

