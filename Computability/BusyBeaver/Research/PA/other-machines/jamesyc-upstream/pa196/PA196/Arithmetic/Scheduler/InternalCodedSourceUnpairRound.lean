module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceUnpairSteps
public import PA196.Arithmetic.Scheduler.InternalCodedSourceFinite
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
variable (r x y : Fin 9) (base : Nat) (hrx : r≠x) (hry : r≠y) (hxy : x≠y)
  (hbound : base+7<3812) (hb : UnpairLoopBound r x y base)
include hrx hry hxy hbound hb in
lemma unpair_round_succ (xs w a b : V) (hv : ValidStore xs) :
    ∃ cs,Trace 5 cs (stateCode ((base+1:Nat):V) (unpairStore r x y xs (w+1) (a+1) b))
      (stateCode ((base+1:Nat):V) (unpairStore r x y xs w a (b+1))) := by
  have hw : w+1≠0 := by simp
  have ha : a+1≠0 := by simp
  have run : finiteRun 5 (stateCode ((base+1:Nat):V) (unpairStore r x y xs (w+1) (a+1) b))=
      stateCode ((base+1:Nat):V) (unpairStore r x y xs w a (b+1)) := by
    have hs0 (w a b : V) := unpair_step0 r x y base hrx hry hxy hbound hb xs w a b hv
    have hs1 (w a b : V) := unpair_step1 r x y base hrx hry hxy hbound hb xs w a b hv
    have hs2 (w a b : V) := unpair_step2 r x y base hrx hry hxy hbound hb xs w a b hv
    have hs3 (w a b : V) := unpair_step3 r x y base hrx hry hxy hbound hb xs w a b hv
    have hs7 (w a b : V) := unpair_step7 r x y base hrx hry hxy hbound hb xs w a b hv
    simp only [Nat.add_zero] at hs0 hs7
    simp only [finiteRun,hs0,hs1,hs2,hs3,hs7,hw,ha,ite_false,add_sub_self]
  obtain ⟨cs,hc⟩ := finiteRun_trace 5 (stateCode ((base+1:Nat):V) (unpairStore r x y xs (w+1) (a+1) b))
  rw [run] at hc
  exact ⟨cs,by simpa only [Nat.cast_ofNat] using hc⟩
include hrx hry hxy hbound hb in
lemma unpair_round_zero (xs w b : V) (hv : ValidStore xs) :
    ∃ n cs,Trace n cs (stateCode ((base+1:Nat):V) (unpairStore r x y xs (w+1) 0 b))
      (stateCode ((base+1:Nat):V) (unpairStore r x y xs w (b+1) 0)) := by
  have hs0 (w a b : V) := unpair_step0 r x y base hrx hry hxy hbound hb xs w a b hv
  have hs1 (w a b : V) := unpair_step1 r x y base hrx hry hxy hbound hb xs w a b hv
  have hs2 (w a b : V) := unpair_step2 r x y base hrx hry hxy hbound hb xs w a b hv
  have hs7 (w a b : V) := unpair_step7 r x y base hrx hry hxy hbound hb xs w a b hv
  simp only [Nat.add_zero] at hs0 hs7
  have hstore : ValidStore (unpairStore r x y xs w 0 (b+1)) := unpairStore_valid r x y xs w 0 (b+1) hv
  have hend : drainEnd y x (b+1) (unpairStore r x y xs w 0 (b+1))=unpairStore r x y xs w (b+1) 0 := by
    unfold drainEnd
    rw [unpairStore_read_x r x y xs w 0 (b+1) hv hxy,zero_add,
      unpairStore_write_y,unpairStore_write_x r x y xs w 0 0 (b+1) hxy]
  have hd : ∃ cs,Trace (3*(b+1)+1) cs
      (stateCode ((base+4+1:Nat):V) (unpairStore r x y xs w 0 (b+1)))
      (stateCode ((base+7+1:Nat):V) (unpairStore r x y xs w (b+1) 0)) := by
    rw [←hend]
    apply drain_loop (base+4) (base+5) (base+6) (base+7) y x hxy.symm
      (by omega) (by omega) (by omega)
    · exact hb ⟨4,by decide⟩
    · exact hb ⟨5,by decide⟩
    · exact hb ⟨6,by decide⟩
    · exact hstore
    · exact unpairStore_read_y r x y xs w 0 (b+1) hv
  obtain ⟨cs,hc⟩ := hd
  have ht := trace_one (stateCode ((base+7+1:Nat):V) (unpairStore r x y xs w (b+1) 0))
  rw [hs7] at ht
  obtain ⟨ds,hd⟩ := trace_compose hc ht
  have s2 : stepValue (stateCode ((base+2+1:Nat):V) (unpairStore r x y xs w 0 (b+1)))=
      stateCode ((base+4+1:Nat):V) (unpairStore r x y xs w 0 (b+1)) := by simpa using hs2 w 0 (b+1)
  obtain ⟨es,he⟩ := trace_prepend _ s2 hd
  obtain ⟨fs,hf⟩ := trace_prepend _ (hs1 w 0 b) he
  have s0 : stepValue (stateCode ((base+1:Nat):V) (unpairStore r x y xs (w+1) 0 b))=
      stateCode ((base+1+1:Nat):V) (unpairStore r x y xs w 0 b) := by simpa using hs0 (w+1) 0 b
  obtain ⟨gs,hg⟩ := trace_prepend _ s0 hf
  exact ⟨_,gs,hg⟩
#print axioms unpair_round_succ
#print axioms unpair_round_zero
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

