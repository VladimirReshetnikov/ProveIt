module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalSymbolicPrimitives
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.Symbolic
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ScanBits M6.Runtime
attribute [local irreducible] Step StepFormula.formula
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
variable (n : V) (box : BoxSt → V → V)

/-- Only the box call actually present in this symbolic state is requested.
This is an explicit semantic premise, not an axiom or an external Nat theorem. -/
def OracleAt (br : Branch) (s : SConf) : Prop :=
  ∀ q l x, s=(q,false,l,[.box x]) → ∀ q' x' extra,
    Runtime.oracle q br x=some (q',x',extra) →
    Progress false (config n box denseControl s)
      (config n box denseControl (q',true,(if extra then .bit true::l else l),[.box x']))

def HeadAt (s : SConf) : Prop :=
  ∀ q l x, s=(q,false,l,[.box x]) → ∃ t : V, box x 0=(1+1)*t

theorem sstep_sound {br : Branch} {s s' : SConf} {m : Bool}
    (h : Runtime.sstep NativeTable.machine br s=some (s',m))
    (ho : OracleAt n box br s) (hh : HeadAt (V := V) box s) :
    Progress m (config n box denseControl s) (config n box denseControl s') := by
  obtain ⟨q,onl,l,r⟩ := s
  cases onl with
  | true =>
    cases l with
    | nil =>
      simp only [Runtime.sstep,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      apply progress_eq
      simp [config,word]
    | cons x l =>
      cases x with
      | bit x =>
        simp only [Runtime.sstep,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        apply progress_eq
        simp [config,word,LeftPhase.bit_div,LeftPhase.bit_mod]
      | box x => simp [Runtime.sstep] at h
      | run b a c =>
        have hp : ∀ {s'' : SConf} {m' : Bool}, Runtime.peelLeft q b a c l r=some (s'',m') →
            Progress m' (config n box denseControl (q,true,.run b a c::l,r))
              (config n box denseControl s'') := by
          intro s'' m' hp
          obtain ⟨rfl,he⟩ := peel_left n box denseControl hp
          exact progress_eq he
        simp only [Runtime.sstep] at h
        split at h
        · rename_i w q2 hm
          split at h
          · rename_i hq
            subst hq
            simp only [Option.some.injEq,Prod.mk.injEq] at h
            obtain ⟨rfl,rfl⟩ := h
            exact run_left n box a c l r hm
          · exact hp h
        · exact hp h
  | false =>
    cases r with
    | nil => simp [Runtime.sstep] at h
    | cons x r =>
      cases x with
      | bit x =>
        simp only [Runtime.sstep] at h
        split at h
        · rename_i w q2 hm
          simp only [Option.some.injEq,Prod.mk.injEq] at h
          obtain ⟨rfl,rfl⟩ := h
          exact bit_right n box l r hm
        · rename_i w q2 hm
          simp only [Option.some.injEq,Prod.mk.injEq] at h
          obtain ⟨rfl,rfl⟩ := h
          exact bit_left n box l r hm
        · simp at h
      | run b a c =>
        have hp : ∀ {s'' : SConf} {m' : Bool}, Runtime.peelRight q b a c l r=some (s'',m') →
            Progress m' (config n box denseControl (q,false,l,.run b a c::r))
              (config n box denseControl s'') := by
          intro s'' m' hp
          obtain ⟨rfl,he⟩ := peel_right n box denseControl hp
          exact progress_eq he
        simp only [Runtime.sstep] at h
        split at h
        · rename_i w q2 hm
          split at h
          · rename_i hq
            subst hq
            simp only [Option.some.injEq,Prod.mk.injEq] at h
            obtain ⟨rfl,rfl⟩ := h
            exact run_right n box a c l r hm
          · exact hp h
        · exact hp h
      | box x =>
        cases r with
        | cons y r => simp [Runtime.sstep] at h
        | nil =>
          simp only [Runtime.sstep] at h
          split at h
          · rename_i q2 x2 extra hor
            simp only [Option.some.injEq,Prod.mk.injEq] at h
            obtain ⟨rfl,rfl⟩ := h
            exact ho q l x rfl q2 x2 extra hor
          · split at h
            · rename_i q2 hm
              simp only [Option.some.injEq,Prod.mk.injEq] at h
              obtain ⟨rfl,rfl⟩ := h
              obtain ⟨t,ht⟩ := hh q l x rfl
              apply progress_one
              have hs := NativeRows.left hm (word n box l 0) t
              simpa [config,word,denseControl,ht,
                Bool.toNat_false,Nat.cast_zero,add_zero] using hs
            · simp at h
end Models
#print axioms sstep_sound
end PA196.Arithmetic.Machine.PA.InternalTrace.Symbolic

