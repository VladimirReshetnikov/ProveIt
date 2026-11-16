module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalFileLayout
public import M6PA.Model.PAInternalDecrementPositive
public import M6PA.Model.PAInternalDecrementZero
public import M6PA.Model.PAInternalSymbolicPrimitives
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.FileBoxes
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open ScanBits CarryCode FileLayout M6.Runtime Symbolic
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
/-- Single interpretation for every original symbolic file shape. Register
indices are standard syntactic naturals; HFS files/entries may be nonstandard. -/
noncomputable def box (xs : V) : BoxSt → V → V
  | .plain .none,t => rightFile xs t
  | .mark r,t => rightFile (front r xs) (4*repeatBits (value r xs) 1 (rightFile (suffix r xs) t))
  | .plain (.inc r),t => rightFile (front r xs)
      (4*repeatBits (value r xs+1) 1 (rightFile (suffix r xs) (8*t+6))+2)
  | .plain (.dec r),t => rightFile (front r xs)
      (4*repeatBits (value r xs-1) 1 (rightFile (suffix r xs) t)+2)

lemma file_even (xs t : V) (he : ∃ u : V,t=(1+1)*u) :
    ∃ u : V,rightFile xs t=(1+1)*u := by
  rcases nil_or_adjoin xs with hz | ⟨a,as,ha⟩
  · simpa [hz] using he
  · rw [ha,right_adjoin]
    exact ⟨2*repeatBits a 1 (rightFile as t)+1,by ring1⟩

lemma head (xs : V) (x : BoxSt) : ∃ t : V,box xs x 0=(1+1)*t := by
  have even4 (u : V) : ∃ t : V,4*u=(1+1)*t := ⟨2*u,by ring1⟩
  have even42 (u : V) : ∃ t : V,4*u+2=(1+1)*t := ⟨2*u+1,by ring1⟩
  cases x with
  | mark r => exact file_even _ _ (even4 _)
  | plain e =>
    cases e with
    | none => exact file_even _ _ ⟨0,by simp⟩
    | inc r => exact file_even _ _ (even42 _)
    | dec r => exact file_even _ _ (even42 _)

lemma marked (xs : V) (r : Nat) : box xs (.mark r) 0=Increment.input (front r xs) (value r xs) (suffix r xs) := rfl
lemma incremented (xs : V) (r : Nat) : box xs (.plain (.inc r)) 0=Increment.output (front r xs) (value r xs) (suffix r xs) := by
  simp only [box,Increment.output,mul_zero,zero_add]
lemma decremented (xs : V) (r : Nat) : box xs (.plain (.dec r)) 0=DecrementPositive.output (front r xs) (value r xs-1) (suffix r xs) := rfl

lemma mark_call (xs l : V) (r : Fin 9) (hl : (r.val : V)<len xs) : Progress false
    ⟨(NativeRows.code (sk r.val) : V),l,box xs (.plain .none) 0⟩
    ⟨(NativeRows.code (markExit r.val) : V),l/2,(1+1)*box xs (.mark r.val) 0+l%2⟩ := by
  obtain ⟨qs,ls,rs,h⟩ := MarkAll.segment r (front r.val xs) l
    (repeatBits (value r.val xs) 1 (rightFile (suffix r.val xs) 0))
    (prefix_length r.val xs (le_of_lt hl))
  have hi := input_split r.val xs (0 : V) hl
  have hc : NativeRows.code (markExit r.val)=if r.val=0 then 2 else 4 := by
    unfold markExit
    split <;> rfl
  refine ⟨2*cost (front r.val xs)+3,qs,ls,rs,?_,by simp⟩
  rw [hc]
  by_cases hr : r.val=0 <;>
    simpa only [box,hi,hr,ite_true,ite_false,Nat.cast_ofNat,one_add_one_eq_two] using h

lemma increment_call (xs l : V) (r : Nat) : Progress false
    ⟨(NativeRows.code 64 : V),l,box xs (.mark r) 0⟩
    ⟨(NativeRows.code 40 : V),l/2,(1+1)*box xs (.plain (.inc r)) 0+l%2⟩ := by
  obtain ⟨qs,ls,rs,h⟩ := Increment.segment (front r xs) (value r xs) (suffix r xs) l
  refine ⟨Increment.time (front r xs) (value r xs) (suffix r xs),qs,ls,rs,?_,by simp⟩
  simpa only [show NativeRows.code 64=64 by rfl,show NativeRows.code 40=40 by rfl,
    Nat.cast_ofNat,marked,incremented] using h

lemma positive_call (xs l : V) (r : Nat) (hp : value r xs≠0) : Progress false
    ⟨(NativeRows.code 0 : V),l,box xs (.mark r) 0⟩
    ⟨(NativeRows.code 40 : V),l,(1+1)*box xs (.plain (.dec r)) 0+1⟩ := by
  rcases zero_or_succ (value r xs) with hz | ⟨v,hv⟩
  · exact False.elim (hp hz)
  obtain ⟨qs,ls,rs,h⟩ := DecrementPositive.segment (front r xs) v (suffix r xs) l
  refine ⟨DecrementPositive.time (front r xs),qs,ls,rs,?_,by simp⟩
  simpa [show NativeRows.code 0=1 by rfl,show NativeRows.code 40=40 by rfl,
    marked,decremented,hv,one_add_one_eq_two] using h
lemma zero_call (xs l : V) (r : Nat) (hl : (r : V)<len xs)
    (hz : value r xs=0) (hs : suffix r xs≠0) : Progress false
    ⟨(NativeRows.code 0 : V),l,box xs (.mark r) 0⟩
    ⟨(NativeRows.code 97 : V),l/2,(1+1)*box xs (.plain .none) 0+l%2⟩ := by
  rcases nil_or_adjoin (suffix r xs) with hnil | ⟨w,ws,hw⟩
  · exact False.elim (hs hnil)
  let t := repeatBits w 1 (rightFile ws 0)
  obtain ⟨qs,ls,rs,h⟩ := DecrementZero.segment (front r xs) l t
  have hi : box xs (.mark r) 0=rightFile (front r xs) (16*t+8) := by
    simp only [box,hz,repeat_zero,hw,right_adjoin]
    congr 1
    dsimp [t]
    ring1
  have ho : box xs (.plain .none) 0=rightFile (front r xs) (16*t+10) := by
    rw [box,input_split r xs (0 : V) hl]
    simp only [hz,repeat_zero,hw,right_adjoin]
    congr 1
    dsimp [t]
    ring1
  refine ⟨2*cost (front r xs)+7,qs,ls,rs,?_,by simp⟩
  simpa only [show NativeRows.code 0=1 by rfl,show NativeRows.code 97=94 by rfl,
    Nat.cast_ofNat,Nat.cast_one,hi,ho,one_add_one_eq_two] using h

end Models
#print axioms head
#print axioms mark_call
#print axioms increment_call
#print axioms positive_call
#print axioms zero_call
end M6.Arithmetic.PA.InternalTrace.FileBoxes

