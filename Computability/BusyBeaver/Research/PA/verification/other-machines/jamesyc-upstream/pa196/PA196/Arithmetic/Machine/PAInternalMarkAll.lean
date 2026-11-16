module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalMarkPrefix
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.MarkAll
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ScanBits
attribute [local irreducible] Step StepFormula.formula
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

theorem prefix_segment (pre : List V) (hpre : pre.length<9) (l t : V) :
    ∃ qs ls rs, Segment (2*CarryCode.cost (MarkPrefix.file pre)+3) qs ls rs
      (NativeRows.code (Runtime.sk pre.length)) l
      (CarryCode.rightFile (MarkPrefix.file pre) (4*t+2))
      (if pre.length=0 then 2 else 4) (l/2)
      (2*CarryCode.rightFile (MarkPrefix.file pre) (4*t)+l%2) := by
  have hc0 : NativeRows.code (Runtime.sk 0)=51 := by rfl
  cases pre with
  | nil =>
    simpa only [List.length_nil,hc0,MarkPrefix.file_nil,CarryCode.cost_nil,
      CarryCode.right_nil,mul_zero,zero_add,ite_true,one_add_one_eq_two,Nat.cast_ofNat] using MarkDelimiter.segment l t
  | cons p ps =>
    obtain ⟨qa,la,ra,ha⟩ := MarkPrefix.skip (p::ps) 0 l (4*t+2) (by simpa using hpre)
    simp only [Nat.add_zero] at ha
    rw [hc0] at ha
    obtain ⟨qb,lb,rb,hb⟩ := MarkDelimiter.segment (ReturnCode.leftFile (MarkPrefix.file (p::ps)) l) t
    obtain ⟨qc,lc,rc,hc⟩ := MarkPrefix.returning (p::ps) (⟨2,by decide⟩ : WorkingState)
      (by rfl) (by simp) l (4*t)
    obtain ⟨q1,l1,r1,h1⟩ := segment_compose ha hb
    obtain ⟨q2,l2,r2,h2⟩ := segment_compose h1 hc
    have ht : CarryCode.cost (MarkPrefix.file (p::ps))+3+CarryCode.cost (MarkPrefix.file (p::ps))=
        2*CarryCode.cost (MarkPrefix.file (p::ps))+3 := by ring1
    exact ⟨q2,l2,r2,by simpa only [Phase,ht,List.length_cons,Nat.succ_ne_zero,ite_false,one_add_one_eq_two] using h2⟩

/-- All nine mark entries, arbitrary model values and residual suffix, with an
explicit bounded HFS prefix length. No standardness of entries is assumed. -/
theorem segment (r : Fin 9) (pre l t : V) (hlen : len pre=(r.val : V)) :
    ∃ qs ls rs, Segment (2*CarryCode.cost pre+3) qs ls rs
      (NativeRows.code (Runtime.sk r.val)) l (CarryCode.rightFile pre (4*t+2))
      (if r.val=0 then 2 else 4) (l/2) (2*CarryCode.rightFile pre (4*t)+l%2) := by
  obtain ⟨ps,hps,hfile⟩ := MarkPrefix.of_length r.val pre hlen
  have h := prefix_segment ps (by omega) l t
  simpa only [hps,hfile] using h
end Models

def sentence (r : Fin 9) : ArithmeticSentence :=
  “∀ pre l t, !lenDef ↑(r.val) pre → ∃ i o c a b,
    !CarryCode.rightGraph i pre (4*t+2) ∧ !CarryCode.rightGraph o pre (4*t) ∧
    !CarryCode.costGraph c pre ∧ !divDef a l 2 ∧ !remDef b l 2 ∧
    ∃ qs ls rs, !segmentFormula (2*c+3) qs ls rs ↑(NativeRows.code (Runtime.sk r.val)) l i
      ↑(if r.val=0 then 2 else 4) a (2*o+b)”
theorem pa_proves_mark (r : Fin 9) : theory ⊢ sentence r := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sentence,models_iff]
  simp [len_defined.df,CarryCode.right_defined.df,CarryCode.cost_defined.df,div_defined.df,
    rem_defined.df,segment_correct,numeral_eq_natCast]
  intro pre l t hlen
  have h := segment (V := V) r pre l t hlen.symm
  simpa only [Fin.val_eq_zero_iff] using h

#print axioms segment
#print axioms pa_proves_mark
end PA196.Arithmetic.Machine.PA.InternalTrace.MarkAll

