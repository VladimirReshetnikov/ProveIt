module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalScanLeft
public import PA196.Arithmetic.Machine.PAInternalPhaseTrace
@[expose] public section

namespace PA196.Arithmetic.Machine.PA.InternalTrace.LeftPhase
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open ScanBits
attribute [local irreducible] Step StepFormula.formula

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

lemma bool_lt_two (b : Bool) : (b.toNat : V)<2 := by cases b <;> simp
lemma bit_div (b : Bool) (u : V) : ((1+1)*u+b.toNat)/2=u := by
  simpa only [one_add_one_eq_two] using div_mul_add' u 2 (bool_lt_two (V := V) b)
lemma bit_mod (b : Bool) (u : V) : ((1+1)*u+b.toNat)%2=b.toNat := by
  simpa only [mul_comm,one_add_one_eq_two] using mod_mul_add_of_lt u 2 (bool_lt_two (V := V) b)

/-- Arbitrary left stack, with its head bit supplied by arithmetic remainder. -/
lemma left_row_any (q : WorkingState) (read : Bool)
    (hd : (row q read).right=false) (l t : V) :
    Step (q.val : V) l ((1+1)*t+read.toNat)
      (StepFormula.controlCode (row q read).next : V)
      (l/2) ((1+1)*((1+1)*t+(row q read).write.toNat)+l%2) := by
  rcases mod_two l with hz | ho
  · have h := left_row q read false hd (l/2) t
    have he : (1+1)*(l/2)+0=l := by simpa only [hz,one_add_one_eq_two] using div_add_mod l 2
    simpa only [Bool.toNat_false,Nat.cast_zero,he,hz] using h
  · have h := left_row q read true hd (l/2) t
    have he : (1+1)*(l/2)+1=l := by simpa only [ho,one_add_one_eq_two] using div_add_mod l 2
    simpa only [Bool.toNat_true,Nat.cast_one,he,ho] using h

/-- Exact left-headed phase: the high-level left word includes the current
head. Quotient/remainder explicitly convert it to the six-place step convention. -/
theorem segment (q : WorkingState) (read write : Bool)
    (hr : row q read=⟨write,false,some q⟩) (n l t : V) :
    ∃ qs ls rs, Segment n qs ls rs q.val
      (repeatBits n read.toNat l/2) ((1+1)*t+repeatBits n read.toNat l%2)
      q.val (l/2) ((1+1)*repeatBits n write.toNat t+l%2) := by
  rcases zero_or_succ n with rfl | ⟨k,rfl⟩
  · exact ⟨_,_,_,by simpa using segment_zero (q.val : V) (l/2) ((1+1)*t+l%2)⟩
  · obtain ⟨qs,ls,rs,hs⟩ := ScanLeft.segment q read write hr k l t
    have final := left_row_any q read (by rw [hr]) l (repeatBits k write.toNat t)
    rw [hr] at final
    simp only [StepFormula.controlCode] at final
    have joined := segment_compose hs (segment_one final)
    simpa only [repeat_succ,bit_div,bit_mod] using joined
end Models

def scanFormula (q : WorkingState) (read write : Bool) : ArithmeticSemisentence 1 :=
  “n. ∀ l t, ∃ a b u v c d, !repeatGraph a n ↑read.toNat l ∧
    !repeatGraph b n ↑write.toNat t ∧ !divDef u a 2 ∧ !remDef v a 2 ∧
    !divDef c l 2 ∧ !remDef d l 2 ∧
    ∃ qs ls rs, !segmentFormula n qs ls rs ↑q.val u ((1+1)*t+v) ↑q.val c ((1+1)*b+d)”
lemma scan_correct {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
    (q : WorkingState) (read write : Bool) (n : V) :
    (V ⊧/![n] (scanFormula q read write)) ↔
    ∀ l t : V, ∃ qs ls rs, Segment n qs ls rs q.val
      (repeatBits n read.toNat l/2) ((1+1)*t+repeatBits n read.toNat l%2)
      q.val (l/2) ((1+1)*repeatBits n write.toNat t+l%2) := by
  simp [scanFormula,repeat_defined.df,div_defined.df,rem_defined.df,segment_correct,numeral_eq_natCast]

def sentence (q : WorkingState) (read write : Bool) : ArithmeticSentence :=
  “∀ n, !(scanFormula q read write) n”

theorem pa_proves_left_phase (q : WorkingState) (read write : Bool)
    (hr : row q read=⟨write,false,some q⟩) : theory ⊢ sentence q read write := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sentence,models_iff]
  simp [scan_correct]
  exact segment (V := V) q read write hr

#print axioms segment
#print axioms pa_proves_left_phase
end PA196.Arithmetic.Machine.PA.InternalTrace.LeftPhase

