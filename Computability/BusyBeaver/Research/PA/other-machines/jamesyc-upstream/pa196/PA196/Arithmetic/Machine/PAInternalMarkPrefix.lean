module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalMarkSkipGeneric
public import PA196.Arithmetic.Machine.PAInternalMarkReturnGeneric
public import PA196.Arithmetic.Machine.PAInternalMarkDelimiter
public import PA196.Arithmetic.Machine.PAInternalReturnCode
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.MarkPrefix
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open ScanBits
attribute [local irreducible] Step StepFormula.formula
section Coding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- A fixed finite prefix of arbitrary model values; not a claim that every
model-valued HFS vector has standard length. Oracle indices are bounded by8. -/
noncomputable def file : List V → V
  | [] => 0
  | p::ps => p∷file ps
@[simp] theorem file_nil : file ([] : List V)=0 := rfl
@[simp] theorem file_cons (p : V) (ps : List V) : file (p::ps)=p∷file ps := rfl
/-- Exact bridge for a standard bounded length, with arbitrary model entries. -/
theorem of_length : ∀ (n : Nat) (xs : V), len xs=(n : V) →
    ∃ ps : List V, ps.length=n ∧ file ps=xs
  | 0,xs,h => by
    have hz : xs=0 := len_zero_iff_eq_nil.mp (by simpa using h)
    exact ⟨[],rfl,by simpa using hz.symm⟩
  | n+1,xs,h => by
    rcases nil_or_adjoin xs with hz | ⟨a,as,ha⟩
    · subst xs
      simp only [len_nil,Nat.cast_add,Nat.cast_one] at h
      have : (0 : V)<(n : V)+1 := by simp
      exact False.elim ((ne_of_gt this) h.symm)
    · subst xs
      have hn : len as=(n : V) := by
        simp only [len_adjoin,Nat.cast_add,Nat.cast_one] at h
        exact add_right_cancel h
      obtain ⟨ps,hp,he⟩ := of_length n as hn
      exact ⟨a::ps,by simp [hp],by simp [he]⟩
end Coding
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

theorem skip : ∀ (pre : List V) (m : Nat) (l t : V), pre.length+m<9 →
    ∃ qs ls rs, Segment (CarryCode.cost (file pre)) qs ls rs
      (NativeRows.code (Runtime.sk (pre.length+m))) l (CarryCode.rightFile (file pre) t)
      (NativeRows.code (Runtime.sk m)) (ReturnCode.leftFile (file pre) l) t
  | [],m,l,t,_ => by exact ⟨_,_,_,by simpa using segment_zero (NativeRows.code (Runtime.sk m) : V) l t⟩
  | p::ps,m,l,t,h => by
    have hj : ps.length+m<8 := by simp only [List.length_cons] at h; omega
    obtain ⟨qa,la,ra,ha⟩ := MarkSkipGeneric.skip_cell (ps.length+m) hj p l
      (CarryCode.rightFile (file ps) t)
    obtain ⟨qb,lb,rb,hb⟩ := skip ps m (repeatBits p 1 (4*l+1)) t (by omega)
    obtain ⟨qc,lc,rc,hc⟩ := segment_compose ha hb
    have hn : ps.length+1+m=ps.length+m+1 := by omega
    exact ⟨qc,lc,rc,by simpa only [List.length_cons,hn,file_cons,CarryCode.cost_adjoin,
      CarryCode.right_adjoin,ReturnCode.left_adjoin] using hc⟩

/-- Returning through a nonempty standard-length prefix, with arbitrary model
entries. Each unbounded unary scan is supplied by its internal induction proof. -/
theorem returning : ∀ (pre : List V) (q : WorkingState),
    row q true=⟨true,false,some ⟨3,by decide⟩⟩ → pre≠[] → ∀ l t : V,
    ∃ qs ls rs, Phase (CarryCode.cost (file pre)) qs ls rs q.val
      (ReturnCode.leftFile (file pre) l) t 4 l (CarryCode.rightFile (file pre) t)
  | [],_,_,h,_,_ => False.elim (h rfl)
  | p::ps,q,hq,_,l,t => by
    cases ps with
    | nil =>
      simpa only [file_cons,file_nil,CarryCode.cost_adjoin,CarryCode.cost_nil,
        ReturnCode.left_adjoin,ReturnCode.left_nil,CarryCode.right_adjoin,CarryCode.right_nil,
        add_zero] using MarkReturnGeneric.segment q hq p l t
    | cons a as =>
      obtain ⟨qa,la,ra,ha⟩ := returning (a::as) q hq (by simp) (repeatBits p 1 (4*l+1)) t
      obtain ⟨qb,lb,rb,hb⟩ := MarkReturnGeneric.segment (⟨4,by decide⟩ : WorkingState)
        (by rfl) p l (CarryCode.rightFile (file (a::as)) t)
      obtain ⟨qc,lc,rc,hc⟩ := segment_compose ha hb
      have ht : CarryCode.cost (file (a::as))+(p+2)=p+2+CarryCode.cost (file (a::as)) := by ring1
      rw [ht] at hc
      exact ⟨qc,lc,rc,by simpa only [Phase,file_cons,CarryCode.cost_adjoin,ReturnCode.left_adjoin,
        CarryCode.right_adjoin] using hc⟩
end Models
#print axioms skip
#print axioms returning
end PA196.Arithmetic.Machine.PA.InternalTrace.MarkPrefix

