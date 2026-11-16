import PA194SymbolicTrace
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace PA194SymbolicChecker
open PA194BidirectionalRow PA194SymbolicTrace

structure Row where
  write : Bool
  right : Bool
  next : Nat
  deriving Repr, DecidableEq

def checkStep (s : Config) (row : Row) : Option Config :=
  match s.right with
  | [] => none
  | b::rs =>
    if s.q < 194 ∧ PA194Rows.rows.getD (s.q+s.q+bit b) (0,0,194) = (bit row.write,bit row.right,row.next) then
      if row.right then some ⟨row.next,row.write::s.left,rs⟩
      else match s.left with
        | [] => none
        | a::ls => some ⟨row.next,ls,a::row.write::rs⟩
    else none

theorem stepSound (s t : Config) (row : Row) (h : checkStep s row = some t) : Step s t := by
  rcases s with ⟨q,ls,rt⟩
  rcases row with ⟨w,d,next⟩
  cases rt with
  | nil => simp [checkStep] at h
  | cons b rs =>
    simp only [checkStep] at h
    split at h
    next hc =>
      rcases hc with ⟨hq,hrow⟩
      cases d with
      | false =>
        cases ls with
        | nil => simp at h
        | cons a rest =>
          simp at h
          subst t
          apply Step.left q next a b w rest rs hq
          simpa [bit] using hrow
      | true =>
        simp at h
        subst t
        apply Step.right q next b w ls rs hq
        simpa [bit] using hrow
    next hc => simp at h

def checkRun : Config → List Row → Option Config
  | s, [] => some s
  | s, row::rows => (checkStep s row).bind (fun mid => checkRun mid rows)

theorem runSound (rows : List Row) (s t : Config) (h : checkRun s rows = some t) : Run s t rows.length := by
  induction rows generalizing s with
  | nil =>
    simp [checkRun] at h
    subst t
    exact Run.nil _
  | cons row rows ih =>
    simp only [checkRun] at h
    cases hs : checkStep s row with
    | none => simp [hs] at h
    | some mid =>
      simp [hs] at h
      exact Run.cons s mid t rows.length (stepSound s mid row hs) (ih mid h)
#print axioms stepSound
#print axioms runSound
end PA194SymbolicChecker
