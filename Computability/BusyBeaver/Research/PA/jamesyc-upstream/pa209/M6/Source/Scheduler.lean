module
public import M6.Source.EnumerationSchedule
public import M6.Source.FetchDispatch
@[expose] public section
namespace M6.Source.Scheduler
open Enumeration

/-- An actual N/L frontier in the deterministic command schedule. Empty L is
exactly a word boundary; positive L contains the residual encoded command word. -/
def Frontier (n l : Nat) (history : List Command) : Prop :=
  (l = 0 ∧ history = schedule n) ∨
  ∃ k p, n = k+1 ∧ 0 < l ∧ history = schedule k ++ p ∧ word k = p ++ residual l

theorem initial : Frontier 0 0 [] := Or.inl ⟨rfl,rfl⟩

theorem history_prefix (hf : Frontier n l history) :
    ∃ k p rest, history = schedule k ++ p ∧ word k = p ++ rest := by
  rcases hf with ⟨hl,rfl⟩ | ⟨k,p,hn,hl,hh,hw⟩
  · exact ⟨n,[],word n,by simp,rfl⟩
  · exact ⟨k,p,residual l,hh,hw⟩

private theorem after_prefix (k : Nat) (p : List Command) (next : Nat)
    (hword : word k = p ++ residual next) :
    Frontier (k+1) next (schedule k ++ p) := by
  by_cases hz : next = 0
  · left
    refine ⟨hz,?_⟩
    have he : word k = p := by simpa only [hz,residual,List.append_nil] using hword
    rw [schedule_succ,he]
  · right
    exact ⟨k,p,rfl,by omega,rfl,hword⟩

/-- The exact fresh/positive pointer convention advances one parsed command
and appends precisely that command to the schedule history. -/
theorem advance (hf : Frontier n l history) :
    Frontier (FetchDispatch.nextN n l) (parse (FetchDispatch.seed n l)).next
      (history ++ [(parse (FetchDispatch.seed n l)).command]) := by
  rcases hf with ⟨hl,rfl⟩ | ⟨k,p,rfl,hl,rfl,hw⟩
  · subst l
    simp only [FetchDispatch.nextN,FetchDispatch.seed,↓reduceIte]
    apply after_prefix n [(parse n).command] (parse n).next
    rfl
  · have hz : l ≠ 0 := by omega
    simp only [FetchDispatch.nextN,FetchDispatch.seed,hz,↓reduceIte]
    have he : residual l = (parse (l-1)).command :: residual (parse (l-1)).next := by
      have hl' : l = (l-1)+1 := by omega
      rw [hl',residual]
      simp only [Nat.add_sub_cancel]
    rw [he] at hw
    rw [List.append_assoc]
    apply after_prefix k (p++[(parse (l-1)).command]) (parse (l-1)).next
    simpa only [List.append_assoc,List.singleton_append] using hw

#print axioms advance
end M6.Source.Scheduler

