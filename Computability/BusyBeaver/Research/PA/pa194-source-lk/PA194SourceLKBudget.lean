import PA194SourceLKBase
import PA194RelationalSourceGeneralization
import PA194RelationalSourceCode
namespace PA194Logic.Relational.Source
open LO LO.FirstOrder M6.PA.RelationalSource
deriving instance DecidableEq for Relation
instance : language.DecidableEq where
  func _ := inferInstanceAs (DecidableEq Empty)
  rel k := inferInstanceAs (DecidableEq (Relation k))

theorem depth_rew {ξ η : Type} {n m : Nat} (p : Semiformula language ξ n)
    (ω : Rew language ξ n η m) : depth (Semiformula.rewAux ω p) = depth p := by
  induction p generalizing η m <;> simp_all [Semiformula.rewAux,depth]

def sequentDepth (Γ : SourceSequent) : Nat :=
  (Γ.map depth).foldr max 0

theorem depth_le_sequentDepth {Γ : SourceSequent} {p : Proposition language}
    (h : p ∈ Γ) : depth p ≤ sequentDepth Γ := by
  induction Γ using Multiset.induction_on with
  | empty => simp at h
  | @cons q Γ ih =>
    simp only [sequentDepth,Multiset.map_cons,Multiset.foldr_cons]
    rcases Multiset.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact (ih h).trans (Nat.le_max_right _ _)

def lkBudget {Γ : SourceSequent} (d : SourceLK Γ) : Nat :=
  max (sequentDepth Γ + 1) (match d with
    | .identity _ _ => 1
    | .cut p q => max (lkBudget p) (lkBudget q)
    | .contraction p => lkBudget p
    | .weakening p => lkBudget p
    | .verum => 1
    | .or p => lkBudget p
    | .and p q => max (lkBudget p) (lkBudget q)
    | .all p => lkBudget p + 1
    | .exs p => lkBudget p + 1)

theorem depth_lt_lkBudget {Γ : SourceSequent} (d : SourceLK Γ)
    {p : Proposition language} (h : p ∈ Γ) : depth p < lkBudget d :=
  by
    unfold lkBudget
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (depth_le_sequentDepth h)) (Nat.le_max_left _ _)

end PA194Logic.Relational.Source
