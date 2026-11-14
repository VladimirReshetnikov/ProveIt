import PA194DepthPR
import PA194FoundationLKList
namespace PA194BudgetSkeleton
open LO LO.FirstOrder M6.PA.RelationalSource
open PA194Logic.Relational.Source PA194DepthPR

inductive Tree where
  | leaf : Nat → Tree
  | unary : Nat → Bool → Tree → Tree
  | binary : Nat → Tree → Tree → Tree

def treeOf {Γ : List (Proposition language)} (d : LO.FirstOrder.Derivation Γ) : Tree :=
  let k := sequentDepth (Γ : SourceSequent) + 1
  match d with
  | .identity _ _ => .leaf k
  | .verum => .leaf k
  | .cut p q => .binary k (treeOf p) (treeOf q)
  | .contraction p _ => .unary k false (treeOf p)
  | .or p => .unary k false (treeOf p)
  | .and p q => .binary k (treeOf p) (treeOf q)
  | .all p => .unary k true (treeOf p)
  | .exs p => .unary k true (treeOf p)

def budget : Tree → Nat
  | .leaf k => max k 1
  | .unary k false t => max k (budget t)
  | .unary k true t => max k (budget t + 1)
  | .binary k l r => max k (max (budget l) (budget r))

theorem treeOf_correct {Γ : List (Proposition language)} (d : LO.FirstOrder.Derivation Γ) :
    budget (treeOf d) = listFoundationBudget d := by
  induction d with
  | identity | verum => rfl
  | cut p q ihp ihq | and p q ihp ihq => simp [treeOf, budget, listFoundationBudget, ihp, ihq]
  | contraction p hs ih | or p ih | all p ih | exs p ih => simp [treeOf, budget, listFoundationBudget, ih]

def treeCode : Tree → Nat
  | .leaf k => Nat.pair 0 k + 1
  | .unary k false t => Nat.pair 1 (Nat.pair k (treeCode t)) + 1
  | .unary k true t => Nat.pair 2 (Nat.pair k (treeCode t)) + 1
  | .binary k l r => Nat.pair 3 (Nat.pair k (Nat.pair (treeCode l) (treeCode r))) + 1

def budgetCode : Nat → Nat
  | 0 => 0
  | e+1 =>
    let tag := e.unpair.1
    let data := e.unpair.2
    if tag = 0 then max data 1
    else if tag = 1 then max data.unpair.1 (budgetCode data.unpair.2)
    else if tag = 2 then max data.unpair.1 (budgetCode data.unpair.2 + 1)
    else if tag = 3 then max data.unpair.1
      (max (budgetCode data.unpair.2.unpair.1) (budgetCode data.unpair.2.unpair.2))
    else 0
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_of_le (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _))
  · exact Nat.lt_succ_of_le (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _))
  · exact Nat.lt_succ_of_le (le_trans (Nat.unpair_left_le _) (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)))
  · exact Nat.lt_succ_of_le (le_trans (Nat.unpair_right_le _) (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)))

theorem budgetCode_correct (t : Tree) : budgetCode (treeCode t) = budget t := by
  induction t with
  | leaf k => simp [treeCode, budgetCode, budget]
  | unary k b t ih => cases b <;> simp [treeCode, budgetCode, budget, ih]
  | binary k l r ihl ihr => simp [treeCode, budgetCode, budget, ihl, ihr]

theorem coded_treeOf_correct {Γ : List (Proposition language)} (d : LO.FirstOrder.Derivation Γ) :
    budgetCode (treeCode (treeOf d)) = listFoundationBudget d := by
  rw [budgetCode_correct, treeOf_correct]

def budgetStep (tab : List Nat) : Nat :=
  let n := tab.length
  if n = 0 then 0 else
    let e := n-1
    let tag := e.unpair.1
    let data := e.unpair.2
    if tag = 0 then max data 1
    else if tag = 1 then max data.unpair.1 (tab.getD data.unpair.2 0)
    else if tag = 2 then max data.unpair.1 (tab.getD data.unpair.2 0 + 1)
    else if tag = 3 then max data.unpair.1
      (max (tab.getD data.unpair.2.unpair.1 0) (tab.getD data.unpair.2.unpair.2 0))
    else 0

theorem budgetStep_primrec : Primrec budgetStep := by
  let len : List Nat → Nat := List.length
  let tag : List Nat → Nat := fun tab => (len tab - 1).unpair.1
  let data : List Nat → Nat := fun tab => (len tab - 1).unpair.2
  have plen : Primrec len := Primrec.list_length
  have ptag : Primrec tag := (Primrec.fst.comp (Primrec.unpair.comp Primrec.pred)).comp plen
  have pdata : Primrec data := (Primrec.snd.comp (Primrec.unpair.comp Primrec.pred)).comp plen
  have pu : Primrec (fun tab : List Nat => (data tab).unpair) := Primrec.unpair.comp pdata
  have pnode : Primrec (fun tab : List Nat => (data tab).unpair.1) := Primrec.fst.comp pu
  have ptail : Primrec (fun tab : List Nat => (data tab).unpair.2) := Primrec.snd.comp pu
  have pchild : Primrec (fun tab : List Nat => tab.getD (data tab).unpair.2 0) :=
    Primrec.list_getD 0 |>.comp Primrec.id ptail
  have pleft : Primrec (fun tab : List Nat => tab.getD (data tab).unpair.2.unpair.1 0) :=
    Primrec.list_getD 0 |>.comp Primrec.id (Primrec.fst.comp (Primrec.unpair.comp ptail))
  have pright : Primrec (fun tab : List Nat => tab.getD (data tab).unpair.2.unpair.2 0) :=
    Primrec.list_getD 0 |>.comp Primrec.id (Primrec.snd.comp (Primrec.unpair.comp ptail))
  exact Primrec.ite (Primrec.eq.comp plen (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp ptag (Primrec.const 0)) (Primrec.nat_max.comp pdata (Primrec.const 1))
      (Primrec.ite (Primrec.eq.comp ptag (Primrec.const 1)) (Primrec.nat_max.comp pnode pchild)
        (Primrec.ite (Primrec.eq.comp ptag (Primrec.const 2)) (Primrec.nat_max.comp pnode (Primrec.succ.comp pchild))
          (Primrec.ite (Primrec.eq.comp ptag (Primrec.const 3))
            (Primrec.nat_max.comp pnode (Primrec.nat_max.comp pleft pright)) (Primrec.const 0)))))

theorem budgetStep_correct (n : Nat) :
    budgetStep ((List.range n).map budgetCode) = budgetCode n := by
  cases n with
  | zero => simp [budgetStep, budgetCode]
  | succ e =>
    have hget (j : Nat) (hj : j < e+1) :
        ((List.range (e+1)).map budgetCode).getD j 0 = budgetCode j := by
      rw [List.getD_eq_getElem _ _ (by simpa using hj)]
      simp [List.getElem_map, List.getElem_range]
    have hdata : e.unpair.2 < e+1 := Nat.lt_succ_of_le (Nat.unpair_right_le e)
    have hchild : e.unpair.2.unpair.2 < e+1 := lt_of_le_of_lt (Nat.unpair_right_le _) hdata
    have hleft : e.unpair.2.unpair.2.unpair.1 < e+1 := lt_of_le_of_lt (Nat.unpair_left_le _) hchild
    have hright : e.unpair.2.unpair.2.unpair.2 < e+1 := lt_of_le_of_lt (Nat.unpair_right_le _) hchild
    simp only [budgetStep, List.length_map, List.length_range, Nat.succ_ne_zero, if_false,
      Nat.succ_sub_one, hget _ hchild, hget _ hleft, hget _ hright]
    rw [budgetCode]

theorem budgetCode_primrec : Primrec budgetCode := by
  have hg : Primrec₂ (fun (_ : Unit) (tab : List Nat) => some (budgetStep tab)) :=
    Primrec.option_some.comp (budgetStep_primrec.comp Primrec.snd)
  have h : Primrec₂ (fun (_ : Unit) (n : Nat) => budgetCode n) :=
    Primrec.nat_strong_rec _ hg (fun _ n => by simp only [budgetStep_correct])
  exact h.comp (Primrec.const ()) Primrec.id

#print axioms budgetCode_primrec
#print axioms budgetStep_correct
#print axioms budgetStep_primrec
#print axioms coded_treeOf_correct
#print axioms budgetCode_correct
#print axioms treeOf_correct
end PA194BudgetSkeleton
