module
public import M6.Source.Syntax
set_option linter.unusedSimpArgs false
@[expose] public section

namespace M6.Source.PathTrie

inductive Tree where
  | leaf (op : Op)
  | node (left right : Tree)

def prepend (b : Bool) (s : Site) : Site := ⟨b::s.path,s.op⟩
def flatten : Tree → List Site
  | .leaf op => [⟨[],op⟩]
  | .node l r => (flatten l).map (prepend false) ++ (flatten r).map (prepend true)
def size : Tree → Nat
  | .leaf _ => 1
  | .node l r => size l + size r

def lookup : Tree → Path → Option Nat
  | .leaf _,p => if p.all (· == false) then some 0 else none
  | .node _ _,[] => some 0
  | .node l _,false::p => lookup l p
  | .node l r,true::p => (size l + ·) <$> lookup r p

private theorem find_append (p : Path) (xs ys : List Site) :
    findSite p (xs++ys) = match findSite p xs with
      | some i => some i
      | none => (xs.length+·) <$> findSite p ys := by
  induction xs with
  | nil => simp [findSite]
  | cons s xs ih =>
    simp only [List.cons_append,findSite,List.length_cons]
    split
    · rfl
    · rw [ih]
      cases hx : findSite p xs <;> cases hy : findSite p ys <;> simp [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

private theorem find_same (b : Bool) (p : Path) (xs : List Site) :
    findSite (b::p) (xs.map (prepend b)) = findSite p xs := by
  induction xs with
  | nil => rfl
  | cons s xs ih =>
    simp only [List.map_cons,findSite,prepend,List.isPrefixOf_cons_cons,
      beq_self_eq_true,Bool.true_and,List.length_cons,List.drop_succ_cons,ih]

private theorem find_other (b : Bool) (p : Path) (xs : List Site) :
    findSite ((!b)::p) (xs.map (prepend b)) = none := by
  induction xs with
  | nil => rfl
  | cons s xs ih =>
    cases b <;> simp_all [List.map_cons,findSite,prepend,List.isPrefixOf_cons_cons]

theorem length_flatten (t : Tree) : (flatten t).length = (size t) := by
  induction t <;> simp_all [flatten,size]
private theorem flatten_ne_nil (t : Tree) : (flatten t) ≠ [] := by
  induction t with
  | leaf => simp [flatten]
  | node l r hl hr => simp_all [flatten]
private theorem find_empty (xs : List Site) (h : xs ≠ []) : findSite [] xs = some 0 := by
  cases xs with
  | nil => contradiction
  | cons s xs => simp [findSite]

/-- Verified binary path traversal, exactly preserving the existing
leftmost-prefix and zero-extension lookup semantics. -/
theorem lookup_eq (t : Tree) (p : Path) : lookup t p = findSite p (flatten t) := by
  induction t generalizing p with
  | leaf op =>
    cases p with
    | nil => rfl
    | cons b p => simp [lookup,flatten,findSite]
  | node l r hl hr =>
    cases p with
    | nil => exact (find_empty _ (flatten_ne_nil (.node l r))).symm
    | cons b p =>
      cases b with
      | false =>
        simp only [lookup,flatten,find_append,find_same,← hl]
        have hn := find_other true p (flatten r)
        simp only [Bool.not_true] at hn
        rw [hn]
        cases lookup l p <;> rfl
      | true =>
        simp only [lookup,flatten,find_append]
        have hn := find_other false p (flatten l)
        simp only [Bool.not_false] at hn
        rw [hn,find_same,List.length_map,length_flatten,← hr]

#print axioms lookup_eq
end M6.Source.PathTrie

