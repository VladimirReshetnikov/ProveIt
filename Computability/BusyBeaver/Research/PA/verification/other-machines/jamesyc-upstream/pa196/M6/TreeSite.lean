module
public import M6.FastResolve
@[expose] public section

namespace M6.Source.PathTrie
/-- Ordinal lookup that returns the exact leaf path and operation without expanding the flattened list. -/
def nthSite : Tree → Nat → Option Site
  | .leaf op, i => if i=0 then some ⟨[],op⟩ else none
  | .node l r, i => if i < size l then (nthSite l i).map (prepend false)
      else (nthSite r (i-size l)).map (prepend true)

theorem nthSite_eq (t : Tree) (i : Nat) : nthSite t i = (flatten t)[i]? := by
  induction t generalizing i with
  | leaf op => cases i <;> simp [nthSite,flatten]
  | node l r hl hr =>
    simp only [nthSite,flatten,List.getElem?_append,List.length_map,length_flatten]
    split <;> simp_all only [List.getElem?_map]
#print axioms nthSite_eq
end M6.Source.PathTrie
