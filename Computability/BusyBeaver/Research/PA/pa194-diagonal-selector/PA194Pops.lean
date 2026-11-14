import PA194Words
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194Selectors
open M6.Source.Cantor PA196.Commands PA196.Commands.Code PA194Words

def pops : Nat → List Command
  | 0 => []
  | n+1 => pop ++ pops n

theorem pops_stack (xs : List Nat) (t a w d h : Nat) :
    PA194Words.run (pops (xs.length+1)) ⟨t,(xs++[a]).foldr pair w,d,h⟩ = some ⟨t,w,0,a⟩ := by
  induction xs generalizing d h with
  | nil =>
    simpa only [List.length_nil,Nat.zero_add,pops,List.append_nil,
      List.nil_append,List.foldr_cons,List.foldr_nil] using pop_total t a w d h
  | cons x xs ih =>
    simp only [List.length_cons,List.cons_append,List.foldr_cons,pops,PA194Words.run_append,pop_total,Option.bind_some]
    simpa only [pops,PA194Words.run_append] using ih 0 x


#print axioms pops_stack
end PA194Selectors
