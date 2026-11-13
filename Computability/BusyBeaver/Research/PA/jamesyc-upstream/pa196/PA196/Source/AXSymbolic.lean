module
public import PA196.Source.AXProgram
public import PA196.Commands.Code
public import M6.Source.AXSymbolic
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Source.AXSymbolic
open M6.Source
open M6.Source.AXSymbolic

def initial : Store := ⟨.atom 0,.atom 1,.atom 2,.atom 3,[.atom 4,.atom 5],[]⟩

/-- The symbolic expression trees obtained from the new PA196 macro sequence. -/
def result : Store :=
  ⟨(.im (.im (.im (.succ (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5)))))) (.succ (.succ (.im (.succ (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5)))))) (.atom 1))))) (.im (.im (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5)))) (.succ (.succ (.im (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5)))) (.atom 1))))) (.succ (.succ (.im (.im (.succ (.succ (.im (.im (.im (.im (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5)))) (.im (.atom 1) (.succ (.im (.atom 1) (.add (.atom 2) (.atom 5)))))) (.im (.im (.succ (.im (.atom 1) (.add (.atom 2) (.atom 5)))) (.atom 1)) (.succ .zero))) (.succ .zero)) (.add (.atom 2) (.atom 5))))) (.im (.im (.atom 1) (.succ (.im (.atom 1) (.add (.atom 2) (.atom 5))))) (.succ .zero))) (.atom 1)))))) (.succ .zero)),(.atom 1),(.add (.atom 2) (.atom 5)),(.add (.atom 3) (.atom 4)),[],[(.im (.succ (.succ (.im (.atom 1) (.add (.atom 2) (.atom 5))))) (.im (.succ (.succ (.im (.im (.atom 1) (.add (.atom 3) (.atom 4))) (.add (.atom 2) (.atom 5))))) (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5))))))),(.im (.succ (.succ (.im (.im (.succ (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5)))))) (.succ .zero)) (.add (.atom 2) (.atom 5))))) (.succ .zero)),(.im (.succ (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5)))))) (.im (.succ (.im (.atom 1) (.add (.atom 3) (.atom 4)))) (.succ (.im (.atom 1) (.add (.atom 2) (.atom 5)))))),(.im (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5)))) (.im (.succ (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.atom 1))))) (.succ (.im (.atom 1) (.add (.atom 2) (.atom 5)))))),(.im (.succ (.succ (.im (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.atom 1)))) (.add (.atom 2) (.atom 5))))) (.succ (.succ (.im (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5))))) (.atom 1))))),(.im (.im (.succ (.succ (.im (.im (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5))))) (.succ .zero)) (.add (.atom 2) (.atom 5))))) (.succ .zero)) (.add (.atom 3) (.atom 4))),(.im (.im (.im (.add (.atom 3) (.atom 4)) (.atom 2)) (.add (.atom 2) (.atom 5))) (.im (.im (.add (.atom 2) (.atom 5)) (.add (.atom 3) (.atom 4))) (.im (.atom 1) (.add (.atom 3) (.atom 4))))),(.succ (.succ (.im (.atom 3) (.atom 2)))),(.atom 0)]⟩

theorem program_symbolic : run AXProgram.program initial = some result := by
  decide +kernel

def valuation (t c d h y x : Nat) : Fin 6 → Nat :=
  fun i => [t,c,d,h,y,x][i.val]!

/-- The computed expression trees have precisely the paper's transposed
quantifier encoding, new head order, and equality-vacuity gate. -/
theorem result_spec (t c d h y x tail : Nat) :
    materialize (valuation t c d h y x) tail result =
      ⟨PA196.Commands.Code.bundle (h+y) (d+x) c,c,d+x,h+y,tail,
        PA196.Commands.Code.heads (d+x) (h+y) c d h ++ [t]⟩ := by
  rfl

/-- Uniform arithmetic evaluation; the primitive source binding is proved
separately by the certified macro plan. -/
theorem macro_result (t c d h y x tail : Nat) :
    AXMacro.run AXProgram.program ⟨t,c,d,h,Cantor.pair y (Cantor.pair x tail),[]⟩ =
      some ⟨PA196.Commands.Code.bundle (h+y) (d+x) c,c,d+x,h+y,tail,
        PA196.Commands.Code.heads (d+x) (h+y) c d h ++ [t]⟩ := by
  have h := run_sound AXProgram.program initial result program_symbolic
    (valuation t c d h y x) tail
  rw [result_spec] at h
  exact h

#print axioms program_symbolic
#print axioms macro_result
end PA196.Source.AXSymbolic
