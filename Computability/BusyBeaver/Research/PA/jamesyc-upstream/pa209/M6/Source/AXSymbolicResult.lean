module
public import M6.Source.AXSymbolic
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace M6.Source.AXSymbolic

def initial : Store := ⟨.atom 0,.atom 1,.atom 2,.atom 3,[.atom 4,.atom 5],[]⟩
/-- Literal symbolic output, not the previously conjectured PA135 specification. -/
def actualResult : Store :=
  ⟨(.im (.im (.im (.succ (.im (.add (.atom 2) (.atom 5)) (.add (.atom 3) (.atom 4)))) (.succ (.succ (.im (.atom 1) (.succ (.im (.add (.atom 2) (.atom 5)) (.add (.atom 3) (.atom 4)))))))) (.succ (.succ (.im (.atom 1) (.im (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.im (.im (.im (.succ (.im (.add (.atom 2) (.atom 5)) (.add (.atom 3) (.atom 4)))) (.im (.atom 1) (.succ (.im (.atom 1) (.add (.atom 3) (.atom 4)))))) (.im (.im (.succ (.im (.atom 1) (.add (.atom 3) (.atom 4)))) (.atom 1)) (.succ .zero))) (.succ .zero))))) (.im (.im (.atom 1) (.succ (.im (.atom 1) (.add (.atom 3) (.atom 4))))) (.succ .zero))))))) (.succ .zero)),(.atom 1),(.add (.atom 2) (.atom 5)),(.add (.atom 3) (.atom 4)),[],[(.im (.succ (.succ (.im (.add (.atom 2) (.atom 5)) (.im (.succ (.succ (.succ (.im (.add (.atom 2) (.atom 5)) (.add (.atom 3) (.atom 4)))))) (.succ .zero))))) (.succ .zero)),(.im (.succ (.succ (.im (.add (.atom 2) (.atom 5)) (.im (.add (.atom 3) (.atom 4)) (.atom 1))))) (.im (.succ (.succ (.im (.add (.atom 2) (.atom 5)) (.add (.atom 3) (.atom 4))))) (.succ (.succ (.im (.add (.atom 2) (.atom 5)) (.atom 1)))))),(.im (.succ (.succ (.succ (.im (.add (.atom 2) (.atom 5)) (.add (.atom 3) (.atom 4)))))) (.im (.succ (.im (.atom 1) (.add (.atom 2) (.atom 5)))) (.succ (.im (.atom 1) (.add (.atom 3) (.atom 4)))))),(.im (.succ (.succ (.im (.add (.atom 2) (.atom 5)) (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.atom 1))))))) (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.succ (.succ (.im (.add (.atom 2) (.atom 5)) (.atom 1)))))))),(.im (.succ (.succ (.succ (.im (.atom 1) (.add (.atom 2) (.atom 5)))))) (.im (.succ (.im (.atom 1) (.add (.atom 3) (.atom 4)))) (.succ (.im (.add (.atom 2) (.atom 5)) (.add (.atom 3) (.atom 4)))))),(.im (.im (.succ (.succ (.im (.add (.atom 2) (.atom 5)) (.im (.succ (.succ (.im (.add (.atom 2) (.atom 5)) (.add (.atom 3) (.atom 4))))) (.succ .zero))))) (.succ .zero)) (.add (.atom 3) (.atom 4))),(.im (.succ (.succ (.succ (.im (.atom 1) (.add (.atom 2) (.atom 5)))))) (.im (.succ (.succ (.succ (.im (.atom 1) (.add (.atom 3) (.atom 4)))))) (.succ (.succ (.im (.succ (.im (.add (.atom 2) (.atom 5)) (.add (.atom 3) (.atom 4)))) (.succ (.succ (.succ (.im (.add (.atom 2) (.atom 5)) (.add (.atom 3) (.atom 4))))))))))),(.im (.im (.im (.atom 1) (.atom 2)) (.add (.atom 2) (.atom 5))) (.im (.im (.add (.atom 2) (.atom 5)) (.atom 1)) (.im (.add (.atom 3) (.atom 4)) (.atom 1)))),(.succ (.succ (.im (.atom 2) (.atom 3)))),(.atom 0)]⟩

theorem program_actual : run AXMacro.program initial = some actualResult := by decide
#print axioms program_actual
end M6.Source.AXSymbolic

