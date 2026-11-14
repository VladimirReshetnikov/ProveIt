import PA194AXOnce
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PA194HeadShape
open M6.Source.Cantor PA196.Commands.Code
attribute [local irreducible] M6.Source.Cantor.pair PA194AXSymbolic.diagonal

def remaining (D H A d h : Nat) : List Nat :=
 [head5 D H,head4 D A H,head3 D A H,head2 D A H,head1 D H,rho8 D A H d,U d h]

@[simp] theorem remaining_length (D H A d h : Nat) : (remaining D H A d h).length = 7 := rfl

theorem shape (D H A d h t w : Nat) :
    ([PA194AXSymbolic.diagonal A] ++ heads D H A d h ++ [t]).foldr pair w =
    pair (PA194AXSymbolic.diagonal A) (pair (head6 D A H) ((remaining D H A d h ++ [t]).foldr pair w)) := by
  unfold heads remaining
  rfl

#print axioms shape
end PA194HeadShape
