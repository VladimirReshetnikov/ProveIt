import PA194Pops
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PA194RhoSelector
open M6.Source.Cantor PA196.Commands PA196.Commands.Code PA194Words PA194Selectors
attribute [local irreducible] PA194Words.pop PA194Words.discard PA194Words.run M6.Source.Cantor.pair

def selectRho8 (a b c u : Nat) : List Command :=
  (discard ++ offset u) ++ ([.ax b (a-u) c] ++ List.replicate 9 .shift) ++ pop

theorem selectRho8_total (a b c u t w : Nat) (hu : u ≤ a) :
    PA194Words.run (selectRho8 a b c u) ⟨t,w,0,0⟩ = some ⟨rho8 a b c u,w,0,0⟩ := by
  have hadd : u + (a-u) = a := by omega
  have hx := ax_shift9 b (a-u) c 0 w u 0
  simp only [Nat.zero_add,hadd] at hx
  exact append_total (append_total (append_total (discard_total t w) (offset_total u w)) hx)
    (pop_total (rho8 a b c u) 0 w 0 (U u 0))

#print axioms selectRho8_total
end PA194RhoSelector
