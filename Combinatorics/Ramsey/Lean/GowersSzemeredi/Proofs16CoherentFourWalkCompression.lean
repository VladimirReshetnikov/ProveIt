import GowersSzemeredi.Proofs16FourWalkCompressionBound
import GowersSzemeredi.Proofs16CoherentCommonNeighbours

/-! Many four-walks in a difference relation imply an endpoint identity
with only two further factor-six radius losses. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem CoherentBridgeSystem.four_walks {N ell depth i : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma eta : Real}
    (h : CoherentBridgeSystem B X theta F sigma eta depth) (he : 0 < eta)
    (hi : i+1 ≤ depth) (a u v : ZMod N)
    (hmass : 2*eta*(N : Real)^3 < ((graphFourWalks
      (fun x y => CoherentRelationLevel X B theta F sigma (i+1) (x+a,x) (y+a,y)) u v).card : Real)) :
    CoherentRelationLevel X B theta F sigma (i+3) (u+a,u) (v+a,v) := by
  let G := fun x y => CoherentRelationLevel X B theta F sigma (i+1) (x+a,x) (y+a,y)
  let H := fun x y => CoherentRelationLevel X B theta F sigma (i+2) (x+a,x) (y+a,y)
  by_contra hn
  have hsmall : ((graphCommonNeighbours H u v).card : Real) ≤ eta*N := by
    apply (lt_of_not_ge ?_).le
    intro hm
    exact hn (by simpa only [Nat.add_assoc] using h.common_neighbours he hi a u v hm)
  have hbound := graph_four_walks_le_of_small_common G H
    (fun _ _ hg => hg.symm) (by positivity : 0 ≤ eta*(N : Real))
    (fun x y hm => h.common_neighbours he (by omega : i ≤ depth) a x y hm) u v hsmall
  simp only [ZMod.card] at hbound
  have heq : 2*(eta*(N : Real))*(N : Real)^2 = 2*eta*(N : Real)^3 := by ring
  rw [heq] at hbound
  exact (not_lt_of_ge hbound) hmass

end LeanProofs.GowersSzemeredi
