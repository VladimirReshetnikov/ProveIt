import GowersSzemeredi.Proofs16CoherentRelationLevels
import GowersSzemeredi.Proofs16GraphCommonCodegrees

/-! A sufficiently large common neighborhood advances one relation level.
The membership data come from actual bridges, not from extra assumptions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem CoherentBridgeSystem.common_neighbours {N ell depth i : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma eta : Real}
    (h : CoherentBridgeSystem B X theta F sigma eta depth) (he : 0 < eta)
    (hi : i ≤ depth) (a u v : ZMod N)
    (hmass : eta*N ≤ ((graphCommonNeighbours
      (fun x y => CoherentRelationLevel X B theta F sigma (i+1) (x+a,x) (y+a,y)) u v).card : Real)) :
    CoherentRelationLevel X B theta F sigma (i+2) (u+a,u) (v+a,v) := by
  let G := fun x y => CoherentRelationLevel X B theta F sigma (i+1) (x+a,x) (y+a,y)
  let Z := graphCommonNeighbours G u v
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hne : Z.Nonempty := Finset.card_pos.mp (by exact_mod_cast (mul_pos he hN).trans_le hmass)
  obtain ⟨z,hz⟩ := hne
  have hbridge (z : ZMod N) (hz : z ∈ Z) : G u z ∧ G v z := (Finset.mem_filter.mp hz).2
  have hends := hbridge z hz
  have hZ : Z ⊆ X := fun z hz => (hbridge z hz).1.2.1.2
  have hza : ∀ z ∈ Z, z+a ∈ X := fun z hz => (hbridge z hz).1.2.1.1
  have hcomp := h i hi Z u v a hZ hmass hends.1.1.2 hends.1.1.1 hends.2.1.2 hends.2.1.1 hza (by
    intro z hz
    have h₁ := (hbridge z hz).1.2.2.2
    have h₂ := (CoherentRelationLevel.symm (hbridge z hz).2).2.2.2
    exact ⟨by simpa only [coherentRelationRadius,Nat.add_sub_cancel] using h₁,
      by simpa only [coherentRelationRadius,Nat.add_sub_cancel] using h₂⟩)
  refine ⟨hends.1.1,hends.2.1,by simp,?_⟩
  have heq : coherentRelationRadius sigma (i+2) = (sigma/(6 : Real)^i)/6 := by
    unfold coherentRelationRadius
    rw [show i+2-1 = i+1 by omega,pow_succ,div_div]
  rw [heq]
  exact hcomp

end LeanProofs.GowersSzemeredi
