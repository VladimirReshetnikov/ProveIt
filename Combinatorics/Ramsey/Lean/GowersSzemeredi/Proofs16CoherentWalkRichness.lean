import GowersSzemeredi.Proofs16CoherentWalkKeyTuples

/-! Dense endpoint sets in a robust coherent graph contain many exact
mixed quadruples. The bridge error pays only for discarded collision fibres. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem CoherentBridgeSystem.mixed_quadruples_of_walks {N ell depth i : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma eta beta1 beta2 lambda : Real}
    (h : CoherentBridgeSystem B X theta F sigma eta depth) (he : 0 < eta)
    (hi : i+1 ≤ depth) (hb1 : 0 < beta1) (hb2 : 0 < beta2) (hl : 0 < lambda)
    (hsmall : 4*eta < (beta1*beta2*lambda)^2)
    (E : Finset (ZMod N × ZMod N)) (U V : Finset (ZMod N))
    (hU : beta1*N ≤ (U.card : Real)) (hV : beta2*N ≤ (V.card : Real))
    (hwalk : ∀ u ∈ U, ∀ v ∈ V, lambda*(N : Real)^3 ≤
      ((graphFourWalks (fun a b => (a,b) ∈ E) u v).card : Real))
    (hcoh : ∀ p ∈ E, ∀ q ∈ E, p.1-p.2 = q.1-q.2 →
      CoherentRelationLevel X B theta F sigma (i+1) p q) :
    (beta1*beta2*lambda)^2*(N : Real)^3/2 ≤
      ((mixedExactColumnQuadruples U V (fun u => B ∪ Finset.univ.image (fun j => theta j u))
        F (coherentRelationRadius sigma (i+3))).card : Real) := by
  let mu := beta1*beta2*lambda
  have hmu : 0 < mu := by dsimp [mu]; positivity
  have hprod := mul_le_mul hU hV (by positivity) (Nat.cast_nonneg U.card)
  have hmass : mu*(N : Real)^5 ≤ (fourWalkFamily E U V).card := by
    have hm := mul_le_mul_of_nonneg_right hprod (show 0 ≤ lambda*(N : Real)^3 by positivity)
    have hw := fourWalkFamily_mass E U V hwalk
    dsimp [mu]
    nlinarith [hm]
  let P := popularEndpointFibres (fourWalkCollisions (fourWalkFamily E U V))
    fourWalkCollisionKey (mu^2*(N : Real)^3/2)
  have hP := popular_fourWalkCollisionKeys_dense (fourWalkFamily E U V) hmu.le hmass
  have hsub : P.image coherentWalkKeyTuple ⊆ mixedExactColumnQuadruples U V
      (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F (coherentRelationRadius sigma (i+3)) := by
    intro q hq
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hq
    exact popular_coherent_walk_key_tuple h he hi hmu hsmall E U V hcoh hk
  have hcard : P.card ≤ (mixedExactColumnQuadruples U V
      (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F (coherentRelationRadius sigma (i+3))).card := by
    rw [← Finset.card_image_of_injective P coherentWalkKeyTuple_injective]
    exact Finset.card_le_card hsub
  exact hP.trans (Nat.cast_le.mpr hcard)

end LeanProofs.GowersSzemeredi
