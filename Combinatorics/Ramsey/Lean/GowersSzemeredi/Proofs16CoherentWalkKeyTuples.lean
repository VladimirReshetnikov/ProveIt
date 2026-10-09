import GowersSzemeredi.Proofs16MatchedCoherentWalks
import GowersSzemeredi.Proofs16PopularWalkCollisionKeys
import GowersSzemeredi.Proofs16WalkAdditiveRichness

/-! Popular matched-walk keys give distinct mixed coherent endpoint
quadruples at a constant-factor smaller radius. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def coherentWalkKeyTuple {N : Nat} (k : ZMod N × ZMod N × ZMod N) : Fin 4 → ZMod N :=
  ![k.1,k.2.2,k.2.1,k.2.2+(k.1-k.2.1)]

theorem coherentWalkKeyTuple_injective {N : Nat} : Function.Injective (@coherentWalkKeyTuple N) := by
  intro k l h
  have h0 : k.1 = l.1 := congrFun h 0
  have h1 : k.2.1 = l.2.1 := congrFun h 2
  have h2 : k.2.2 = l.2.2 := congrFun h 1
  exact Prod.ext h0 (Prod.ext h1 h2)

theorem popular_coherent_walk_key_tuple {N ell depth i : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma eta mu : Real}
    (h : CoherentBridgeSystem B X theta F sigma eta depth) (he : 0 < eta)
    (hi : i+1 ≤ depth) (hmu : 0 < mu) (hsmall : 4*eta < mu^2)
    (E : Finset (ZMod N × ZMod N)) (U V : Finset (ZMod N))
    (hcoh : ∀ p ∈ E, ∀ q ∈ E, p.1-p.2 = q.1-q.2 →
      CoherentRelationLevel X B theta F sigma (i+1) p q)
    {k : ZMod N × ZMod N × ZMod N}
    (hk : k ∈ popularEndpointFibres (fourWalkCollisions (fourWalkFamily E U V))
      fourWalkCollisionKey (mu^2*(N : Real)^3/2)) :
    coherentWalkKeyTuple k ∈ mixedExactColumnQuadruples U V
      (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F (coherentRelationRadius sigma (i+3)) := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hmass : mu^2*(N : Real)^3/2 ≤
      ((fourWalkCollisionFibre (fourWalkFamily E U V) k).card : Real) := (Finset.mem_filter.mp hk).2
  have hwalk := Nat.cast_le (α := Real).mpr (coherent_collision_fibre_le_walks X B theta F sigma E U V hcoh k)
  have hlt : 2*eta*(N : Real)^3 < mu^2*(N : Real)^3/2 := by
    have hm := mul_lt_mul_of_pos_right hsmall (pow_pos hn 3)
    nlinarith only [hm]
  have hrel := h.four_walks he hi (k.1-k.2.1) k.2.1 k.2.2 (hlt.trans_le (hmass.trans hwalk))
  obtain ⟨p,hp,hkey⟩ := Finset.mem_image.mp (popular_endpoint_mem_image _ _ (by positivity) hk)
  obtain ⟨hpW,hsteps⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hpW
  have h1 := Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp1).1).1
  have h2 := Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp2).1).1
  dsimp only [fourWalkCollisionKey] at hkey
  have hk0 : p.1.1.1 = k.1 := congrArg (fun k : ZMod N × ZMod N × ZMod N => k.1) hkey
  have hk1 : p.2.1.1 = k.2.1 := congrArg (fun k => k.2.1) hkey
  have hk2 : p.2.1.2 = k.2.2 := congrArg (fun k => k.2.2) hkey
  have hdiff := ((fourWalkSteps_equal_iff _ _ _ _ _ _).mp hsteps).2.2.2
  have hend : p.1.1.2 = k.2.2+(k.1-k.2.1) := by
    rw [hk0,hk1,hk2] at hdiff
    linear_combination -hdiff
  have hu : k.2.1+(k.1-k.2.1) = k.1 := by ring
  have hU0 : k.1 ∈ U := hk0 ▸ h1.1
  have hU1 : k.2.1 ∈ U := hk1 ▸ h2.1
  have hV0 : k.2.2 ∈ V := hk2 ▸ h2.2
  have hV1 : k.2.2+(k.1-k.2.1) ∈ V := hend ▸ h1.2
  have hrel' : ColumnPairRelated (U ∪ V)
      (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F (coherentRelationRadius sigma (i+3))
      (k.1,k.2.1) (k.2.2+(k.1-k.2.1),k.2.2) := by
    rw [hu] at hrel
    exact ⟨⟨Finset.mem_union_left _ hU0,Finset.mem_union_left _ hU1⟩,
      ⟨Finset.mem_union_right _ hV1,Finset.mem_union_right _ hV0⟩,hrel.2.2⟩
  refine Finset.mem_filter.mpr ⟨?_,hU0,hU1,hV0,hV1⟩
  exact (columnPairRelated_iff_exact _ _ _ _ _ _).mp hrel'

end LeanProofs.GowersSzemeredi
