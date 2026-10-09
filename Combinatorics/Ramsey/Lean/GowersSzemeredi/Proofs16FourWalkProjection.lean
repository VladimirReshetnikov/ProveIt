import GowersSzemeredi.Proofs16FourWalkCollisionCount

/-! Matched walk pairs project to additive endpoint quadruples with
fibres of size at most the number of internal triples. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def fourWalkEndpointTuple {N : Nat} (p : FourWalkData N × FourWalkData N) : Fin 4 → ZMod N :=
  columnPairTuple (p.1.1.1,p.2.1.1) (p.1.1.2,p.2.1.2)

/-- The endpoint quadruple and the first internal triple determine a
matched pair of walks. -/
theorem fourWalk_endpoint_internal_injOn {N : Nat} [NeZero N] (W : Finset (FourWalkData N)) :
    Set.InjOn (fun p : FourWalkData N × FourWalkData N => (fourWalkEndpointTuple p,p.1.2)) ↑(fourWalkCollisions W) := by
  intro p hp q hq heq
  have he := congrArg Prod.fst heq
  have ht := congrArg Prod.snd heq
  change p.1.2 = q.1.2 at ht
  have hu : p.1.1.1 = q.1.1.1 := congrFun he 0
  have hv : p.1.1.2 = q.1.1.2 := congrFun he 3
  have hu' : p.2.1.1 = q.2.1.1 := congrFun he 2
  have hleft : p.1 = q.1 := Prod.ext (Prod.ext hu hv) ht
  have hpsteps := (Finset.mem_filter.mp hp).2
  have hqsteps := (Finset.mem_filter.mp hq).2
  have hseq : fourWalkDataSteps p.2 = fourWalkDataSteps q.2 :=
    hpsteps.symm.trans ((congrArg fourWalkDataSteps hleft).trans hqsteps)
  change fourWalkSteps p.2.1.1 p.2.1.2 p.2.2 = fourWalkSteps q.2.1.1 q.2.1.2 q.2.2 at hseq
  rw [← hu'] at hseq
  have hsecond : (p.2.1.2,p.2.2) = (q.2.1.2,q.2.2) := fourWalkSteps_start_injective _ hseq
  have hend := congrArg Prod.fst hsecond
  have hinside := congrArg Prod.snd hsecond
  exact Prod.ext hleft (Prod.ext (Prod.ext hu' hend) hinside)

/-- At most `N^3` matched pairs have a prescribed endpoint quadruple. -/
theorem fourWalk_endpoint_image_bound {N : Nat} [NeZero N] (W : Finset (FourWalkData N)) :
    (fourWalkCollisions W).card ≤
      ((fourWalkCollisions W).image fourWalkEndpointTuple).card * N^3 := by
  have h := Finset.card_le_card_of_injOn (s := fourWalkCollisions W)
    (t := (fourWalkCollisions W).image fourWalkEndpointTuple ×ˢ
      (Finset.univ : Finset (ZMod N × ZMod N × ZMod N)))
    (fun p => (fourWalkEndpointTuple p,p.1.2))
    (fun p hp => Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp,Finset.mem_univ _⟩)
    (fourWalk_endpoint_internal_injOn W)
  simpa only [Finset.card_product, Finset.card_univ, Fintype.card_prod, ZMod.card,
    show N*(N*N) = N^3 by ring] using h

/-- A mass `mu*N^5` of walks gives `mu^2*N^3` distinct matched endpoint
quadruples. -/
theorem fourWalk_endpoint_density {N : Nat} [NeZero N] (W : Finset (FourWalkData N))
    {mu : Real} (hmu : 0 ≤ mu) (hW : mu*(N : Real)^5 ≤ W.card) :
    mu^2*(N : Real)^3 ≤ (((fourWalkCollisions W).image fourWalkEndpointTuple).card : Real) := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hmass : mu^2*(N : Real)^10 ≤ (W.card : Real)^2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ mu*(N : Real)^5) hW 2
    nlinarith [h]
  have hcollision := fourWalkCollisions_mass_bound W
  have hprojection : ((fourWalkCollisions W).card : Real) ≤
      ((fourWalkCollisions W).image fourWalkEndpointTuple).card * (N : Real)^3 := by
    exact_mod_cast fourWalk_endpoint_image_bound W
  have hbound := hmass.trans (hcollision.trans (mul_le_mul_of_nonneg_left hprojection (by positivity)))
  apply (mul_le_mul_iff_right₀ (pow_pos hn 7)).mp
  nlinarith [hbound]

end LeanProofs.GowersSzemeredi
