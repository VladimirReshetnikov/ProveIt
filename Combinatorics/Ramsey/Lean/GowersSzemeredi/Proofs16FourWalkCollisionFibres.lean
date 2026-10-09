import GowersSzemeredi.Proofs16FourWalkProjection

/-! Three endpoint coordinates index matched-walk fibres. The second
internal triple determines the entire matched pair in each fibre. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def fourWalkCollisionKey {N : Nat} (p : FourWalkData N × FourWalkData N) :
    ZMod N × ZMod N × ZMod N := (p.1.1.1,p.2.1.1,p.2.1.2)

def fourWalkCollisionFibre {N : Nat} [NeZero N] (W : Finset (FourWalkData N))
    (k : ZMod N × ZMod N × ZMod N) :=
  (fourWalkCollisions W).filter (fun p => fourWalkCollisionKey p = k)

theorem fourWalkCollisionFibre_second_injOn {N : Nat} [NeZero N]
    (W : Finset (FourWalkData N)) (k : ZMod N × ZMod N × ZMod N) :
    Set.InjOn (fun p : FourWalkData N × FourWalkData N => p.2.2)
      ↑(fourWalkCollisionFibre W k) := by
  intro p hp q hq ht
  obtain ⟨hp,hpk⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq,hqk⟩ := Finset.mem_filter.mp hq
  have hk := hpk.trans hqk.symm
  dsimp only [fourWalkCollisionKey] at hk
  have hu : p.1.1.1 = q.1.1.1 := congrArg (fun k : ZMod N × ZMod N × ZMod N => k.1) hk
  have hu' : p.2.1.1 = q.2.1.1 := congrArg (fun k => k.2.1) hk
  have hv' : p.2.1.2 = q.2.1.2 := congrArg (fun k => k.2.2) hk
  have hsecond : p.2 = q.2 := Prod.ext (Prod.ext hu' hv') ht
  have hsteps := (Finset.mem_filter.mp hp).2.trans
    ((congrArg fourWalkDataSteps hsecond).trans (Finset.mem_filter.mp hq).2.symm)
  change fourWalkSteps p.1.1.1 p.1.1.2 p.1.2 = fourWalkSteps q.1.1.1 q.1.1.2 q.1.2 at hsteps
  rw [← hu] at hsteps
  have hfirst : (p.1.1.2,p.1.2) = (q.1.1.2,q.1.2) :=
    fourWalkSteps_start_injective _ hsteps
  have hv : p.1.1.2 = q.1.1.2 := congrArg (fun k : ZMod N × (ZMod N × ZMod N × ZMod N) => k.1) hfirst
  have ht1 : p.1.2 = q.1.2 := congrArg (fun k : ZMod N × (ZMod N × ZMod N × ZMod N) => k.2) hfirst
  exact Prod.ext (Prod.ext (Prod.ext hu hv) ht1) hsecond

theorem fourWalkCollisionFibre_card_le {N : Nat} [NeZero N]
    (W : Finset (FourWalkData N)) (k : ZMod N × ZMod N × ZMod N) :
    (fourWalkCollisionFibre W k).card ≤ N^3 := by
  have h := Finset.card_le_card_of_injOn (s := fourWalkCollisionFibre W k)
    (t := Finset.univ) (fun p => p.2.2) (fun _ _ => Finset.mem_univ _)
    (fourWalkCollisionFibre_second_injOn W k)
  simpa only [Finset.card_univ,Fintype.card_prod,ZMod.card,show N*(N*N)=N^3 by ring] using h

end LeanProofs.GowersSzemeredi
