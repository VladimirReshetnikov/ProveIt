import GowersSzemeredi.Proofs16FourWalkCollisionFibres
import GowersSzemeredi.Proofs16PopularEndpointFibres

/-! A dense walk family has many endpoint keys with enough matched
walks to apply coherent compression. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem fourWalkCollisions_density {N : Nat} [NeZero N] (W : Finset (FourWalkData N))
    {mu : Real} (hmu : 0 ≤ mu) (hW : mu*(N : Real)^5 ≤ W.card) :
    mu^2*(N : Real)^6 ≤ (fourWalkCollisions W).card := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ mu*(N : Real)^5) hW 2
  have hc := fourWalkCollisions_mass_bound W
  apply (mul_le_mul_iff_left₀ (pow_pos hn 4)).mp
  nlinarith [hs,hc]

theorem popular_fourWalkCollisionKeys_dense {N : Nat} [NeZero N]
    (W : Finset (FourWalkData N)) {mu : Real} (hmu : 0 ≤ mu)
    (hW : mu*(N : Real)^5 ≤ W.card) :
    mu^2*(N : Real)^3/2 ≤
      ((popularEndpointFibres (fourWalkCollisions W) fourWalkCollisionKey (mu^2*(N : Real)^3/2)).card : Real) := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hmass := fourWalkCollisions_density W hmu hW
  have h := popular_endpoint_fibres_dense (fourWalkCollisions W) fourWalkCollisionKey
    (by positivity : (0 : Real) < (N : Real)^3) (sq_nonneg mu)
    (fun k => by exact_mod_cast fourWalkCollisionFibre_card_le W k)
    (by simpa only [Fintype.card_prod,ZMod.card,Nat.cast_mul] using (show
      mu^2*((N : Real)*(N*N))*(N : Real)^3 ≤ (fourWalkCollisions W).card by nlinarith [hmass]))
  simpa only [Fintype.card_prod,ZMod.card,Nat.cast_mul,show (N : Real)*(N*N)=(N : Real)^3 by ring] using h

end LeanProofs.GowersSzemeredi
