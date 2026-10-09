import GowersSzemeredi.Proofs16OffsetCollisionProjection

/-! Offset-fibre bounds turn a dense indexed equation into a dense
mixed-quadruple family with a quadratic loss in density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem offset_fibres_card_bound {N : Nat} [NeZero N] {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ZMod N) (M : Nat) (ha : ∀ z, (Finset.univ.filter fun i => a i = z).card ≤ M) :
    Fintype.card I ≤ M*N := by
  have h : (Finset.univ : Finset I).card ≤ M*(Finset.univ.image a).card := by
    apply Finset.card_le_mul_card_image
    exact fun z _ => ha z
  have hc : (Finset.univ.image a).card ≤ N := by simpa only [ZMod.card] using Finset.card_le_univ (Finset.univ.image a)
  simpa only [Finset.card_univ] using h.trans (Nat.mul_le_mul_left M hc)

theorem offset_collision_quadruple_density {N : Nat} [NeZero N] {I : Type*}
    [Fintype I] [DecidableEq I] (Q : Finset (I × ZMod N)) (a : I → ZMod N) (M : Nat)
    (hM : 0 < M) (ha : ∀ z, (Finset.univ.filter fun i => a i = z).card ≤ M)
    {delta : Real} (hd : 0 ≤ delta) (hQ : delta*M*(N : Real)^2 ≤ Q.card) :
    delta^2*(N : Real)^3 ≤ ((parameterCollisions Q).image (offsetCollisionQuad a)).card := by
  let V := (parameterCollisions Q).image (offsetCollisionQuad a)
  have hcs : Q.card^2 ≤ (parameterCollisions Q).card*Fintype.card I :=
    card_sq_le_keyMatchingCount Q Prod.fst
  have hnat : Q.card^2 ≤ (M*V.card)*(M*N) := hcs.trans (Nat.mul_le_mul
    (parameterCollisions_projection_card Q a M ha) (offset_fibres_card_bound a M ha))
  have hreal : (Q.card : Real)^2 ≤ ((M : Real)*V.card)*((M : Real)*N) := by exact_mod_cast hnat
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hm : (0 : Real) < M := by exact_mod_cast hM
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ delta*M*(N : Real)^2) hQ 2
  apply le_of_mul_le_mul_right (a := (M : Real)^2*N) _ (by positivity)
  calc delta^2*(N : Real)^3*((M : Real)^2*N) = (delta*M*(N : Real)^2)^2 := by ring
    _ ≤ (Q.card : Real)^2 := hpow
    _ ≤ _ := hreal
    _ = (V.card : Real)*((M : Real)^2*N) := by ring

theorem offset_equation_freiman_piece {N : Nat} [NeZero N] [Fact N.Prime] {I : Type*}
    [Fintype I] [DecidableEq I] (Q : Finset (I × ZMod N)) (a v : I → ZMod N)
    (A : Finset (ZMod N)) (f g : ZMod N → ZMod N) (M : Nat)
    (hM : 0 < M) (ha : ∀ z, (Finset.univ.filter fun i => a i = z).card ≤ M)
    (hA : ∀ p ∈ Q, p.2+a p.1 ∈ A) (hval : ∀ p ∈ Q, f (p.2+a p.1)-g p.2 = v p.1)
    {delta : Real} (hd : 0 < delta) (hQ : delta*M*(N : Real)^2 ≤ Q.card) :
    ∃ E ⊆ A, (2 : Real)^(-(1882 : Real))*((delta^2)^4)^1164*N ≤ E.card ∧ FreimanHom 8 E f := by
  exact mixed_quadruples_freiman_piece A ![f,g,f,g] _ (offsetCollisionQuad_mem_mixed Q a v A f g hA hval)
    (pow_pos hd 2) (offset_collision_quadruple_density Q a M hM ha hd.le hQ)

end LeanProofs.GowersSzemeredi
