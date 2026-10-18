import GowersSzemeredi.Proofs07BohrHom

/-! Declarations of `Proofs07BohrHom` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma lemma78_alpha_le_one {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real)
    (hcard : (A.card : Real) = alpha * N) : alpha <= 1 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcardN : (A.card : Real) <= N := by
    exact_mod_cast (by simpa only [ZMod.card] using A.card_le_univ)
  rw [hcard] at hcardN
  nlinarith

/-- The general-abelian-codomain form of Lemma 7.8 mentioned immediately
after its proof in the paper.  The Bohr neighborhood lives in the cyclic
domain; the induced Freiman map may take values in any additive commutative
group. -/
theorem lemma_7_8_group_holds {G : Type*} [AddCommGroup G]
    (N : Nat) [NeZero N] (A : Finset (ZMod N))
    (phi : ZMod N -> G) (alpha : Real) (halpha : 0 < alpha)
    (hcard : (A.card : Real) = alpha * N) (hphi : FreimanHom 8 A phi) :
    let K := section7Spectrum A alpha
    (K.card : Real) <= 16 * alpha ^ (-(2 : Real)) /\
      exists psi : ZMod N -> G,
        FreimanHom 2 (bohr K (alpha / (32 * Real.pi))) psi /\
        forall x, x ∈ A -> forall y, y ∈ A ->
          x - y ∈ bohr K (alpha / (32 * Real.pi)) ->
          phi x - phi y = psi (x - y) := by
  dsimp only
  constructor
  · exact lemma78_spectrum_card_bound A alpha halpha hcard
  · exact ⟨lemma78InducedMap A phi alpha halpha hcard,
      lemma78_induced_freiman A phi alpha halpha hcard hphi,
      lemma78_induced_agrees A phi alpha halpha hcard hphi⟩

end LeanProofs.GowersSzemeredi
