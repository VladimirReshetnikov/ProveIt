import GowersSzemeredi.Proofs16HigherArrangementModel

/-! A dense sixteen-map arrangement retains a dense subfamily whose
first endpoint lies in an order-eight Freiman piece of the first map. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem higher_arrangements_retain_first_freiman_piece {N : Nat} [NeZero N] [Fact N.Prime]
    (f : Fin 16 → ZMod N → ZMod N) (Q : Finset (HigherArrangementParameter N))
    (hQ : ∀ p ∈ Q, HigherArrangementEquation f p)
    {delta : Real} (hd : 0 < delta) (hcount : delta*(N : Real)^11 ≤ Q.card) :
    ∃ (E : Finset (ZMod N)) (R : Finset (HigherArrangementParameter N)),
      E ⊆ Q.image (fun p => higherArrangementEndpoints p 0) ∧ R ⊆ Q ∧
      (∀ p ∈ R, higherArrangementEndpoints p 0 ∈ E) ∧ FreimanHom 8 E (f 0) ∧
      (2 : Real)^(-(1882 : Real))*(((delta/2)^2)^4)^1164*N ≤ E.card ∧
      offsetFreimanRetention delta*(N : Real)^11 ≤ R.card := by
  have hcount' : delta*(N^9 : Nat)*(N : Real)^2 ≤ Q.card := by
    simpa only [Nat.cast_pow,show delta*(N : Real)^9*(N : Real)^2 = delta*(N : Real)^11 by ring] using hcount
  obtain ⟨E,R,hEQ,hRQ,hER,hF,hE,hR⟩ := offset_equation_retain_freiman_piece Q Prod.fst
    (higherArrangementResidual f) (f 0) (f 1) (N^9) (pow_pos (NeZero.pos N) 9)
    (fun a => (higherArrangement_offset_fibre_card a).le)
    (fun p hp => higherArrangementEquation_offset f p (hQ p hp)) hd hcount'
  refine ⟨E,R,hEQ,hRQ,hER,hF,hE,?_⟩
  simpa only [Nat.cast_pow,show offsetFreimanRetention delta*(N : Real)^9*(N : Real)^2 =
    offsetFreimanRetention delta*(N : Real)^11 by ring] using hR

end LeanProofs.GowersSzemeredi
