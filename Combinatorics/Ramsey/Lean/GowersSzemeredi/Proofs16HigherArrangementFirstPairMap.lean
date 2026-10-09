import GowersSzemeredi.Proofs16OffsetPairFrequencyMap
import GowersSzemeredi.Proofs16HigherArrangementModel

/-! The first pair of a dense higher arrangement has a common Freiman
map on a translated proper progression, with original tuples retained. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem higher_arrangements_first_pair_frequency_map {N : Nat} [NeZero N]
    (f : Fin 16 → ZMod N → ZMod N) (Q : Finset (HigherArrangementParameter N))
    (A B : Finset (ZMod N)) (hQ : ∀ p ∈ Q, HigherArrangementEquation f p)
    (hA : ∀ p ∈ Q, higherArrangementEndpoints p 0 ∈ A)
    (hB : ∀ p ∈ Q, higherArrangementEndpoints p 1 ∈ B)
    (hf : FreimanHom 8 A (f 0)) (hg : FreimanHom 8 B (f 1))
    {delta : Real} (hd : 0 < delta) (hcount : delta*(N : Real)^11 ≤ Q.card) :
    ∃ (theta : PairFrequencyMap N) (R : Finset (HigherArrangementParameter N)),
      theta.Controlled (delta^2) ∧ R ⊆ Q ∧
      offsetDifferenceProgressionRetention delta*(N : Real)^11 ≤ R.card ∧
      ∀ p ∈ R, p.1.1 ∈ theta.domain ∧ theta.toFun p.1.1 =
        f 0 (higherArrangementEndpoints p 0)-f 1 (higherArrangementEndpoints p 1) := by
  have hcount' : delta*(N^9 : Nat)*(N : Real)^2 ≤ Q.card := by
    simpa only [Nat.cast_pow,show delta*(N : Real)^9*(N : Real)^2 = delta*(N : Real)^11 by ring] using hcount
  obtain ⟨theta,R,hcontrol,hRQ,hR,hvalue⟩ := offset_equation_pair_frequency_map Q Prod.fst
    (higherArrangementResidual f) A B (f 0) (f 1) (N^9) (pow_pos (NeZero.pos N) 9)
    (fun a => (higherArrangement_offset_fibre_card a).le) hA hB
    (fun p hp => higherArrangementEquation_offset f p (hQ p hp))
    (hf.isFreimanLinearOn (by decide)) hg hd hcount'
  refine ⟨theta,R,hcontrol,hRQ,?_,hvalue⟩
  simpa only [Nat.cast_pow,show offsetDifferenceProgressionRetention delta*(N : Real)^9*(N : Real)^2 =
    offsetDifferenceProgressionRetention delta*(N : Real)^11 by ring] using hR

end LeanProofs.GowersSzemeredi
