import GowersSzemeredi.Proofs16BohrTranslateRetention
import GowersSzemeredi.Proofs16CommonProgressionParameters

/-! Localize indexed Bohr configurations to one proper centered
progression and retain the normalized common difference map. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem bohr_freiman_progression_retention {N r : Nat} [NeZero N] {I : Type*}
    (Q : Finset I) (x : I → ZMod N) (Gamma : Finset (ZMod N))
    (psi : ZMod N → ZMod N) {rho mass : Real}
    (hrho : 0 < rho) (hG : Gamma.card ≤ r) (hmass : 0 < mass) (hQ : mass ≤ Q.card)
    (hx : ∀ q ∈ Q, x q ∈ bohr Gamma (rho/2))
    (hpsi : FreimanHom 2 (bohr Gamma rho) psi) (hzero : psi 0 = 0) :
    ∃ (P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N) (t : ZMod N) (R : Finset I),
      P.rank ≤ r+1 ∧ P.Proper ∧ P.carrier ⊆ bohr Gamma (rho/4) ∧
      bohrProgressionDensity r rho*N ≤ (P.carrier.card : Real) ∧
      R ⊆ Q ∧ bohrProgressionDensity r rho*mass ≤ (R.card : Real) ∧
      t ∈ bohr Gamma rho ∧
      ∀ q ∈ R, x q-t ∈ P.carrier ∧ psi (x q) = psi t+psi (x q-t) := by
  obtain ⟨P,hPrank,hPproper,hPsub,hPmass⟩ := exists_uniform_proper_progression_in_bohr Gamma hrho hG
  obtain ⟨t,R,hRQ,hR,ht,hvalue⟩ := bohr_freiman_translate_retention Q x Gamma P.carrier psi
    hrho.le (bohrProgressionDensity_pos r rho) hmass hQ hPmass hx
    (hPsub.trans (bohr_mono_radius Gamma (by linarith))) hpsi hzero
  exact ⟨P,t,R,hPrank,hPproper,hPsub,hPmass,hRQ,hR,ht,hvalue⟩

end LeanProofs.GowersSzemeredi
