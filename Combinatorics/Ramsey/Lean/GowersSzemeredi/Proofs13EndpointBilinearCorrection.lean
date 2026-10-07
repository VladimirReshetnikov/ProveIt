import GowersSzemeredi.Proofs13EndpointRowCorrection
import GowersSzemeredi.Proofs13EndpointSymmetricRankOne

/-! A symmetric frequency table over a prime field lies within eighteen
 times its averaged addition-test failure of a scalar bilinear map. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem endpoint_symmetric_bilinear_correction {N : Nat} [NeZero N] [Fact N.Prime]
    (phi : ZMod N × ZMod N → ZMod N) (tau : Real)
    (hsymm : ∀ h k, phi (h, k) = phi (k, h))
    (hfailure : (𝔼 k : ZMod N, endpointAdditiveFailure (fun h => phi (h, k))) ≤ tau) :
    ∃ c : ZMod N, endpointError phi (fun p => c * p.1 * p.2) ≤ 18 * tau := by
  obtain ⟨a, ha⟩ := endpoint_rows_correction phi tau hfailure
  let L : ZMod N × ZMod N → ZMod N := fun p => a p.2 * p.1
  let L' : ZMod N × ZMod N → ZMod N := fun p => a p.1 * p.2
  have hswap : endpointError phi L' = endpointError phi L := by
    have he := endpointError_equiv (Equiv.prodComm (ZMod N) (ZMod N)) phi L
    have hp : phi ∘ Equiv.prodComm (ZMod N) (ZMod N) = phi :=
      funext (fun p => hsymm p.2 p.1)
    rw [hp] at he
    exact he
  have hsym : endpointError L L' ≤ 2 * endpointError phi L := by
    have ht := endpointError_triangle L phi L'
    rw [endpointError_symm L phi, hswap] at ht
    linarith only [ht]
  obtain ⟨c, hc⟩ := endpoint_symmetric_rank_one a
  refine ⟨c, ?_⟩
  have ht := endpointError_triangle phi L (fun p => c * p.1 * p.2)
  change endpointError L (fun p => c * p.1 * p.2) ≤ endpointError L L' at hc
  change endpointError phi L ≤ 6 * tau at ha
  linarith only [ht, hc, hsym, ha]

end LeanProofs.GowersSzemeredi
