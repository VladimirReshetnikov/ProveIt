import GowersSzemeredi.Proofs16MixedQuadrupleExtraction
import GowersSzemeredi.Proofs16PopularFibreRetention

/-! Extract a Freiman piece of one map while retaining a dense subfamily
of the original mixed configurations. Popular first coordinates prevent
the extraction from discarding almost all configurations. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def mixedConfigurationRetention (delta : Real) : Real :=
  delta/2*((2 : Real)^(-(1882 : Real))*((delta/2)^4)^1164)

theorem mixedConfigurationRetention_pos {delta : Real} (hdelta : 0 < delta) :
    0 < mixedConfigurationRetention delta := by
  unfold mixedConfigurationRetention
  positivity

/-- A dense original family contains an explicitly dense subfamily whose
first coordinates lie in a single order-eight Freiman piece of `f 0`. -/
theorem mixed_configurations_retain_freiman_piece {N : Nat} [NeZero N] [Fact N.Prime]
    (f : Fin 4 → ZMod N → ZMod N) (Q : Finset (Fin 4 → ZMod N))
    (hQ : Q ⊆ mixedColumnQuadruples Finset.univ f)
    {delta : Real} (hdelta : 0 < delta) (hcount : delta*(N : Real)^3 ≤ Q.card) :
    ∃ (E : Finset (ZMod N)) (R : Finset (Fin 4 → ZMod N)),
      E ⊆ Q.image (fun q => q 0) ∧ R ⊆ Q ∧
      (∀ q ∈ R, q 0 ∈ E) ∧ FreimanHom 8 E (f 0) ∧
      (2 : Real)^(-(1882 : Real))*((delta/2)^4)^1164*N ≤ E.card ∧
      mixedConfigurationRetention delta*(N : Real)^3 ≤ R.card := by
  let tau := delta*(N : Real)^2/2
  let P := popularEndpointFibres Q (fun q => q 0) tau
  let Q' := Q.filter fun q => q 0 ∈ P
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have htau : 0 < tau := by dsimp [tau]; positivity
  have hmass := popular_fibre_retained_mass Q (fun q => q 0) htau.le
  have hQ' : (delta/2)*(N : Real)^3 ≤ Q'.card := by
    simp only [ZMod.card] at hmass
    change (Q.card : Real)-(N : Real)*tau ≤ (Q'.card : Real) at hmass
    dsimp [tau] at hmass
    nlinarith only [hmass,hcount]
  have hsub : Q' ⊆ mixedColumnQuadruples P f := by
    intro q hq
    obtain ⟨hqQ,hqP⟩ := Finset.mem_filter.mp hq
    obtain ⟨_,_,hd,hv⟩ := Finset.mem_filter.mp (hQ hqQ)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hqP,hd,hv⟩
  obtain ⟨E,hEP,hE,hF⟩ := mixed_quadruples_freiman_piece P f Q' hsub (by positivity) hQ'
  let R := Q.filter fun q => q 0 ∈ E
  have hR : tau*E.card ≤ (R.card : Real) :=
    fibre_filter_mass_lower Q (fun q => q 0) E (fun x hx => (Finset.mem_filter.mp (hEP hx)).2)
  refine ⟨E,R,fun x hx => popular_endpoint_mem_image Q (fun q => q 0) htau (hEP hx),
    Finset.filter_subset _ _,fun q hq => (Finset.mem_filter.mp hq).2,hF,hE,?_⟩
  calc mixedConfigurationRetention delta*(N : Real)^3 =
      tau*((2 : Real)^(-(1882 : Real))*((delta/2)^4)^1164*N) := by
        dsimp [mixedConfigurationRetention,tau]
        ring
    _ ≤ tau*E.card := mul_le_mul_of_nonneg_left hE htau.le
    _ ≤ R.card := hR

end LeanProofs.GowersSzemeredi
