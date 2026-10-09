import GowersSzemeredi.Proofs16RecenteredQuadruples

/-! Dense coherent quadruples can be recentered onto one actual proper
progression, with additive translations and an explicit ambient density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem additive_quadruples_on_proper_progression {N g : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (Gamma : Finset (ZMod N)) {rho kappa : Real}
    (hr : 0 < rho) (hk : 0 < kappa) (hG : Gamma.card ≤ g)
    (hQ : ∀ a ∈ Q, a 0+a 1 = a 2+a 3) (hmass : kappa*(N : Real)^3 ≤ Q.card) :
    ∃ (P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N)
      (t : Fin 4 → ZMod N) (S : Finset (Fin 4 → ZMod N)),
      P.rank ≤ g+1 ∧ P.Proper ∧ P.carrier ⊆ bohr Gamma (rho/4) ∧
      bohrProgressionDensity g rho*N ≤ (P.carrier.card : Real) ∧
      t 0+t 1 = t 2+t 3 ∧ S.Nonempty ∧
      (kappa*(bohrProgressionDensity g rho)^4)*(N : Real)^3 ≤ S.card ∧
      ∀ b ∈ S, b 0+b 1 = b 2+b 3 ∧ (∀ j, b j ∈ P.carrier) ∧ (fun j => t j+b j) ∈ Q := by
  obtain ⟨P,hPrank,hPproper,hPsub,hPmass⟩ := exists_uniform_proper_progression_in_bohr Gamma hr hG
  obtain ⟨t,ht,hm⟩ := exists_dense_additive_translation Q P.carrier hQ
    (bohrProgressionDensity_pos g rho).le hmass hPmass
  let S := recenteredQuadruples (localizedQuadruples Q P.carrier t) t
  have hS : (kappa*(bohrProgressionDensity g rho)^4)*(N : Real)^3 ≤ S.card := by
    simpa only [S,recenteredQuadruples_card] using hm
  have hSne : S.Nonempty := by
    apply Finset.card_pos.mp
    have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    have hp := bohrProgressionDensity_pos g rho
    exact_mod_cast (by positivity : 0 < (kappa*(bohrProgressionDensity g rho)^4)*(N : Real)^3).trans_le hS
  exact ⟨P,t,S,hPrank,hPproper,hPsub,hPmass,ht,hSne,hS,recentered_localized_quadruples Q P.carrier t hQ ht⟩

end LeanProofs.GowersSzemeredi
