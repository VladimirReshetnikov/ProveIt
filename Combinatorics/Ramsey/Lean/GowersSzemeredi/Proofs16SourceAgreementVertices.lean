import GowersSzemeredi.Proofs16QueryVertexCounts
import GowersSzemeredi.Proofs16QuerySourceAgreement

/-! Promote the good-query source comparison to good vertices. A vertex
with insufficient original alternatives can belong only to bad queries,
so its exception mass is bounded by the proved participation count. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def sourceAgreementBadVertices {N : Nat} [NeZero N]
    (Q : CenteredProgression N) (U : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (f : ZMod N → FourRepresentationTuple N)
    (rho : Real) (J : Nat) (kappa : Real) : Finset (ZMod N) :=
  (centeredProgressionShrink Q 16).carrier.filter fun x =>
    ((representationAgreementAlternatives U T L f x rho J).card : Real) < kappa*(N : Real)^3/2

theorem source_agreement_bad_vertices_subset {N : Nat} [NeZero N]
    (Q : CenteredProgression N) (U : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (f : ZMod N → FourRepresentationTuple N)
    (rho : Real) (J : Nat) (kappa : Real) (Bad : Finset (Fin 4 → ZMod N))
    (hgood : ∀ q ∈ progressionAdditiveQuadruples Q.carrier, q ∉ Bad →
      ∀ i, kappa*(N : Real)^3/2 ≤ ((representationAgreementAlternatives U T L f (q i) rho J).card : Real)) :
    sourceAgreementBadVertices Q U T L f rho J kappa ⊆ progressionQueryBadVertices Q Bad := by
  intro x hx
  obtain ⟨hxD,hsmall⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxD,?_⟩
  intro q hq hqx
  by_contra hnot
  have h := hgood q hq hnot 0
  rw [hqx] at h
  exact not_lt_of_ge h hsmall

/-- Sparse joint queries give a linear bound on vertices lacking enough
original agreement alternatives. -/
theorem source_agreement_bad_vertices_mass {N : Nat} [NeZero N]
    (Q : CenteredProgression N) (hQ : Q.Proper) (U : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (f : ZMod N → FourRepresentationTuple N) (rho : Real) (J : Nat) (kappa : Real)
    (Bad : Finset (Fin 4 → ZMod N)) {delta eta : Real}
    (hdelta : 0 < delta) (hmass : delta*N ≤ (Q.carrier.card : Real)) (hbad : (Bad.card : Real) ≤ eta*(N : Real)^3)
    (hgood : ∀ q ∈ progressionAdditiveQuadruples Q.carrier, q ∉ Bad →
      ∀ i, kappa*(N : Real)^3/2 ≤ ((representationAgreementAlternatives U T L f (q i) rho J).card : Real)) :
    ((sourceAgreementBadVertices Q U T L f rho J kappa).card : Real) ≤ eta*(4096 : Real)^Q.rank/delta^2*N := by
  have hsub := source_agreement_bad_vertices_subset Q U T L f rho J kappa Bad hgood
  have hcard : ((sourceAgreementBadVertices Q U T L f rho J kappa).card : Real) ≤
      (progressionQueryBadVertices Q Bad).card := by exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans (progression_bad_query_vertices_mass Q hQ Bad hdelta hmass hbad)

theorem source_agreement_of_not_bad_vertex {N : Nat} [NeZero N]
    (Q : CenteredProgression N) (U : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (f : ZMod N → FourRepresentationTuple N)
    (rho : Real) (J : Nat) (kappa : Real) {x : ZMod N}
    (hx : x ∈ (centeredProgressionShrink Q 16).carrier)
    (hnot : x ∉ sourceAgreementBadVertices Q U T L f rho J kappa) :
    kappa*(N : Real)^3/2 ≤ ((representationAgreementAlternatives U T L f x rho J).card : Real) := by
  apply not_lt.mp
  intro hsmall
  exact hnot (Finset.mem_filter.mpr ⟨hx,hsmall⟩)

end LeanProofs.GowersSzemeredi
