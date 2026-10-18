import GowersSzemeredi.Proofs13PolyStage136

/-! Declarations of `Proofs13PolyStage136` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- **Lemmas 13.5 and 13.6 at a polynomial exponent.** Every budget is stated
in terms of `|P|^u` with `u = (2p(q+1)^8)^(−4)`. -/
theorem lemma_13_6_poly {N : Nat} [Fact N.Prime] {K : Real} {p : Nat}
    (hpp : ProgressionPhasePartition K p) (hp : 0 < p) (hK : K ≤ 2 ^ p)
    (S : Section13Context N) (D : Stage134Data N) (m : Nat)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D)
    (hm : 0 < m) (hsize : m * m ≤ N)
    (hupper : (m : Real) + 1 ≤ (D.P.length : Real) ^ stage135UniformExponent p D.q / 2)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m)
    (hbudget : (D.P.length : Real) ^ (-stage135UniformExponent p D.q) ≤
      section10Zeta (S.alpha ^ 32 / 16) / m) :
    ∃ E : Stage135Data N, ∃ F : Stage136Data N,
      IsStage135Data S D E ∧
      IsStage135At S D E (stage135UniformExponent p D.q) (stage135UniformExponent p D.q) ∧
      IsStage136Data S D E F ∧ m ≤ F.R.length ∧ F.R.length ≤ E.Q.length := by
  obtain ⟨E, h135, hE⟩ := lemma_13_5_poly_with_catalogue (Fact.out : N.Prime) hpp hp hK S D _ h134
  have hupper' : m + 1 ≤ E.Q.length := by
    have h : ((m + 1 : Nat) : Real) ≤ E.Q.length := by
      push_cast
      exact hupper.trans hE.2.2.2.1
    exact_mod_cast h
  obtain ⟨F, hF, hmF, hFQ⟩ := lemma_13_6_from_initial_stages_at S D E m _ h134 h135
    hE.2.2.2.2.1 hm hsize hupper' hlower hbudget
  exact ⟨E, F, h135, hE, hF, hmF, hFQ⟩

end LeanProofs.GowersSzemeredi
