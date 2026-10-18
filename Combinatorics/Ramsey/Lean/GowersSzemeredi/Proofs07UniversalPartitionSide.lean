import GowersSzemeredi.Proofs07UniversalPartition

/-! Declarations of `Proofs07UniversalPartition` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Two coefficient maps share the single-domain exponent, rather than
losing a factor two from treating them as two independent spectra. -/
theorem corollary_7_11_pair_modular (N : Nat) [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (a c : ZMod N → ZMod N) (alpha : Real)
    (hR : R.IsProper) (hstep : R.step != 0) (hl : 0 < R.length)
    (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (hA : A ⊆ R.carrier) (hdensity : alpha * R.length ≤ A.card)
    (ha : FreimanHom 8 A a) (hc : FreimanHom 8 A c) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      ∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧
        (R.length : Real) ^ cor711Exponent alpha 1 ≤ (Q j).length ∧
        LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) a ∧
        LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) c := by
  obtain ⟨M, Q, hp, hcell⟩ :=
    corollary_7_11_all_scales_universal N R A alpha hR hstep hl hα hαone hA hdensity
  exact ⟨M, Q, hp, fun j ↦ ⟨(hcell j).1, (hcell j).2.1, (hcell j).2.2.1,
    (hcell j).2.2.2 a ha, (hcell j).2.2.2 c hc⟩⟩

end LeanProofs.GowersSzemeredi
