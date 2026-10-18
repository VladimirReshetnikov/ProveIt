import GowersSzemeredi.Proofs16Translations

/-! Relation covers with the actual power exponent, graph budget, and
starting width. Translation preserves all four quantitative parameters.

`LargeBoxMultilinearCover.translate` is in `Proofs16PowerCoverTransportSide`,
outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A relation admits proper multilinear covers on every sufficiently wide
proper box. The explicit width threshold is part of the assertion. -/
def LargeBoxMultilinearCover {N k : Nat} [NeZero N]
    (Gamma : Finset (Point N k × ZMod N)) (rho C e T : Real) : Prop :=
  ∀ P : Box N k, P.IsProper → T ≤ (P.width : Real) →
    ∃ M q : Nat, ∃ H : Finset (Point N k), ∃ Q : Fin M → Box N k,
      ∃ mu : Fin M → Fin q → Point N k → ZMod N,
        H ⊆ P.carrier ∧ (1 - rho) * (P.carrier.card : Real) ≤ H.card ∧
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧ (q : Real) ≤ C ∧
        (∀ j, (P.width : Real) ^ e ≤ (Q j).width) ∧
        (∀ j i, IsMultilinear (mu j i)) ∧
        ∀ j x, x ∈ (Q j).carrier → x ∈ H → ∀ y,
          (x, y) ∈ Gamma → ∃ i, y = mu j i x

theorem LargeBoxMultilinearCover.mono {N k : Nat} [NeZero N]
    {Gamma Delta : Finset (Point N k × ZMod N)} {rho C e T : Real}
    (h : LargeBoxMultilinearCover Gamma rho C e T) (hsub : Delta ⊆ Gamma) :
    LargeBoxMultilinearCover Delta rho C e T := by
  intro P hP hT
  obtain ⟨M, q, H, Q, mu, hH, hm, hp, hproper, hq, hw, hmu, hc⟩ := h P hP hT
  exact ⟨M, q, H, Q, mu, hH, hm, hp, hproper, hq, hw, hmu,
    fun j x hx hh y hy => hc j x hx hh y (hsub hy)⟩

end LeanProofs.GowersSzemeredi
