import GowersSzemeredi.Proofs16CoherentRichPowerAccuracy

/-! The density-dependent subset threshold is attained by the rich set
itself, giving actual mixed quadruples rather than a vacuous universal property. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem HasCoherentRichSet.self_richness {N ell p : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma kappa : Real}
    (h : HasCoherentRichSet X B theta F sigma kappa (coherentRichSubsetDensity kappa p))
    (hk : 0 ≤ kappa) (hk1 : kappa ≤ 1) :
    ∃ A : Finset (ZMod N), A ⊆ X ∧ (9*kappa^2/512)*N ≤ (A.card : Real) ∧
      coherentRichSubsetDensity kappa p*N ≤ (A.card : Real) ∧
      ((coherentRichSubsetDensity kappa p)^2*coherentRobustWalkDensity kappa)^2*(N : Real)^3/2 ≤
        ((mixedExactColumnQuadruples A A (fun u => B ∪ Finset.univ.image (fun j => theta j u))
          F (sigma/1296)).card : Real) := by
  obtain ⟨A,hAX,hA,hrich⟩ := h
  have hb := mul_le_mul_of_nonneg_right (coherentRichSubsetDensity_le hk hk1 p)
    (Nat.cast_nonneg N : (0 : Real) ≤ N)
  have hthreshold : coherentRichSubsetDensity kappa p*N ≤ (A.card : Real) := by
    nlinarith [mul_nonneg (sq_nonneg kappa) (Nat.cast_nonneg N : (0 : Real) ≤ N)]
  exact ⟨A,hAX,hA,hthreshold,hrich A A (Finset.Subset.refl A) (Finset.Subset.refl A) hthreshold hthreshold⟩

end LeanProofs.GowersSzemeredi
