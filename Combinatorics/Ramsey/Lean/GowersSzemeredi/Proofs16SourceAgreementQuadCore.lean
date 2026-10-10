import GowersSzemeredi.Proofs16JointSourceCoreBudget

/-! Prune the compatible quadruple core by its actual source-agreement
exceptions. The retained core simultaneously respects every quadruple and
has many original alternatives at every vertex. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Preserve all-quadruple compatibility and pointwise original source
agreement on one near-full core, with the required anchor reserve. -/
theorem exists_source_agreement_quad_core {N d K : Nat} [NeZero N]
    (Q : CenteredProgression N) (hQ : Q.Proper)
    (T : ZMod N → Finset (ZMod N)) (F : ZMod N → ZMod N → ZMod N)
    (U : Finset (ZMod N)) (Tsrc : ZMod N → Finset (ZMod N)) (Lsrc : ZMod N → ZMod N → ZMod N)
    (f : ZMod N → FourRepresentationTuple N) (sigma : Real) (J : Nat) (kappa : Real)
    (Bad : Finset (Fin 4 → ZMod N)) {rho delta eta : Real}
    (hrho : 0 < rho) (hK : 0 < K) (hdelta : 0 < delta)
    (hmass : delta*N ≤ (Q.carrier.card : Real))
    (heta : eta ≤ delta^3/(4096*(4194304 : Real)^Q.rank))
    (hT : ∀ x ∈ Q.carrier, (T x).card ≤ d)
    (hF : ∀ x ∈ Q.carrier, IsFreimanLinearOn (bohr (T x) rho) (F x))
    (hsub : progressionMapImageFailures Q.carrier T F rho K ⊆ Bad)
    (hbad : (Bad.card : Real) ≤ eta*(N : Real)^3)
    (hgood : ∀ q ∈ progressionAdditiveQuadruples Q.carrier, q ∉ Bad →
      ∀ i, kappa*(N : Real)^3/2 ≤ ((representationAgreementAlternatives U Tsrc Lsrc f (q i) sigma J).card : Real)) :
    let M := K*K*refinementKernelCap (4*d) (2*d) rho rho
    ∃ S ⊆ (centeredProgressionShrink Q 16).carrier,
      (((centeredProgressionShrink Q 16).carrier \ S).card : Real) ≤ delta*N/(16*(1024 : Real)^Q.rank) ∧
      (∀ x ∈ S, kappa*(N : Real)^3/2 ≤ ((representationAgreementAlternatives U Tsrc Lsrc f x sigma J).card : Real)) ∧
      ∀ a b c e : ZMod N, a ∈ S → b ∈ S → c ∈ S → e ∈ S → a-b = c-e →
        ColumnQuadImageRelation T F (rho/4)
          (M*M*refinementKernelCap (4*d) (2*d) (rho/2) (rho/2)) a b c e := by
  intro M
  have hfail : ((progressionMapImageFailures Q.carrier T F rho K).card : Real) ≤ eta*(N : Real)^3 := by
    have hcard : ((progressionMapImageFailures Q.carrier T F rho K).card : Real) ≤ Bad.card := by
      exact_mod_cast Finset.card_le_card hsub
    exact hcard.trans hbad
  obtain ⟨S0,hS0,hS0mass,hquad⟩ := exists_progression_all_quad_image_core Q hQ T F hrho hK hT hF hfail
  let V := sourceAgreementBadVertices Q U Tsrc Lsrc f sigma J kappa
  let S := S0 \ V
  have hSmem : S ⊆ (centeredProgressionShrink Q 16).carrier := fun x hx => hS0 (Finset.mem_sdiff.mp hx).1
  have hVmass : (V.card : Real) ≤ eta*(4096 : Real)^Q.rank/delta^2*N :=
    source_agreement_bad_vertices_mass Q hQ U Tsrc Lsrc f sigma J kappa Bad hdelta hmass hbad hgood
  have hS0loss : (((centeredProgressionShrink Q 16).carrier \ S0).card : Real) ≤
      2*(eta*(N : Real)^3/(progressionGoodPairThreshold Q+1))/(progressionPurificationVertexThreshold Q+1) := by
    have hp : (((centeredProgressionShrink Q 16).carrier \ S0).card : Real)+(S0.card : Real) =
        (centeredProgressionShrink Q 16).carrier.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hS0
    linarith
  have hmissing : (centeredProgressionShrink Q 16).carrier \ S ⊆
      ((centeredProgressionShrink Q 16).carrier \ S0) ∪ V := by
    intro x hx
    obtain ⟨hxD,hxnot⟩ := Finset.mem_sdiff.mp hx
    by_cases hx0 : x ∈ S0
    · apply Finset.mem_union_right
      by_contra hxV
      exact hxnot (Finset.mem_sdiff.mpr ⟨hx0,hxV⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxD,hx0⟩)
  have hmissingR : (((centeredProgressionShrink Q 16).carrier \ S).card : Real) ≤
      ((centeredProgressionShrink Q 16).carrier \ S0).card+(V.card : Real) := by
    exact_mod_cast (Finset.card_le_card hmissing).trans (Finset.card_union_le _ _)
  have hbudget := joint_source_core_loss_budget Q hQ hdelta hmass heta
  have hSmissing : (((centeredProgressionShrink Q 16).carrier \ S).card : Real) ≤ delta*N/(16*(1024 : Real)^Q.rank) :=
    (hmissingR.trans (add_le_add hS0loss hVmass)).trans hbudget
  refine ⟨S,hSmem,hSmissing,?_,?_⟩
  · intro x hx
    exact source_agreement_of_not_bad_vertex Q U Tsrc Lsrc f sigma J kappa (hSmem hx) (Finset.mem_sdiff.mp hx).2
  · intro a b c e ha hb hc he hadd
    exact hquad a b c e (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1
      (Finset.mem_sdiff.mp hc).1 (Finset.mem_sdiff.mp he).1 hadd

end LeanProofs.GowersSzemeredi
