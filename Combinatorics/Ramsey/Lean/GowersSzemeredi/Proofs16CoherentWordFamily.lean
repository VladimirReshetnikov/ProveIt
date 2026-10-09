import GowersSzemeredi.Proofs16CoherentWordParameters

/-! Every bounded-length list from a dense set of anchors has many
compatible word representations at the same coherent radius. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def HasCoherentWordFamily {N ell : Nat} [NeZero N] (X B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (sigma kappa : Real) (K : Nat) : Prop :=
  let T := fun u => B ∪ Finset.univ.image (fun j => theta j u)
  ∃ A P : Finset (ZMod N), A ⊆ X ∧ P ⊆ A ∧
    (9*kappa^2/512)*N ≤ (A.card : Real) ∧ (9*kappa^2/1024)*N ≤ (P.card : Real) ∧
    ThresholdColumnRichness A T F (sigma/1296) (coherentWordDensity kappa K/2) (coherentRobustWalkDensity kappa) ∧
    (∀ a ∈ P, coherentAnchorTripleDensity kappa*(N : Real)^2 ≤
      (columnTripleRepresentations A T F (sigma/1296) a).card) ∧
    ∀ (a : ZMod N) (as : List (ZMod N)), (∀ x ∈ a::as, x ∈ P) → as.length ≤ K →
      coherentWordDensity kappa as.length*(N : Real)^(3*as.length+2) ≤
        (columnWordRepresentations A T F (sigma/1296) (a::as)).card

theorem HasCoherentRichSet.word_family {N ell : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma kappa : Real} (K : Nat)
    (h : HasCoherentRichSet X B theta F sigma kappa (coherentWordDensity kappa K/2))
    (hk : 0 < kappa) (hk1 : kappa ≤ 1) :
    HasCoherentWordFamily X B theta F sigma kappa K := by
  obtain ⟨A,hAX,hA,hrich⟩ := h
  let T := fun u => B ∪ Finset.univ.image (fun j => theta j u)
  have hr : ThresholdColumnRichness A T F (sigma/1296)
      (coherentWordDensity kappa K/2) (coherentRobustWalkDensity kappa) := hrich
  let P := popularColumnAnchors A T F (sigma/1296) (coherentAnchorTripleDensity kappa)
  have hcut : coherentWordDensity kappa K/2 ≤ (9*kappa^2/512)/2 := by
    have hd := coherentWordDensity_antitone hk hk1 (Nat.zero_le K)
    have hl := coherentAnchorTripleDensity_le_set_density hk hk1
    change coherentWordDensity kappa K ≤ coherentAnchorTripleDensity kappa at hd
    linarith
  have hP := hr.popular_anchors (by positivity : 0 < 9*kappa^2/512)
    (coherentRobustWalkDensity_pos hk) hA hcut
  have htrip : ∀ a ∈ P, coherentAnchorTripleDensity kappa*(N : Real)^2 ≤
      (columnTripleRepresentations A T F (sigma/1296) a).card :=
    fun _ ha => popular_column_triple_count A T F (sigma/1296) (coherentAnchorTripleDensity kappa) ha
  refine ⟨A,P,hAX,Finset.filter_subset _ _,hA,?_,hr,htrip,?_⟩
  · change (9*kappa^2/1024)*N ≤ (P.card : Real)
    change (9*kappa^2/512)*(N : Real)/2 ≤ (P.card : Real) at hP
    nlinarith only [hP]
  · intro a as has hsize
    exact threshold_column_word_representations_count A P T F (sigma/1296)
      (coherentAnchorTripleDensity_pos hk) (coherentRobustWalkDensity_pos hk) htrip hr K
      (fun j hj => div_le_div_of_nonneg_right (coherentWordDensity_antitone hk hk1 hj) (by norm_num))
      a as has hsize

end LeanProofs.GowersSzemeredi
