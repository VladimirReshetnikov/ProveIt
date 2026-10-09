import GowersSzemeredi.Proofs16RepresentationQuadImageTransfer
import GowersSzemeredi.Proofs16RepeatedQuadrupleCounts

/-! Actual normalized maps on the structured index set, with controlled
quadruple image failures. Independent distinct-index errors and repeated
indices are accounted for separately. All maps retain their representation
in the original column family. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def progressionAdditiveQuadruples {N : Nat} [NeZero N] (C : Finset (ZMod N)) :
    Finset (Fin 4 → ZMod N) :=
  Finset.univ.filter fun q => (∀ j, q j ∈ C) ∧ q 0-q 1+q 2-q 3 = 0

def progressionMapImageFailures {N : Nat} [NeZero N]
    (C : Finset (ZMod N)) (S : ZMod N → Finset (ZMod N))
    (F : ZMod N → ZMod N → ZMod N) (sigma : Real) (K : Nat) : Finset (Fin 4 → ZMod N) :=
  (progressionAdditiveQuadruples C).filter fun q =>
    ¬ ColumnQuadImageRelation S F sigma K (q 0) (q 1) (q 3) (q 2)

/-- Choose representatives and normalize their maps. At most
`epsilon*N^3/(2*kappa^4)+6*N^2` progression quadruples exceed the original
image cap on the actual normalized half-radius common domain. -/
theorem exists_selected_progression_maps {N d K : Nat} [NeZero N]
    (X U C : Finset (ZMod N)) (hUX : U ⊆ X) (h0 : (0 : ZMod N) ∈ C)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N) (rho : Real)
    (hcol : ∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) rho) (L x) ∧ L x 0 = 0)
    {kappa epsilon : Real} (hk : 0 < kappa)
    (hrep : ∀ x ∈ C, kappa*(N : Real)^3 ≤ (fourDifferenceRepresentations U x).card)
    (hbad : ((columnTupleImageExceptions U T L rho K).card : Real) ≤ epsilon*(N : Real)^15/2) :
    ∃ f : ZMod N → FourRepresentationTuple N,
      (∀ x ∈ C, f x ∈ fourDifferenceRepresentations U x) ∧
      (∀ x ∈ C, (normalizedRepresentationSpectrum T f x).card ≤ 8*d ∧
        IsFreimanLinearOn (bohr (normalizedRepresentationSpectrum T f x) rho) (normalizedRepresentationMap L f x) ∧
        normalizedRepresentationMap L f x 0 = 0) ∧
      (∀ y, normalizedRepresentationMap L f 0 y = 0) ∧
      ((progressionMapImageFailures C (normalizedRepresentationSpectrum T f)
        (normalizedRepresentationMap L f) (rho/2) K).card : Real) ≤
          epsilon/(2*kappa^4)*(N : Real)^3+6*(N : Real)^2 := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let Q := progressionAdditiveQuadruples C
  let Qd := Q.filter Function.Injective
  let Bad := columnTupleImageExceptions U T L rho K
  have hQd : ∀ q ∈ Qd, (∀ j, q j ∈ C) ∧ Function.Injective q := by
    intro q hq
    obtain ⟨hqQ, hi⟩ := Finset.mem_filter.mp hq
    exact ⟨(Finset.mem_filter.mp hqQ).2.1, hi⟩
  obtain ⟨f, hvalid, hbadD⟩ := exists_progression_representatives_few_bad_distinct U C hk hrep Qd hQd Bad
  let BD := Qd.filter fun q => flattenFourRepresentations (fun j => f (q j)) ∈ Bad
  have hbadDR : (BD.card : Real) ≤ epsilon/(2*kappa^4)*(N : Real)^3 := by
    have hdiv := div_le_div_of_nonneg_right hbad
      (by positivity : (0 : Real) ≤ kappa^4*(N : Real)^12)
    have hbound : (Bad.card : Real)/(kappa^4*(N : Real)^12) ≤
        epsilon/(2*kappa^4)*(N : Real)^3 := by
      have heq : (epsilon*(N : Real)^15/2)/(kappa^4*(N : Real)^12) =
          epsilon/(2*kappa^4)*(N : Real)^3 := by
        field_simp
      simpa only [Bad, heq] using hdiv
    exact hbadD.trans hbound
  have hrepeat : ((Q.filter fun q => ¬ Function.Injective q).card : Real) ≤ 6*(N : Real)^2 := by
    exact_mod_cast repeated_additive_quadruples_card_le Q
      (fun q hq => (Finset.mem_filter.mp hq).2.2)
  have hsub : progressionMapImageFailures C (normalizedRepresentationSpectrum T f)
      (normalizedRepresentationMap L f) (rho/2) K ⊆ BD ∪ Q.filter (fun q => ¬ Function.Injective q) := by
    intro q hq
    obtain ⟨hqQ, hfail⟩ := Finset.mem_filter.mp hq
    by_cases hi : Function.Injective q
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hqQ, hi⟩, ?_⟩
      by_contra hnotBad
      have hqC := (Finset.mem_filter.mp hqQ).2.1
      have hadd := (Finset.mem_filter.mp hqQ).2.2
      have htuple := flattenFourRepresentations_mem_fibre U q (fun j => f (q j))
        (fun j => hvalid _ (hqC j)) hadd
      have himage : ((bohr (columnListSpectrum T (columnAnchorList
          (flattenFourRepresentations (fun j => f (q j))))) (rho/2)).image
          (fun y => columnAnchorEval (fun x => L x y)
            (columnAnchorList (flattenFourRepresentations (fun j => f (q j)))))).card ≤ K := by
        apply not_lt.mp
        intro hgt
        exact hnotBad (Finset.mem_filter.mpr ⟨htuple, hgt⟩)
      exact hfail (normalized_quad_image_transfer T L f q (rho/2) himage)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hqQ, hi⟩)
  have hcount : ((progressionMapImageFailures C (normalizedRepresentationSpectrum T f)
      (normalizedRepresentationMap L f) (rho/2) K).card : Real) ≤
      (BD.card : Real)+(Q.filter fun q => ¬ Function.Injective q).card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  exact ⟨f, hvalid, normalized_representation_column_data X U C hUX h0 T L rho hcol f hvalid,
    normalizedRepresentationMap_index_zero L f, hcount.trans (add_le_add hbadDR hrepeat)⟩

end LeanProofs.GowersSzemeredi
