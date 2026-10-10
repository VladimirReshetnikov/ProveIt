import GowersSzemeredi.Proofs16JointRepresentativeSelection
import GowersSzemeredi.Proofs16GoodRepresentationImages
import GowersSzemeredi.Proofs16SelectedProgressionMaps

/-! Actual normalized progression maps selected simultaneously for their
quadruple images and for many original alternatives in every queried row.
Repeated progression indices are explicitly charged as exceptions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def progressionJointRepresentationFailures {N : Nat} [NeZero N]
    (U C : Finset (ZMod N)) (f : ZMod N → FourRepresentationTuple N)
    (Bad : Finset (ColumnAnchorTuple N 15)) (kappa : Real) : Finset (Fin 4 → ZMod N) :=
  jointRepresentationQueryFailures U ((progressionAdditiveQuadruples C).filter Function.Injective) f Bad kappa ∪
    (progressionAdditiveQuadruples C).filter fun q => ¬Function.Injective q

/-- The same actual maps have controlled image failures and many original
alternative representations on every nonexceptional additive query. -/
theorem exists_joint_selected_progression_maps {N d K : Nat} [NeZero N]
    (X U C : Finset (ZMod N)) (hUX : U ⊆ X) (h0 : (0 : ZMod N) ∈ C)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N) (rho : Real)
    (hcol : ∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) rho) (L x) ∧ L x 0 = 0)
    {kappa epsilon : Real} (hk : 0 < kappa) (hk1 : kappa ≤ 1)
    (hrep : ∀ x ∈ C, kappa*(N : Real)^3 ≤ (fourDifferenceRepresentations U x).card)
    (hbad : ((columnTupleImageExceptions U T L rho K).card : Real) ≤ epsilon*(N : Real)^15/2) :
    ∃ f : ZMod N → FourRepresentationTuple N,
      (∀ x ∈ C, f x ∈ fourDifferenceRepresentations U x) ∧
      (∀ x ∈ C, (normalizedRepresentationSpectrum T f x).card ≤ 8*d ∧
        IsFreimanLinearOn (bohr (normalizedRepresentationSpectrum T f x) rho) (normalizedRepresentationMap L f x) ∧
        normalizedRepresentationMap L f x 0 = 0) ∧
      (∀ y, normalizedRepresentationMap L f 0 y = 0) ∧
      ((progressionJointRepresentationFailures U C f (columnTupleImageExceptions U T L rho K) kappa).card : Real) ≤
        (9*epsilon/(2*kappa^5))*(N : Real)^3+6*(N : Real)^2 ∧
      progressionMapImageFailures C (normalizedRepresentationSpectrum T f) (normalizedRepresentationMap L f) (rho/2) K ⊆
        progressionJointRepresentationFailures U C f (columnTupleImageExceptions U T L rho K) kappa ∧
      ∀ q ∈ progressionAdditiveQuadruples C,
        q ∉ progressionJointRepresentationFailures U C f (columnTupleImageExceptions U T L rho K) kappa →
        flattenFourRepresentations (fun j => f (q j)) ∉ columnTupleImageExceptions U T L rho K ∧
        ∀ i, kappa*(N : Real)^3/2 ≤ (((fourDifferenceRepresentations U (q i)).filter
          fun p => flattenFourRepresentations (Function.update (fun j => f (q j)) i p) ∉
            columnTupleImageExceptions U T L rho K).card : Real) := by
  classical
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let Q := progressionAdditiveQuadruples C
  let Qd := Q.filter Function.Injective
  let Bad := columnTupleImageExceptions U T L rho K
  have hQd : ∀ q ∈ Qd, (∀ j, q j ∈ C) ∧ Function.Injective q := by
    intro q hq
    obtain ⟨hqQ,hi⟩ := Finset.mem_filter.mp hq
    exact ⟨(Finset.mem_filter.mp hqQ).2.1,hi⟩
  obtain ⟨f,hvalid,hbadD,hgoodD⟩ := exists_joint_progression_representatives U C hk hk1 hrep Qd hQd Bad
  have hgood : ∀ q ∈ Q, q ∉ progressionJointRepresentationFailures U C f Bad kappa →
      flattenFourRepresentations (fun j => f (q j)) ∉ Bad ∧
      ∀ i, kappa*(N : Real)^3/2 ≤ (((fourDifferenceRepresentations U (q i)).filter
        fun p => flattenFourRepresentations (Function.update (fun j => f (q j)) i p) ∉ Bad).card : Real) := by
    intro q hq hnot
    have hi : Function.Injective q := by
      by_contra hninj
      exact hnot (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hq,hninj⟩))
    apply hgoodD q (Finset.mem_filter.mpr ⟨hq,hi⟩)
    intro hjoint
    exact hnot (Finset.mem_union_left _ hjoint)
  have hcountD : ((jointRepresentationQueryFailures U Qd f Bad kappa).card : Real) ≤
      (9*epsilon/(2*kappa^5))*(N : Real)^3 := by
    have hscaled := mul_le_mul_of_nonneg_left hbad (by norm_num : (0 : Real) ≤ 9)
    have hdiv := div_le_div_of_nonneg_right hscaled (by positivity : (0 : Real) ≤ kappa^5*(N : Real)^12)
    have heq : (9*(epsilon*(N : Real)^15/2))/(kappa^5*(N : Real)^12) =
        (9*epsilon/(2*kappa^5))*(N : Real)^3 := by field_simp
    exact hbadD.trans (by simpa only [Bad,heq] using hdiv)
  have hrepeat : ((Q.filter fun q => ¬Function.Injective q).card : Real) ≤ 6*(N : Real)^2 := by
    exact_mod_cast repeated_additive_quadruples_card_le Q (fun q hq => (Finset.mem_filter.mp hq).2.2)
  have hcount : ((progressionJointRepresentationFailures U C f Bad kappa).card : Real) ≤
      (9*epsilon/(2*kappa^5))*(N : Real)^3+6*(N : Real)^2 := by
    have hle : ((progressionJointRepresentationFailures U C f Bad kappa).card : Real) ≤
        (jointRepresentationQueryFailures U Qd f Bad kappa).card+(Q.filter fun q => ¬Function.Injective q).card := by
      exact_mod_cast Finset.card_union_le _ _
    exact hle.trans (add_le_add hcountD hrepeat)
  have hsub : progressionMapImageFailures C (normalizedRepresentationSpectrum T f)
      (normalizedRepresentationMap L f) (rho/2) K ⊆ progressionJointRepresentationFailures U C f Bad kappa := by
    intro q hq
    obtain ⟨hqQ,hfail⟩ := Finset.mem_filter.mp hq
    by_contra hnot
    have hqC := (Finset.mem_filter.mp hqQ).2.1
    have hadd := (Finset.mem_filter.mp hqQ).2.2
    have hflat := (hgood q hqQ hnot).1
    have himage := good_flattened_representation_image U T L rho q (fun j => f (q j))
      (fun j => hvalid _ (hqC j)) hadd hflat
    exact hfail (normalized_quad_image_transfer T L f q (rho/2) himage)
  exact ⟨f,hvalid,normalized_representation_column_data X U C hUX h0 T L rho hcol f hvalid,
    normalizedRepresentationMap_index_zero L f,hcount,hsub,hgood⟩

end LeanProofs.GowersSzemeredi
