import GowersSzemeredi.Proofs16OriginalEightDomainExpansion
import GowersSzemeredi.Proofs16SmallImageRelations
import GowersSzemeredi.Proofs16SelectedColumnExtensions

/-! Exact compatibility and original eight-tuple agreement from small images.
The prime-modulus hypothesis removes the bounded defect on a radius divided
by the common image cap. The original tuples and all endpoint frequencies
are retained; there is no loss depending on the size of the tuple family. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Bounded quadruple defects give exact compatibility of the two difference
maps on their natural common domain at the divided radius. -/
theorem column_quad_image_relation_exact {N K : Nat} [NeZero N] [Fact N.Prime]
    (S : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {rho : Real} (hr : 0 ≤ rho)
    (hL : ∀ x ∈ S, IsFreimanLinearOn (bohr (T x) rho) (L x) ∧ L x 0 = 0)
    {a b c e : ZMod N} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (he : e ∈ S)
    (himage : ColumnQuadImageRelation T L rho K a b c e) (hKN : K < N) :
    ColumnPairCompatible T L (rho / K) (a,b) (c,e) := by
  have hf := column_quad_defect_freiman T L rho a b c e (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (hL _ ha).1
    · exact (hL _ hb).1
    · exact (hL _ hc).1
    · exact (hL _ he).1)
  have hf0 : columnQuadDefect L a b c e 0 = 0 := by
    simp [columnQuadDefect, (hL _ ha).2, (hL _ hb).2, (hL _ hc).2, (hL _ he).2]
  have hcard : ((bohr (columnQuadSpectrum T a b c e) rho).image
      (columnQuadDefect L a b c e)).card ≤ K := by
    simpa only [ColumnQuadImageRelation, column_quad_common_domain_eq_bohr] using himage
  intro y hy hy'
  have hdom : y ∈ bohr (columnQuadSpectrum T a b c e) (rho / K) := by
    simpa only [columnQuadSpectrum, columnDifferenceSpectrum, bohr_union, Finset.mem_inter]
      using And.intro hy hy'
  have hz := freiman_small_image_zero _ hr _ hf hf0 hcard hKN y hdom
  dsimp only [columnQuadDefect] at hz
  dsimp only [columnDifferenceMap]
  linear_combination hz

/-- Exact original eight-tuple agreement on the natural intersection of
one chosen map's domain and the eight original column domains. -/
def originalEightExactAgreementSet {N : Nat} [NeZero N]
    (U : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (Tpsi : Finset (ZMod N))
    (psi : ZMod N → ZMod N) (a : ZMod N) (rho : Real) : Finset (ColumnAnchorTuple N 7) :=
  (columnAnchorFibre U 7 a).filter fun t =>
    ∀ y ∈ bohr (Tpsi ∪ columnListSpectrum T (columnAnchorList t)) rho,
      psi y = columnAnchorEval (fun x => L x y) (columnAnchorList t)

/-- Every tuple in the bounded-image family is in the exact family at the
same divided radius. No tuples, endpoint spectra or density are lost. -/
theorem original_eight_bounded_agreement_exact {N d s K : Nat} [NeZero N] [Fact N.Prime]
    (X U : Finset (ZMod N)) (hUX : U ⊆ X)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (Tpsi : Finset (ZMod N)) (psi : ZMod N → ZMod N) (a : ZMod N)
    {rho : Real} (hr : 0 ≤ rho) (hTpsi : Tpsi.card ≤ s)
    (hpsi : IsFreimanLinearOn (bohr Tpsi rho) psi) (hpsi0 : psi 0 = 0)
    (hcol : ∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) rho) (L x) ∧ L x 0 = 0)
    (hKN : K < N) :
    originalEightAgreementSet U T L Tpsi psi a rho K ⊆
      originalEightExactAgreementSet U T L Tpsi psi a (rho / K) := by
  intro t ht
  obtain ⟨hfibre,himage⟩ := Finset.mem_filter.mp ht
  have hdata := original_eight_endpoint_data X U hUX T L Tpsi psi rho hTpsi hpsi
    (fun x hx => ⟨(hcol x hx).1,(hcol x hx).2.1⟩) hfibre
  have hzero : (psi 0 - columnAnchorEval (fun x => L x 0) (columnAnchorList t)) = 0 := by
    rw [hpsi0, columnAnchorEval_zero _ _ (fun x hx =>
      (hcol x (hUX ((Finset.mem_filter.mp hfibre).2.1 x hx))).2.2), sub_zero]
  refine Finset.mem_filter.mpr ⟨hfibre, fun y hy => ?_⟩
  have hz := freiman_small_image_zero _ hr _ hdata.2 hzero himage hKN y hy
  exact sub_eq_zero.mp hz

/-- Enlarging the uniform image cap preserves every original tuple. -/
theorem original_eight_agreement_cap_mono {N K J : Nat} [NeZero N]
    (U : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (Tpsi : Finset (ZMod N))
    (psi : ZMod N → ZMod N) (a : ZMod N) (rho : Real) (hKJ : K ≤ J) :
    originalEightAgreementSet U T L Tpsi psi a rho K ⊆
      originalEightAgreementSet U T L Tpsi psi a rho J := by
  intro t ht
  obtain ⟨hf, hi⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨hf, hi.trans hKJ⟩

/-- The full N^7 source mass survives conversion to exact agreement. -/
theorem original_eight_exact_agreement_mass {N d s K : Nat} [NeZero N] [Fact N.Prime]
    (X U : Finset (ZMod N)) (hUX : U ⊆ X)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (Tpsi : Finset (ZMod N)) (psi : ZMod N → ZMod N) (a : ZMod N)
    {rho gamma : Real} (hr : 0 ≤ rho) (hTpsi : Tpsi.card ≤ s)
    (hpsi : IsFreimanLinearOn (bohr Tpsi rho) psi) (hpsi0 : psi 0 = 0)
    (hcol : ∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) rho) (L x) ∧ L x 0 = 0)
    (hKN : K < N)
    (hmass : gamma * (N : Real)^7 ≤ (originalEightAgreementSet U T L Tpsi psi a rho K).card) :
    gamma * (N : Real)^7 ≤ (originalEightExactAgreementSet U T L Tpsi psi a (rho / K)).card := by
  exact hmass.trans (Nat.cast_le.mpr (Finset.card_le_card
    (original_eight_bounded_agreement_exact X U hUX T L Tpsi psi a hr hTpsi hpsi hpsi0 hcol hKN)))

end LeanProofs.GowersSzemeredi
