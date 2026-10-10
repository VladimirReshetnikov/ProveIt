import GowersSzemeredi.Proofs16SourceCrossAnchorImages
import GowersSzemeredi.Proofs16OriginalEightFamilyCounts
import GowersSzemeredi.Proofs16BoundedImageQuadSymmetry

/-! Compose a cross-anchor comparison with two original alternative
comparisons. The final eight-tuple agreement uses only its endpoint
spectra; all variable-anchor constraints are removed explicitly. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The chosen difference map agrees, up to a bounded image, with the
original eight-column map from any two good alternatives at a valid anchor. -/
theorem original_eight_alternative_agreement_image {N d M J : Nat} [NeZero N]
    (X U C : Finset (ZMod N)) (hUX : U ⊆ X)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (f : ZMod N → FourRepresentationTuple N) (v : ZMod N → ZMod N)
    {rho sigma sigmaSrc : Real} (hsigma : 0 < sigma) (hsigmaR : sigma ≤ rho) (hsigmaSrc : sigma ≤ sigmaSrc)
    (hM : 0 < M) (hJ : 0 < J)
    (hcol : ∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) rho) (L x) ∧ L x 0 = 0)
    (hdata : ∀ x ∈ C, (normalizedRepresentationSpectrum T f x).card ≤ 8*d ∧
      IsFreimanLinearOn (bohr (normalizedRepresentationSpectrum T f x) rho) (normalizedRepresentationMap L f x) ∧
      normalizedRepresentationMap L f x 0 = 0)
    (h8 : ∀ q : PairedColumnTuple N, (∀ i, (q i).1 ∈ C ∧ (q i).2 ∈ C) → pairedColumnIndex q=0 →
      PairedColumnImageRelation (normalizedRepresentationSpectrum T f) (normalizedRepresentationMap L f) sigma J q)
    (a u : ZMod N) (hva : v a ∈ C) (hva' : v a+a ∈ C) (hu : u ∈ C) (hua : u+a ∈ C)
    (p q : FourRepresentationTuple N)
    (hp : p ∈ representationAgreementAlternatives U T L f (u+a) sigmaSrc M)
    (hq : q ∈ representationAgreementAlternatives U T L f u sigmaSrc M) :
    ((bohr (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a ∪
      (representationColumnSpectrum T p ∪ representationColumnSpectrum T q)) (sigma/2)).image
      (fun y => differenceAnchorMap (normalizedRepresentationMap L f) v a y-
        representationColumnMap L p y+representationColumnMap L q y)).card ≤
          M*M*J*refinementKernelCap (24*d) (16*d) sigma sigma := by
  classical
  let E := differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a ∪
    (representationColumnSpectrum T p ∪ representationColumnSpectrum T q)
  let A := normalizedRepresentationSpectrum T f u ∪ normalizedRepresentationSpectrum T f (u+a)
  let D := bohr (E ∪ A) sigma
  let g := fun y => differenceAnchorMap (normalizedRepresentationMap L f) v a y-
    representationColumnMap L (f (u+a)) y+representationColumnMap L (f u) y
  let h := fun y => representationColumnMap L (f (u+a)) y-representationColumnMap L p y
  let t := fun y => representationColumnMap L (f u) y-representationColumnMap L q y
  have hmem : ∀ y ∈ D,
      y ∈ bohr (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a) sigma ∧
      y ∈ bohr (representationColumnSpectrum T p) sigma ∧ y ∈ bohr (representationColumnSpectrum T q) sigma ∧
      y ∈ bohr (normalizedRepresentationSpectrum T f u) sigma ∧
      y ∈ bohr (normalizedRepresentationSpectrum T f (u+a)) sigma := by
    intro y hy
    dsimp only [D] at hy
    rw [bohr_union E A] at hy
    obtain ⟨he,ha⟩ := Finset.mem_inter.mp hy
    dsimp only [E] at he
    rw [bohr_union (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a)
      (representationColumnSpectrum T p ∪ representationColumnSpectrum T q)] at he
    obtain ⟨hpsi,hpq⟩ := Finset.mem_inter.mp he
    rw [bohr_union (representationColumnSpectrum T p) (representationColumnSpectrum T q)] at hpq
    dsimp only [A] at ha
    rw [bohr_union (normalizedRepresentationSpectrum T f u) (normalizedRepresentationSpectrum T f (u+a))] at ha
    exact ⟨hpsi,(Finset.mem_inter.mp hpq).1,(Finset.mem_inter.mp hpq).2,
      (Finset.mem_inter.mp ha).1,(Finset.mem_inter.mp ha).2⟩
  have hg : (D.image g).card ≤ J := by
    have hsrc := source_cross_anchor_image C T L f v sigma a u hva hva' hu hua h8
    apply (image_card_le_of_eq_on_subset D _ g g ?_ (fun _ _ => rfl)).trans hsrc
    intro y hy
    rw [bohr_union (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a)
      (normalizedRepresentationSpectrum T f u ∪ normalizedRepresentationSpectrum T f (u+a))]
    refine Finset.mem_inter.mpr ⟨(hmem y hy).1,?_⟩
    rw [bohr_union (normalizedRepresentationSpectrum T f u) (normalizedRepresentationSpectrum T f (u+a))]
    exact Finset.mem_inter.mpr ⟨(hmem y hy).2.2.2.1,(hmem y hy).2.2.2.2⟩
  have hown : ∀ x y, y ∈ bohr (normalizedRepresentationSpectrum T f x) sigma →
      y ∈ bohr (representationColumnSpectrum T (f x)) sigma := by
    intro x y hy
    rw [normalizedRepresentationSpectrum,bohr_union] at hy
    exact (Finset.mem_inter.mp hy).1
  have hh : (D.image h).card ≤ M := by
    apply (image_card_le_of_eq_on_subset D _ h h ?_ (fun _ _ => rfl)).trans (Finset.mem_filter.mp hp).2
    intro y hy
    apply bohr_mono_radius _ hsigmaSrc
    rw [bohr_union]
    exact Finset.mem_inter.mpr ⟨hown _ y (hmem y hy).2.2.2.2,(hmem y hy).2.1⟩
  have ht : (D.image t).card ≤ M := by
    apply (image_card_le_of_eq_on_subset D _ t t ?_ (fun _ _ => rfl)).trans (Finset.mem_filter.mp hq).2
    intro y hy
    apply bohr_mono_radius _ hsigmaSrc
    rw [bohr_union]
    exact Finset.mem_inter.mpr ⟨hown _ y (hmem y hy).2.2.2.1,(hmem y hy).2.2.1⟩
  have hng : (D.image (fun y => -g y)).card ≤ J := by
    rw [finite_image_neg_card]
    exact hg
  have himage := image_three_defects_card_le D
    (fun y => differenceAnchorMap (normalizedRepresentationMap L f) v a y-representationColumnMap L p y+representationColumnMap L q y)
    h t (fun y => -g y) (by intro y _; dsimp [h,t,g]; ring) hh ht hng
  have hpsi := difference_anchor_map_data C (normalizedRepresentationSpectrum T f)
    (normalizedRepresentationMap L f) v rho hdata hva hva'
  have hpdata := representation_column_data X U hUX T L rho hcol (Finset.mem_filter.mp hp).1
  have hqdata := representation_column_data X U hUX T L rho hcol (Finset.mem_filter.mp hq).1
  have hE : E.card ≤ 24*d := by
    have h0 := Finset.card_union_le (representationColumnSpectrum T p) (representationColumnSpectrum T q)
    have h1 := Finset.card_union_le (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a)
      (representationColumnSpectrum T p ∪ representationColumnSpectrum T q)
    have hp0 := hpdata.1
    have hq0 := hqdata.1
    have hpsi0 := hpsi.1
    dsimp only [E]
    omega
  have hA : A.card ≤ 16*d := (Finset.card_union_le _ _).trans (by
    have := (hdata u hu).1
    have := (hdata (u+a) hua).1
    omega)
  have hePsi : bohr E sigma ⊆ bohr (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a) sigma := by
    intro y hy
    dsimp only [E] at hy
    rw [bohr_union] at hy
    exact (Finset.mem_inter.mp hy).1
  have heP : bohr E sigma ⊆ bohr (representationColumnSpectrum T p) sigma := by
    intro y hy
    dsimp only [E] at hy
    rw [bohr_union (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a)
      (representationColumnSpectrum T p ∪ representationColumnSpectrum T q)] at hy
    have hpq := (Finset.mem_inter.mp hy).2
    rw [bohr_union (representationColumnSpectrum T p) (representationColumnSpectrum T q)] at hpq
    exact (Finset.mem_inter.mp hpq).1
  have heQ : bohr E sigma ⊆ bohr (representationColumnSpectrum T q) sigma := by
    intro y hy
    dsimp only [E] at hy
    rw [bohr_union (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a)
      (representationColumnSpectrum T p ∪ representationColumnSpectrum T q)] at hy
    have hpq := (Finset.mem_inter.mp hy).2
    rw [bohr_union (representationColumnSpectrum T p) (representationColumnSpectrum T q)] at hpq
    exact (Finset.mem_inter.mp hpq).2
  have hfPsi := (column_freiman_smaller_radius _ _ hsigmaR hpsi.2.1).mono hePsi
  have hfP := (column_freiman_smaller_radius _ _ hsigmaR hpdata.2.1).mono heP
  have hfQ := (column_freiman_smaller_radius _ _ hsigmaR hqdata.2.1).mono heQ
  have hf : IsFreimanLinearOn (bohr E sigma)
      (fun y => differenceAnchorMap (normalizedRepresentationMap L f) v a y-representationColumnMap L p y+representationColumnMap L q y) := by
    intro y1 y2 y3 y4 h1 h2 h3 h4 he
    have ep := hfPsi y1 y2 y3 y4 h1 h2 h3 h4 he
    have ea := hfP y1 y2 y3 y4 h1 h2 h3 h4 he
    have eb := hfQ y1 y2 y3 y4 h1 h2 h3 h4 he
    linear_combination ep-ea+eb
  exact freiman_image_remove_frequencies_nat E A _ hsigma hE hA
    (Nat.mul_pos (Nat.mul_pos hM hM) hJ) hf himage

end LeanProofs.GowersSzemeredi
