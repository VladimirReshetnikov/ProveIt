import GowersSzemeredi.Proofs16GoodRepresentationImages
import GowersSzemeredi.Proofs16ColumnImageBridges
import GowersSzemeredi.Proofs16QuadImagePermutations

/-! Two good original 16-tuples compare a selected row with an alternative
original four-term representation. The helper spectra remain in the
intermediate domain and are removed only by the bounded-image theorem. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem representation_replacement_defect {N : Nat}
    (L : ZMod N → ZMod N → ZMod N) (b : Fin 4 → FourRepresentationTuple N)
    (i : Fin 4) (p : FourRepresentationTuple N) (y : ZMod N) :
    representationColumnMap L (b i) y-representationColumnMap L p y =
      if i=0 ∨ i=2 then
        columnAnchorEval (fun x => L x y) (columnAnchorList (flattenFourRepresentations b))-
          columnAnchorEval (fun x => L x y) (columnAnchorList (flattenFourRepresentations (Function.update b i p)))
      else
        columnAnchorEval (fun x => L x y) (columnAnchorList (flattenFourRepresentations (Function.update b i p)))-
          columnAnchorEval (fun x => L x y) (columnAnchorList (flattenFourRepresentations b)) := by
  rw [representationColumnMap_eq,representationColumnMap_eq]
  simp_rw [flattenFourRepresentations_eval]
  fin_cases i <;> simp [Function.update] <;> ring

/-- Compare an original alternative with a selected representation while
removing all three helper rows from its final endpoint domain. -/
theorem good_representation_replacement_image {N d K : Nat} [NeZero N]
    (X U : Finset (ZMod N)) (hUX : U ⊆ X)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    {rho : Real} (hrho : 0 < rho) (hK : 0 < K)
    (hcol : ∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) rho) (L x) ∧ L x 0 = 0)
    (q : Fin 4 → ZMod N) (b : Fin 4 → FourRepresentationTuple N) (i : Fin 4) (p : FourRepresentationTuple N)
    (hb : ∀ j, b j ∈ fourDifferenceRepresentations U (q j))
    (hp : p ∈ fourDifferenceRepresentations U (q i)) (hadd : q 0-q 1+q 2-q 3 = 0)
    (hgood : flattenFourRepresentations b ∉ columnTupleImageExceptions U T L rho K)
    (halt : flattenFourRepresentations (Function.update b i p) ∉ columnTupleImageExceptions U T L rho K) :
    ((bohr (representationColumnSpectrum T (b i) ∪ representationColumnSpectrum T p) (rho/4)).image
      (fun y => representationColumnMap L (b i) y-representationColumnMap L p y)).card ≤
        K*K*refinementKernelCap (8*d) (12*d) (rho/2) (rho/2) := by
  classical
  let sigma := rho/2
  let A := representationColumnSpectrum T (b i) ∪ representationColumnSpectrum T p
  let Uaux := (Finset.univ.erase i).biUnion fun j => representationColumnSpectrum T (b j)
  let D := bohr (A ∪ Uaux) sigma
  let G := fun y => columnAnchorEval (fun x => L x y) (columnAnchorList (flattenFourRepresentations b))
  let H := fun y => columnAnchorEval (fun x => L x y)
    (columnAnchorList (flattenFourRepresentations (Function.update b i p)))
  have hup : ∀ j, Function.update b i p j ∈ fourDifferenceRepresentations U (q j) := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa using hp
    · simpa only [Function.update_of_ne hj] using hb j
  have hrawG := good_flattened_representation_image U T L rho q b hb hadd hgood
  have hrawH := good_flattened_representation_image U T L rho q (Function.update b i p) hup hadd halt
  have hrows : ∀ y ∈ D, (∀ j, y ∈ bohr (representationColumnSpectrum T (b j)) sigma) ∧
      y ∈ bohr (representationColumnSpectrum T p) sigma := by
    intro y hy
    dsimp only [D,A] at hy
    rw [bohr_union,bohr_union] at hy
    obtain ⟨hend,haux⟩ := Finset.mem_inter.mp hy
    obtain ⟨hbi,hp'⟩ := Finset.mem_inter.mp hend
    refine ⟨?_,hp'⟩
    intro j
    by_cases hj : j = i
    · subst j
      exact hbi
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t ht => ?_⟩
      exact (Finset.mem_filter.mp haux).2 t (Finset.mem_biUnion.mpr
        ⟨j,Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩,ht⟩)
  have hG : (D.image G).card ≤ K := by
    apply (image_card_le_of_eq_on_subset D _ G G ?_ (fun _ _ => rfl)).trans hrawG
    intro y hy
    exact mem_bohr_flattened_representations T b sigma y (hrows y hy).1
  have hH : (D.image H).card ≤ K := by
    apply (image_card_le_of_eq_on_subset D _ H H ?_ (fun _ _ => rfl)).trans hrawH
    intro y hy
    apply mem_bohr_flattened_representations T (Function.update b i p) sigma y
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [Function.update_self] using (hrows y hy).2
    · simpa only [Function.update_of_ne hj] using (hrows y hy).1 j
  have himage : (D.image (fun y => representationColumnMap L (b i) y-representationColumnMap L p y)).card ≤ K*K := by
    by_cases hi : i=0 ∨ i=2
    · apply image_two_defects_card_le D _ G H ?_ hG hH
      intro y _
      simpa only [if_pos hi] using representation_replacement_defect L b i p y
    · apply image_two_defects_card_le D _ H G ?_ hH hG
      intro y _
      simpa only [if_neg hi] using representation_replacement_defect L b i p y
  have hbi := representation_column_data X U hUX T L rho hcol (hb i)
  have hpdata := representation_column_data X U hUX T L rho hcol hp
  have hA : A.card ≤ 8*d := (Finset.card_union_le _ _).trans (by have := hbi.1; have := hpdata.1; omega)
  have hUaux : Uaux.card ≤ 12*d := by
    apply Finset.card_biUnion_le.trans
    calc (∑ j ∈ Finset.univ.erase i, (representationColumnSpectrum T (b j)).card) ≤
        ∑ _j ∈ Finset.univ.erase i, 4*d := Finset.sum_le_sum fun j _ =>
          (representation_column_data X U hUX T L rho hcol (hb j)).1
      _ = _ := by simp; ring
  have hfbi : IsFreimanLinearOn (bohr A sigma) (representationColumnMap L (b i)) := by
    apply (column_freiman_smaller_radius _ _ (r := sigma) (by change rho/2 ≤ rho; linarith) hbi.2.1).mono
    intro y hy
    dsimp only [A] at hy
    rw [bohr_union] at hy
    exact (Finset.mem_inter.mp hy).1
  have hfp : IsFreimanLinearOn (bohr A sigma) (representationColumnMap L p) := by
    apply (column_freiman_smaller_radius _ _ (r := sigma) (by change rho/2 ≤ rho; linarith) hpdata.2.1).mono
    intro y hy
    dsimp only [A] at hy
    rw [bohr_union] at hy
    exact (Finset.mem_inter.mp hy).2
  have hf : IsFreimanLinearOn (bohr A sigma)
      (fun y => representationColumnMap L (b i) y-representationColumnMap L p y) := by
    intro y1 y2 y3 y4 h1 h2 h3 h4 he
    have ea := hfbi y1 y2 y3 y4 h1 h2 h3 h4 he
    have eb := hfp y1 y2 y3 y4 h1 h2 h3 h4 he
    linear_combination ea-eb
  have hsigma : 0 < sigma := by dsimp [sigma]; positivity
  have hresult := freiman_image_remove_frequencies_nat A Uaux _ hsigma hA hUaux (Nat.mul_pos hK hK) hf himage
  simpa only [A,sigma,show (rho/2)/2 = rho/4 by ring] using hresult

end LeanProofs.GowersSzemeredi
