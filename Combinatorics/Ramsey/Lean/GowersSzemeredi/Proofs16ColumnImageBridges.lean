import GowersSzemeredi.Proofs16RelationWordImages
import GowersSzemeredi.Proofs16BoundedImageRemoveFrequencies

/-! A common bridge combines two bounded-image quadruple relations. The
bridge frequencies are retained in the intermediate domain and then removed
by the linear-cap half-radius theorem. This is the image-control mechanism
in Claim 7.3, with explicit endpoint and auxiliary frequency budgets. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnQuadSpectrum {N : Nat} (T : ZMod N → Finset (ZMod N))
    (a b c d : ZMod N) : Finset (ZMod N) := (T a ∪ T b) ∪ (T c ∪ T d)

theorem column_quad_common_domain_eq_bohr {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (rho : Real) (a b c d : ZMod N) :
    columnQuadCommonDomain T rho a b c d = bohr (columnQuadSpectrum T a b c d) rho := by
  ext y
  simp only [columnQuadCommonDomain, columnQuadSpectrum, bohr_union,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  tauto

theorem column_quad_spectrum_card {N d : Nat}
    (T : ZMod N → Finset (ZMod N)) (a b c e : ZMod N)
    (ha : (T a).card ≤ d) (hb : (T b).card ≤ d)
    (hc : (T c).card ≤ d) (he : (T e).card ≤ d) :
    (columnQuadSpectrum T a b c e).card ≤ 4*d := by
  have hab := Finset.card_union_le (T a) (T b)
  have hce := Finset.card_union_le (T c) (T e)
  have h := Finset.card_union_le (T a ∪ T b) (T c ∪ T e)
  dsimp only [columnQuadSpectrum]
  omega

/-- A difference has at most the product of the two image cardinalities. -/
theorem image_two_defects_card_le {V H : Type*} [AddCommGroup H] [DecidableEq H]
    (D : Finset V) (f g h : V → H) (he : ∀ x ∈ D, f x = g x-h x)
    {K J : Nat} (hg : (D.image g).card ≤ K) (hh : (D.image h).card ≤ J) :
    (D.image f).card ≤ K*J := by
  let P := D.image g ×ˢ D.image h
  have hsub : D.image f ⊆ P.image (fun p => p.1-p.2) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨(g x,h x),
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem g hx, Finset.mem_image_of_mem h hx⟩,
      (he x hx).symm⟩
  calc (D.image f).card ≤ (P.image (fun p => p.1-p.2)).card := Finset.card_le_card hsub
    _ ≤ P.card := Finset.card_image_le
    _ = (D.image g).card*(D.image h).card := Finset.card_product _ _
    _ ≤ K*J := Nat.mul_le_mul hg hh

/-- Quadruple defects are Freiman-linear on their actual endpoint domain. -/
theorem column_quad_defect_freiman {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (rho : Real) (a b c d : ZMod N)
    (hL : ∀ x ∈ ({a,b,c,d} : Finset (ZMod N)), IsFreimanLinearOn (bohr (T x) rho) (L x)) :
    IsFreimanLinearOn (bohr (columnQuadSpectrum T a b c d) rho) (columnQuadDefect L a b c d) := by
  have hm : ∀ y ∈ bohr (columnQuadSpectrum T a b c d) rho,
      y ∈ bohr (T a) rho ∧ y ∈ bohr (T b) rho ∧ y ∈ bohr (T c) rho ∧ y ∈ bohr (T d) rho := by
    intro y hy
    rw [←column_quad_common_domain_eq_bohr] at hy
    exact (Finset.mem_filter.mp hy).2
  intro y1 y2 y3 y4 h1 h2 h3 h4 he
  have ea := hL a (by simp) y1 y2 y3 y4 (hm y1 h1).1 (hm y2 h2).1 (hm y3 h3).1 (hm y4 h4).1 he
  have eb := hL b (by simp) y1 y2 y3 y4 (hm y1 h1).2.1 (hm y2 h2).2.1 (hm y3 h3).2.1 (hm y4 h4).2.1 he
  have ec := hL c (by simp) y1 y2 y3 y4 (hm y1 h1).2.2.1 (hm y2 h2).2.2.1 (hm y3 h3).2.2.1 (hm y4 h4).2.2.1 he
  have ed := hL d (by simp) y1 y2 y3 y4 (hm y1 h1).2.2.2 (hm y2 h2).2.2.2 (hm y3 h3).2.2.2 (hm y4 h4).2.2.2 he
  dsimp only [columnQuadDefect]
  linear_combination ea-eb-ec+ed

/-- A shared pair of bridge indices removes all auxiliary spectra at half
radius, with image cap `K*J*refinementKernelCap (4d) (2d) rho rho`. -/
theorem column_quad_image_bridge {N d K J : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    {rho : Real} (hrho : 0 < rho) (hK : 0 < K) (hJ : 0 < J)
    (a b c e u v : ZMod N)
    (hT : ∀ x ∈ ({a,b,c,e,u,v} : Finset (ZMod N)), (T x).card ≤ d)
    (hL : ∀ x ∈ ({a,b,c,e} : Finset (ZMod N)), IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hab : ColumnQuadImageRelation T L rho K a b u v)
    (hce : ColumnQuadImageRelation T L rho J c e u v) :
    ColumnQuadImageRelation T L (rho/2) (K*J*refinementKernelCap (4*d) (2*d) rho rho) a b c e := by
  let E := columnQuadSpectrum T a b c e
  let U := T u ∪ T v
  let D := bohr (E ∪ U) rho
  have hmem : ∀ y ∈ D, y ∈ bohr (T a) rho ∧ y ∈ bohr (T b) rho ∧
      y ∈ bohr (T c) rho ∧ y ∈ bohr (T e) rho ∧ y ∈ bohr (T u) rho ∧ y ∈ bohr (T v) rho := by
    intro y hy
    simp only [D, E, U, columnQuadSpectrum, bohr_union, Finset.mem_inter] at hy
    tauto
  have hg : (D.image (columnQuadDefect L a b u v)).card ≤ K := by
    apply (image_card_le_of_eq_on_subset D (columnQuadCommonDomain T rho a b u v)
      _ _ ?_ (fun _ _ => rfl)).trans hab
    intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem y hy).1,
      (hmem y hy).2.1, (hmem y hy).2.2.2.2.1, (hmem y hy).2.2.2.2.2⟩
  have hh : (D.image (columnQuadDefect L c e u v)).card ≤ J := by
    apply (image_card_le_of_eq_on_subset D (columnQuadCommonDomain T rho c e u v)
      _ _ ?_ (fun _ _ => rfl)).trans hce
    intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem y hy).2.2.1,
      (hmem y hy).2.2.2.1, (hmem y hy).2.2.2.2.1, (hmem y hy).2.2.2.2.2⟩
  have himage := image_two_defects_card_le D (columnQuadDefect L a b c e)
    (columnQuadDefect L a b u v) (columnQuadDefect L c e u v)
    (by intro y _; dsimp [columnQuadDefect]; ring) hg hh
  have hE : E.card ≤ 4*d := column_quad_spectrum_card T a b c e
    (hT a (by simp)) (hT b (by simp)) (hT c (by simp)) (hT e (by simp))
  have hU : U.card ≤ 2*d := by
    have h := Finset.card_union_le (T u) (T v)
    have hu := hT u (by simp)
    have hv := hT v (by simp)
    dsimp [U]
    omega
  have hbound := freiman_image_remove_frequencies_nat E U (columnQuadDefect L a b c e)
    hrho hE hU (Nat.mul_pos hK hJ) (column_quad_defect_freiman T L rho a b c e hL) himage
  simpa only [ColumnQuadImageRelation, column_quad_common_domain_eq_bohr, E] using hbound

/-- Two small forbidden sets cannot cover the bridge candidates. -/
theorem exists_bridge_avoiding_two_failures {V : Type*} [DecidableEq V]
    (B : Finset V) (P Q : V → Prop) [DecidablePred P] [DecidablePred Q]
    (hsmall : (B.filter fun u => ¬P u).card+(B.filter fun u => ¬Q u).card < B.card) :
    ∃ u ∈ B, P u ∧ Q u := by
  by_contra h
  have hsub : B ⊆ (B.filter fun u => ¬P u) ∪ (B.filter fun u => ¬Q u) := by
    intro u hu
    have hn : ¬(P u ∧ Q u) := by intro hpq; exact h ⟨u,hu,hpq⟩
    by_cases hp : P u
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu, fun hq => hn ⟨hp,hq⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu,hp⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

end LeanProofs.GowersSzemeredi
