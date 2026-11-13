import FirstRootBridge

/-! Source-only fact-level auxiliary witness proposal. The bounds `1<Q` and
`1<z*z` are explicit hypotheses, not derived from any graph zero here.
The imported five-square draft and all proofs below are uncompiled. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AuxRootModelDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing DirectFirstRootModelDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Auxiliary residual after replacing the old positive u by a direct y. -/
def directAux (z Q y : DiffRing V) : DiffRing V :=
  y*y-Q*(y*y-z*z)-1

/-- Original auxiliary residual, with y represented as z plus positive u. -/
def oldAux (z Q : DiffRing V) (u : V) : DiffRing V :=
  (z+ι u)*(z+ι u)-Q*(ι u*((z+ι u)+z))-1

theorem oldAux_eq_direct (z Q : DiffRing V) (u : V) :
    oldAux z Q u=directAux z Q (z+ι u) := by
  dsimp [oldAux,directAux]
  ring

/-- The auxiliary norm and two strict bounds force y²>z². -/
theorem square_gt_of_aux (z Q y : DiffRing V)
    (hQ : 1<Q) (hz : 1<z*z) (h : directAux z Q y=0) : z*z<y*y := by
  have hn : y*y-Q*(y*y-z*z)=1 := by
    exact sub_eq_zero.mp h
  have he : (Q-1)*(y*y-z*z)=z*z-1 := by nlinarith [hn]
  have hp : 0<(Q-1)*(y*y-z*z) := by rw [he]; exact sub_pos.mpr hz
  have hQpos : 0<Q-1 := sub_pos.mpr hQ
  by_contra hnot
  have hnonpos : y*y-z*z≤0 := by linarith
  have hbad := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hQpos) hnonpos
  linarith

/-- If y lies strictly above z and has larger square, y is positive. -/
theorem positive_of_above (z y : DiffRing V) (hzy : z<y)
    (hsq : z*z<y*y) : 0<y := by
  by_contra hnot
  have hy : y≤0 := le_of_not_gt hnot
  have h1 : 0≤y-z := sub_nonneg.mpr (le_of_lt hzy)
  have h2 : 0≤-(y+z) := by linarith
  have hprod := mul_nonneg h1 h2
  nlinarith

/-- A positive y with larger square lies strictly above z. -/
theorem above_of_positive (z y : DiffRing V) (hy : 0<y)
    (hsq : z*z<y*y) : z<y := by
  by_contra hnot
  have hzy : y≤z := le_of_not_gt hnot
  have h1 : 0≤z-y := sub_nonneg.mpr hzy
  have h2 : 0≤z+y := by linarith
  have hprod := mul_nonneg h1 h2
  nlinarith

/-- Proposed fixed-other-residual positive-coordinate equivalence. The strict
bounds are assumptions; proving them from the 78/79 graph norms is separate. -/
theorem positive_aux_coordinate_iff (first main strong guard z Q : DiffRing V)
    (hQ : 1<Q) (hz : 1<z*z) :
    (∃ u : V, 0<u ∧ fiveSquares first main (oldAux z Q u) strong guard=0) ↔
    (∃ y : V, 0<y ∧ fiveSquares first main (directAux z Q (ι y)) strong guard=0) := by
  constructor
  · rintro ⟨u,hu,hzero⟩
    rcases (fiveSquares_eq_zero_iff _ _ _ _ _).mp hzero with ⟨hf,hm,ha,hs,hg⟩
    have huR : (0 : DiffRing V)<ι u := by
      have h := (ι_lt_ι (a := (0:V)) (b := u)).mpr hu
      simpa only [map_zero] using h
    have hyz : z<z+ι u := lt_add_of_pos_right z huR
    have haux : directAux z Q (z+ι u)=0 := by
      rw [← oldAux_eq_direct]
      exact ha
    have hy : (0 : DiffRing V)<z+ι u :=
      positive_of_above z (z+ι u) hyz (square_gt_of_aux z Q (z+ι u) hQ hz haux)
    obtain ⟨y,hyrepr⟩ := (nonneg_iff).mp (le_of_lt hy)
    have hypos : 0<y := by
      apply (ι_lt_ι (a := (0:V)) (b := y)).mp
      simpa only [map_zero,← hyrepr] using hy
    have hyaux : directAux z Q (ι y)=0 := by rw [← hyrepr]; exact haux
    exact ⟨y,hypos,(fiveSquares_eq_zero_iff _ _ _ _ _).mpr ⟨hf,hm,hyaux,hs,hg⟩⟩
  · rintro ⟨y,hy,hzero⟩
    rcases (fiveSquares_eq_zero_iff _ _ _ _ _).mp hzero with ⟨hf,hm,ha,hs,hg⟩
    have hyR : (0 : DiffRing V)<ι y := by
      have h := (ι_lt_ι (a := (0:V)) (b := y)).mpr hy
      simpa only [map_zero] using h
    have hzy : z<ι y := above_of_positive z (ι y) hyR (square_gt_of_aux z Q (ι y) hQ hz ha)
    have hpos : (0 : DiffRing V)<ι y-z := sub_pos.mpr hzy
    obtain ⟨u,hurepr⟩ := (nonneg_iff).mp (le_of_lt hpos)
    have hupos : 0<u := by
      apply (ι_lt_ι (a := (0:V)) (b := u)).mp
      simpa only [map_zero,← hurepr] using hpos
    have hyrepr : z+ι u=ι y := by rw [← hurepr]; ring
    have haux : oldAux z Q u=0 := by
      rw [oldAux_eq_direct,hyrepr]
      exact ha
    exact ⟨u,hupos,(fiveSquares_eq_zero_iff _ _ _ _ _).mpr ⟨hf,hm,haux,hs,hg⟩⟩

end DiophantineConsistency.AuxRootModelDraft

#print axioms DiophantineConsistency.AuxRootModelDraft.positive_aux_coordinate_iff
