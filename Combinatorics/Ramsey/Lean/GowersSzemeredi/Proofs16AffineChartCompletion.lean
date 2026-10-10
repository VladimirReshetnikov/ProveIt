import GowersSzemeredi.Proofs16SandersLinearPart
import GowersSzemeredi.Proofs16FreimanImageRadiusExpansion

/-! Complete inactive values on a cell using a genuine local linear part.
Only active values are required to agree with the original map. Every
completion has the same local slope, including cells with no active point. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def affineChartAnchor {N : Nat} (C D : Finset (ZMod N)) (c : ZMod N) : ZMod N :=
  if h : (C ∩ D).Nonempty then h.choose else c

def affineChartOffset {N : Nat} (C D : Finset (ZMod N)) (theta : ZMod N → ZMod N)
    (_c : ZMod N) : ZMod N :=
  if h : (C ∩ D).Nonempty then theta h.choose else 0

def affineChartCompletion {N : Nat} (C D : Finset (ZMod N)) (theta psi : ZMod N → ZMod N)
    (c : ZMod N) (x : ZMod N) : ZMod N :=
  affineChartOffset C D theta c + psi (x-affineChartAnchor C D c)

/-- The base lies in the cell even when its active domain misses the cell. -/
theorem affine_chart_anchor_mem {N : Nat} (C D : Finset (ZMod N)) {c : ZMod N} (hc : c ∈ C) :
    affineChartAnchor C D c ∈ C := by
  unfold affineChartAnchor
  split_ifs with h
  · exact (Finset.mem_inter.mp h.choose_spec).1
  · exact hc

/-- The completion retains all actual active values. -/
theorem affine_chart_completion_agree {N : Nat} (C D : Finset (ZMod N))
    (theta psi : ZMod N → ZMod N) (c : ZMod N)
    (hdiff : ∀ a ∈ D, ∀ b ∈ D, theta a-theta b = psi (a-b))
    {x : ZMod N} (hx : x ∈ C) (hDx : x ∈ D) :
    affineChartCompletion C D theta psi c x = theta x := by
  have h : (C ∩ D).Nonempty := ⟨x,Finset.mem_inter.mpr ⟨hx,hDx⟩⟩
  have hb : h.choose ∈ D := (Finset.mem_inter.mp h.choose_spec).2
  unfold affineChartCompletion affineChartAnchor affineChartOffset
  rw [dif_pos h,dif_pos h]
  have he := hdiff x hDx h.choose hb
  linear_combination -he

/-- The map is Freiman-linear on the whole cell, including inactive points. -/
theorem affine_chart_completion_freiman {N : Nat} [NeZero N]
    (C D Gamma : Finset (ZMod N)) (theta psi : ZMod N → ZMod N)
    {c : ZMod N} (hc : c ∈ C) {rho : Real}
    (hpsi : IsFreimanLinearOn (bohr Gamma rho) psi)
    (hclose : ∀ x ∈ C, ∀ y ∈ C, x-y ∈ bohr Gamma rho) :
    IsFreimanLinearOn C (affineChartCompletion C D theta psi c) := by
  have hb := affine_chart_anchor_mem C D hc
  intro x1 x2 x3 x4 h1 h2 h3 h4 hadd
  have he := hpsi (x1-affineChartAnchor C D c) (x2-affineChartAnchor C D c)
    (x3-affineChartAnchor C D c) (x4-affineChartAnchor C D c)
    (hclose _ h1 _ hb) (hclose _ h2 _ hb) (hclose _ h3 _ hb) (hclose _ h4 _ hb)
    (by linear_combination hadd)
  dsimp only [affineChartCompletion]
  linear_combination he

/-- After recentering at any point of the cell, the slope is the original
linear part. This also holds when the cell has no active point. -/
theorem affine_chart_completion_translate {N : Nat} [NeZero N]
    (C D Gamma : Finset (ZMod N)) (theta psi : ZMod N → ZMod N)
    {c x t : ZMod N} (hc : c ∈ C) (hx : x ∈ C) (ht : t ∈ C) {rho : Real} (hr : 0 ≤ rho)
    (hpsi : IsFreimanLinearOn (bohr Gamma rho) psi) (hzero : psi 0 = 0)
    (hclose : ∀ a ∈ C, ∀ b ∈ C, a-b ∈ bohr Gamma rho) :
    affineChartCompletion C D theta psi c x = affineChartCompletion C D theta psi c t + psi (x-t) := by
  have hb := affine_chart_anchor_mem C D hc
  have he := hpsi (x-affineChartAnchor C D c) 0 (t-affineChartAnchor C D c) (x-t)
    (hclose _ hx _ hb) (zero_mem_bohr Gamma hr) (hclose _ ht _ hb) (hclose _ hx _ ht) (by ring)
  rw [hzero] at he
  dsimp only [affineChartCompletion]
  linear_combination he

/-- A completed frequency window still imposes every active original
frequency constraint, regardless of how inactive values are completed. -/
theorem completed_window_bohr_subset_active {N : Nat} [NeZero N] {k : Type*} [DecidableEq k]
    (J S : Finset k) (theta completed : k → ZMod N) (eta : Real)
    (hSJ : S ⊆ J) (heq : ∀ i ∈ S, completed i = theta i) :
    bohr (J.image completed) eta ⊆ bohr (S.image theta) eta := by
  intro y hy
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun r hr => ?_⟩
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hr
  have hmem : theta i ∈ J.image completed :=
    Finset.mem_image.mpr ⟨i,hSJ hi,heq i hi⟩
  exact (Finset.mem_filter.mp hy).2 _ hmem

/-- Apply the active-domain preservation to the concrete affine completion. -/
theorem affine_chart_window_bohr_subset {N : Nat} [NeZero N] {k : Type*} [DecidableEq k]
    (J S : Finset k) (C : Finset (ZMod N)) (D : k → Finset (ZMod N))
    (theta psi : k → ZMod N → ZMod N) (c : ZMod N) {x : ZMod N} (hx : x ∈ C)
    (eta : Real) (hSJ : S ⊆ J) (hDx : ∀ i ∈ S, x ∈ D i)
    (hdiff : ∀ i ∈ J, ∀ a ∈ D i, ∀ b ∈ D i, theta i a-theta i b = psi i (a-b)) :
    bohr (J.image fun i => affineChartCompletion C (D i) (theta i) (psi i) c x) eta ⊆
      bohr (S.image fun i => theta i x) eta := by
  exact completed_window_bohr_subset_active J S _ _ eta hSJ
    (fun i hi => affine_chart_completion_agree C (D i) (theta i) (psi i) c
      (hdiff i (hSJ hi)) hx (hDx i hi))

end LeanProofs.GowersSzemeredi
