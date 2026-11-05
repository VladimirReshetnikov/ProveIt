import IndependentYBounds

/-! Generic free-main forward positivity in arithmetic difference rings. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainForward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem root_above_base (n c g x : DiffRing V)
    (hn : 2≤n) (hc : 3≤c) (hg : 0≤g) (hx : x<c)
    (hpell : g*g = 1+(n*n-1)*(c*c)) :
    x+(n-2)*c<g := by
  have hn1 : 0≤2*(n-1) := by linarith
  have hprod := mul_nonneg hn1 (sq_nonneg c)
  have hbase : 0≤(n-1)*c := mul_nonneg (by linarith) (by linarith)
  have hsq : ((n-1)*c)*((n-1)*c)<g*g := by nlinarith only [hpell,hprod]
  have hroot : (n-1)*c<g := by
    by_contra h
    have hle : g≤(n-1)*c := le_of_not_gt h
    have hh := mul_self_le_mul_self hg hle
    linarith
  nlinarith only [hroot,hx]

theorem positive_of_alignment (n c g x U H h : DiffRing V)
    (hn : 2≤n) (hc : 3≤c) (hg : 0≤g) (hx : x<c)
    (hU : 0<U) (hH : 0<H)
    (hpell : g*g = 1+(n*n-1)*(c*c))
    (halign : U*(g-(x+(n-2)*c))=H*h) : 0<h := by
  have hgap : 0<g-(x+(n-2)*c) := sub_pos.mpr (root_above_base n c g x hn hc hg hx hpell)
  have hp : 0<H*h := by rw [←halign]; exact mul_pos hU hgap
  by_contra hnpos
  have hle : h≤0 := le_of_not_gt hnpos
  have hnp := mul_nonpos_of_nonneg_of_nonpos hH.le hle
  linarith

theorem positive_of_pell_bound (n c g x U H h : DiffRing V)
    (hn : 2≤n) (hc : 3≤c) (hg : 0≤g) (hx : x≤n-2)
    (hU : 0<U) (hH : 0<H)
    (hpell : g*g = 1+(n*n-1)*(c*c))
    (halign : U*(g-(x+(n-2)*c))=H*h) : 0<h := by
  have hc_bound := IndependentYBounds.pell_c_bound n c g hn hc hg hpell
  have hxlt : x<c := by linarith
  exact positive_of_alignment n c g x U H h hn hc hg hxlt hU hH hpell halign

#print axioms FreeMainForward.root_above_base
#print axioms FreeMainForward.positive_of_alignment
#print axioms FreeMainForward.positive_of_pell_bound
end FreeMainForward
