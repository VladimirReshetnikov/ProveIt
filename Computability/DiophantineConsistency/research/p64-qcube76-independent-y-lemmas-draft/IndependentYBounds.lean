import P64QCube78GraphSplit

/-! Unchecked draft: discrete Pell size and auxiliary strictness lemmas. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace IndependentYBounds
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ModelArithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem pell_c_bound (n c g : DiffRing V)
    (hn : 2≤n) (hc : 3≤c) (hg : 0≤g)
    (hpell : g*g = 1+(n*n-1)*(c*c)) : 2*n≤c := by
  by_contra h
  have hclt : c<2*n := lt_of_not_ge h
  have hpos : 0<c*(2*n-c) := mul_pos (by linarith) (by linarith)
  have htop : g*g < (n*c)*(n*c) := by nlinarith only [hpell,hc]
  have hglt : g<n*c := by
    by_contra hbad
    have hge : n*c≤g := le_of_not_gt hbad
    have hncz : 0≤n*c := mul_nonneg (by linarith) (by linarith)
    have hsq := mul_self_le_mul_self hncz hge
    linarith
  have hdisc := model_discrete (n*c-g) (sub_pos.mpr hglt)
  have hgle : g≤n*c-1 := by linarith
  have hsq := mul_self_le_mul_self hg hgle
  have hlow : (n*c-1)*(n*c-1) < g*g := by nlinarith only [hpell,hpos]
  linarith

theorem strong_f_bound (n c g f idx : DiffRing V)
    (hn : 2≤n) (hc : 3≤c) (hg : 0≤g) (_hf : 1≤f) (hi : 1 ≤ idx)
    (hpell : g*g = 1+(n*n-1)*(c*c))
    (hstrong : (n*n-1)*(f*f-1)=(idx*(c*c))*(idx*(c*c))) : c+1<f*f := by
  have hcn := pell_c_bound n c g hn hc hg hpell
  have hdelta : 0≤n*n-1 := by nlinarith only [hn]
  have hc_ge : n≤c := by linarith
  have hp := mul_nonneg (sub_nonneg.mpr hc_ge) (show 0≤c+n by linarith)
  have hdelta_lt : n*n-1<c*c := by nlinarith only [hp]
  by_contra h
  have hff : f*f-1≤c := by linarith
  have h1 := mul_le_mul_of_nonneg_left hff hdelta
  have h2 := mul_lt_mul_of_pos_right hdelta_lt (show 0<c by linarith)
  have hc2 : c≤c*c := by nlinarith only [hc]
  have h3 := mul_le_mul_of_nonneg_left hc2 (show 0≤c*c by positivity)
  have hip := mul_nonneg (show 0 ≤ idx-1 by linarith) (sq_nonneg c)
  have hi2 : c*c ≤ idx*(c*c) := by nlinarith only [hip]
  have h4 := mul_self_le_mul_self (show 0≤c*c by positivity) hi2
  nlinarith only [hstrong,h1,h2,h3,h4,hc]

theorem strict_auxiliary (A c f V0 y z : DiffRing V)
    (hA : 2≤A) (hc : 3≤c) (_hf : 1≤f) (hy : 1≤y)
    (hsize : c+1<f*f) (hV : V0=f*f*z-c)
    (haux : A*(V0*V0-y*y)+y*y=1) : V0<y := by
  have hy2 : 1≤y*y := by nlinarith only [hy]
  have hcmp : V0*V0≤y*y := by
    by_contra h
    have hp := mul_pos (show 0<A by linarith) (show 0<V0*V0-y*y by linarith)
    nlinarith only [haux,hy2,hp]
  by_contra h
  have hge : y≤V0 := le_of_not_gt h
  have hmul := mul_nonneg (sub_nonneg.mpr hge) (show 0≤V0+y by linarith)
  have hsqeq : V0*V0=y*y := by nlinarith only [hcmp,hmul]
  have hprod : (V0-y)*(V0+y)=0 := by nlinarith only [hsqeq]
  have hdiff : V0-y=0 := (mul_eq_zero.mp hprod).resolve_right (ne_of_gt (by linarith : 0<V0+y))
  have heq : V0=y := sub_eq_zero.mp hdiff
  have hyone : y=1 := by rw [heq] at haux; nlinarith only [haux,hy]
  have hzprod : f*f*z=c+1 := by rw [heq,hyone] at hV; linarith
  have hzpos : 0<z := by
    by_contra h
    have hzle : z≤0 := le_of_not_gt h
    have hp := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg f) hzle
    nlinarith only [hp,hzprod,hc]
  have hzone : 1≤z := model_discrete z hzpos
  have hmul := mul_nonneg (sq_nonneg f) (show 0≤z-1 by linarith)
  nlinarith only [hmul,hzprod,hsize]

theorem old_root_ne_zero (A V0 y : DiffRing V)
    (hA : 2≤A) (haux : A*(V0*V0-y*y)+y*y=1) : y≠0 := by
  intro hy
  subst y
  simp only [mul_zero,_root_.sub_zero,add_zero] at haux
  have hV : V0≠0 := by
    intro h
    simp [h] at haux
  have hV1 : 1≤|V0| := DiscreteOrderedRingFacts.abs_ge_one model_discrete hV
  have hV2 : 1≤V0*V0 := by
    have ha := abs_mul_abs_self V0
    nlinarith [abs_nonneg V0]
  have hprod := mul_nonneg (show 0≤A-2 by linarith) (show 0≤V0*V0-1 by linarith)
  nlinarith only [haux,hA,hV2,hprod]

#print axioms IndependentYBounds.pell_c_bound
#print axioms IndependentYBounds.strong_f_bound
#print axioms IndependentYBounds.strict_auxiliary
#print axioms IndependentYBounds.old_root_ne_zero
end IndependentYBounds
