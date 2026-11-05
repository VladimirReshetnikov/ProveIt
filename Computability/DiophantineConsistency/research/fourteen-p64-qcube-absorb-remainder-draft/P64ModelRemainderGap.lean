import P64RemainderGap
import Absorb88TwoNormGap

/-! Draft: two Pell norms imply the quotient witness is below the remainder. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace P64ModelRemainderGap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem remainder_gt (X Y s k eta zeta r g : V)
    (hX : 0<X) (hs : 0<s) (hY : s≤Y) (heta : 0<eta) (hzeta : 0<zeta)
    (hk : k=eta+zeta)
    (hfirst : let P := (X*Y)*Y; let ell := P*k
      (ell+r)*(ell+r)=1+ell*(ell+k))
    (hmain : g*g=1+delta (X*Y+Y)*(eta+Y*k)*(eta+Y*k)) : s<r := by
  let P : V := (X*Y)*Y
  let ell : V := P*k
  have hY0 : 0<Y := lt_of_lt_of_le hs hY
  have hnorm : (ell+r)*(ell+r)=1+P*(P+1)*k*k := by
    calc
      _=1+ell*(ell+k) := hfirst
      _=1+P*(P+1)*k*k := by dsimp [ell]; ring
  have hkgap : 8*P+4≤k := Absorb88TwoNormGap.gap X Y k eta zeta (ell+r) g hX hY0 heta hzeta hk hnorm hmain
  have hs1 : (1:DiffRing V)≤ι s := by rw [←map_one ι,ι_le_ι]; exact pos_iff_one_le.mp hs
  have hX1 : (1:DiffRing V)≤ι X := by rw [←map_one ι,ι_le_ι]; exact pos_iff_one_le.mp hX
  have hYr : (ι s : DiffRing V)≤ι Y := ι_le_ι.mpr hY
  have hYsq : (ι s : DiffRing V)*ι s≤ι Y*ι Y := mul_le_mul hYr hYr (ι_nonneg _) (ι_nonneg _)
  have hPge : (ι s : DiffRing V)*ι s≤ι P := by
    have hx := mul_nonneg (show (0:DiffRing V)≤ι X-1 by linarith)
      (show (0:DiffRing V)≤ι Y*ι Y from mul_nonneg (ι_nonneg _) (ι_nonneg _))
    simp only [P,map_mul]
    nlinarith only [hYsq,hx]
  have hP0 : (0:DiffRing V)≤ι P := ι_nonneg _
  have hk' : (8:DiffRing V)*ι P+4≤ι k := by
    have hh := ι_le_ι.mpr hkgap
    simpa only [map_add,map_mul,map_ofNat] using hh
  have hk1 : (1:DiffRing V)≤ι k := by nlinarith only [hk',hP0]
  have hell : (ι s : DiffRing V)*ι s≤ι ell := by
    have hm := mul_nonneg hP0 (show (0:DiffRing V)≤ι k-1 by linarith)
    simp only [ell,map_mul]
    nlinarith only [hPge,hm]
  have hklin : (2:DiffRing V)*ι s+1≤ι k := by
    have hm := mul_nonneg (ι_nonneg s) (show (0:DiffRing V)≤ι s-1 by linarith)
    nlinarith only [hk',hPge,hm]
  have hnring : ((ι ell : DiffRing V)+ι r)*((ι ell : DiffRing V)+ι r)=
      1+ι ell*(ι ell+ι k) := by
    change (ell+r)*(ell+r)=1+ell*(ell+k) at hfirst
    have hh := congrArg (fun x : V => (ι x : DiffRing V)) hfirst
    simpa only [map_add,map_mul,map_one] using hh
  apply ι_lt_ι.mp
  exact P64RemainderGap.remainder_gt (ι ell) (ι k) (ι s) (ι r)
    (ι_nonneg _) (ι_nonneg _) hell hklin hnring

#print axioms P64ModelRemainderGap.remainder_gt
end P64ModelRemainderGap
