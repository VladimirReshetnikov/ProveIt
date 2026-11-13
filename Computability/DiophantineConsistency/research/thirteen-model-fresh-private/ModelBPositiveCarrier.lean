import DiophantineConsistency.ModelArithmetic

/-! Draft conditional carrier construction, using a supplied signed-ordinate
residue and ordinary auxiliary norm. No graph/port/iPRA bridge is claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ModelBPositiveCarrier
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ModelDifferenceRing
open DiophantineConsistency.ModelArithmetic
open DiophantineConsistency.DiscreteOrderedRingFacts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Generic auxiliary norm bounds, stated directly for the model ring. -/
theorem aux_estimates {S W y : DiffRing V} (hS : 2≤S)
    (hn : S^2*W^2-(S^2-1)*y^2=1) : y≠0 ∧ |y|<2*|W| := by
  have hS2 : 4≤S^2 := by nlinarith
  have hW : W≠0 := by
    intro hW
    rw [hW] at hn
    have hm := mul_nonneg (by linarith : (0:DiffRing V)≤S^2-1) (sq_nonneg y)
    nlinarith
  have hW2 : 1≤W^2 := model_discrete _ (pow_pos (abs_pos.mpr hW) 2 |>.trans_eq (sq_abs W))
  have hy : y≠0 := by
    intro hy
    rw [hy] at hn
    have hm := mul_le_mul_of_nonneg_right hS2 (sq_nonneg W)
    nlinarith
  refine ⟨hy,?_⟩
  have hsq : y^2<4*W^2 := by
    by_contra h
    push_neg at h
    have h1 := mul_nonneg (by linarith : (0:DiffRing V)≤S^2-1)
      (by linarith : (0:DiffRing V)≤y^2-4*W^2)
    have h2 := mul_nonneg (by linarith : (0:DiffRing V)≤3*S^2-4) (sq_nonneg W)
    nlinarith only [hn,h1,h2]
  by_contra h
  push_neg at h
  have h1 := mul_nonneg (by linarith : (0:DiffRing V)≤|y|-2*|W|)
    (show (0:DiffRing V)≤|y|+2*|W| by positivity)
  nlinarith [sq_abs y,sq_abs W]

/-- Generic positivity after recovering the signed affine carrier quotient. -/
theorem affine_carrier_pos {b G W y m : DiffRing V} (hb : 0<b) (hG : 0<G)
    (hsmall : -2*W<y) (hy : y=1+4*(b*(m-W^2*G)-G)) : 0<m := by
  by_contra hm
  push_neg at hm
  have hb1 : 1≤b := model_discrete _ hb
  have hG1 : 1≤G := model_discrete _ hG
  have hbm := mul_nonpos_of_nonneg_of_nonpos hb.le hm
  have hAG := mul_nonneg (show (0:DiffRing V)≤1+b*W^2 by positivity)
    (show (0:DiffRing V)≤G-1 by linarith)
  have hbV := mul_nonneg (show (0:DiffRing V)≤b-1 by linarith) (sq_nonneg W)
  nlinarith only [hy,hsmall,hbm,hAG,hbV,sq_nonneg (4*W-1)]

/-- Given the model norm and actual divisibility witnesses, construct the
strictly positive literal carrier coordinate m. The negative signed ordinate
is `-ι y`. -/
theorem positive_carrier (I u y b G : V) (hI : 2≤I) (hu : 0<u) (hy : 0<y)
    (hb : 0<b) (hG : 0<G) (hGdiv : b∣G)
    (hydiv : 4*b∣y+1) (hn : I*I*u*u+y*y=1+I*I*y*y) :
    ∃ m : V, 0<m ∧
      -(ι y : DiffRing V)=1+4*(ι b*(ι m-(ι u)^2*ι G)-ι G) := by
  obtain ⟨g,hg⟩ := hGdiv
  obtain ⟨h,hh⟩ := hydiv
  let m : DiffRing V := (ι u)^2*ι G+ι g-ι h
  have eqy : -(ι y : DiffRing V)=1+4*(ι b*(m-(ι u)^2*ι G)-ι G) := by
    have hg' := congrArg (ι : V →+* DiffRing V) hg
    have hh' := congrArg (ι : V →+* DiffRing V) hh
    simp only [map_mul,map_add,map_one,map_ofNat] at hg' hh'
    dsimp [m]
    linear_combination -hh' + 4*hg'
  have hn' := congrArg (ι : V →+* DiffRing V) hn
  simp only [map_mul,map_add,map_one] at hn'
  have hnorm : (ι I : DiffRing V)^2*(ι u)^2-((ι I)^2-1)*(-(ι y))^2=1 := by
    nlinarith only [hn']
  have hS : (2:DiffRing V)≤ι I := two_le_ι hI
  have hsmall := (aux_estimates hS hnorm).2
  have hposU : (0:DiffRing V)<ι u := ι_pos hu
  have hposY : (0:DiffRing V)<ι y := ι_pos hy
  rw [abs_of_neg (neg_neg_of_pos hposY),abs_of_pos hposU] at hsmall
  have hm : 0<m := affine_carrier_pos (ι_pos hb) (ι_pos hG) (by linarith) eqy
  obtain ⟨m',hm'⟩ := nonneg_iff.mp (le_of_lt hm)
  refine ⟨m',?_,?_⟩
  · apply ι_lt_ι.mp
    rw [map_zero ι,←hm']
    exact hm
  · rw [←hm']
    exact eqy
end ModelBPositiveCarrier
#print axioms ModelBPositiveCarrier.positive_carrier
