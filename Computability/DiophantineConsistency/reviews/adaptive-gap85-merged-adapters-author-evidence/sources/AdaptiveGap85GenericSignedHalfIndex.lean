import DiophantineConsistency.AdaptiveGap85SignedResidue

/-! A Pell half-index argument that accommodates either sign of a rank. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85GenericSignedHalfIndex
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellClassification ArithmeticPellHalfIndex ArithmeticPellCongruences
open ArithmeticPellResidueAux AdaptiveGap85SignedResidue
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The signed rank magnitude is the Pell index, under the displayed norm and size hypotheses. -/
theorem signed_half_index_of_facts (a c d f i t rp rn y m : V)
    (hc : 0<c) (hi : 0<i) (hf : 0<f) (hm : 0<m) (hy : 0<y)
    (hmy : ycoord m a=c)
    (hR : 0<absdiff rp rn) (hhalf : 2*absdiff rp rn<c)
    (hmain : d*d=1+delta a*c*c)
    (hstrong : (i*c*c)*(i*c*c)+delta a=delta a*(f*f))
    (hbig : (a+2)*delta a*delta a<c)
    (haux : let z := absdiff (f*f*(t*c+rn)) (f*f*rp+c)
      (i*c*c)*(i*c*c)*z*z+y*y=1+(i*c*c)*(i*c*c)*y*y) :
    m=absdiff rp rn := by
  let R := absdiff rp rn
  let L := f*f*(t*c+rn)
  let N := f*f*rp+c
  let z := absdiff L N
  have hfmod := square_mod_one_of_relaxed_auxiliary a c m i f hm hi hf hc hmy hstrong hbig
  have huc : SignMod c z R := signed_rank_residue c f t rp rn hc hfmod
  have huf : SignMod f z c := by
    apply absdiff_residue f L N c hf
    have hd1 : f∣L := ⟨f*(t*c+rn),by dsimp [L]; ring⟩
    have hd2 : f∣f*f*rp := ⟨f*rp,by ring⟩
    calc
      (L+c)%f=c%f := mod_add_remove_left_of_dvd hd1 hf
      _=(f*f*rp+c)%f := (mod_add_remove_left_of_dvd hd2 hf).symm
      _=N%f := rfl
  have hs : (i*c*c)*(i*c*c)+delta a=delta a*f*f := by simpa only [mul_assoc] using hstrong
  obtain ⟨_,hcr⟩ := half_index a c d f i R y z hc hi hf hR hy hmain hs hbig hhalf haux huf huc
  exact index_unique a m R (hmy.trans hcr)
end DiophantineConsistency.AdaptiveGap85GenericSignedHalfIndex
