import DiophantineConsistency.ArithmeticPellHalfIndex

/-! Pell estimates and modular consequences shared by adaptive residue proofs. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellResidueAux
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellStrongDivisibility
open ArithmeticPellIndexDivisibility ArithmeticPellHalfIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] xcoord ycoord

theorem y_six (a : V) :
    ycoord 6 a=32*(a+2)*delta a*delta a+32*(a+2)*delta a+6*(a+2) := by
  have hx1 : xcoord 1 a=a+2 := by simpa using x_succ (0:V) a
  have hy1 : ycoord 1 a=1 := by simpa using y_succ (0:V) a
  conv_lhs =>
    simp only [show (6:V)=5+1 by ring, show (5:V)=4+1 by ring,
      show (4:V)=3+1 by ring, show (3:V)=2+1 by ring,
      show (2:V)=1+1 by ring, y_succ, x_succ, hx1, hy1]
  unfold delta
  ring

theorem large_of_six (a p : V) (hp : 6≤p) :
    (a+2)*delta a*delta a<ycoord p a := by
  have hx : (a+2)*delta a*delta a≤32*(a+2)*delta a*delta a+32*(a+2)*delta a := by
    calc
      (a+2)*delta a*delta a≤32*((a+2)*delta a*delta a) :=
        le_mul_of_one_le_left (by simp) (by simp)
      _=32*(a+2)*delta a*delta a := by ring
      _≤32*(a+2)*delta a*delta a+32*(a+2)*delta a := by simp
  have hpos : 0<6*(a+2) := mul_pos (by simp) (by simp)
  have h := lt_of_le_of_lt hx (lt_add_of_pos_right _ hpos)
  rw [←y_six] at h
  exact lt_of_lt_of_le h ((ArithmeticPellCongruences.y_strictMono a).monotone hp)

theorem same_mul {m x y z w : V} (hm : 0<m)
    (h : x%m=y%m) (h' : z%m=w%m) : (x*z)%m=(y*w)%m := by
  rw [mod_mul hm,mod_mul (a:=y) hm,h,h']

/-- The relaxed auxiliary equation forces the square of f to be one modulo c. -/
theorem square_mod_one_of_relaxed_auxiliary (a c m i f : V)
    (hm : 0<m) (hi : 0<i) (hf : 0<f) (hc : 0<c)
    (hmy : ycoord m a=c)
    (hs : (i*c*c)*(i*c*c)+delta a=delta a*(f*f))
    (hbig : (a+2)*delta a*delta a<c) : (f*f)%c=(1:V)%c := by
  obtain ⟨j,_,hfj,hmj,_,_⟩ := relaxed_auxiliary a c m i f hm hi hf hmy.symm hs hbig
  have hcY : c∣ycoord j a := by
    rw [←hmy]
    exact (y_dvd_iff a m j).mpr hmj
  obtain ⟨w,hw⟩ := hcY
  have hfnorm : f*f=1+c*(delta a*c*w*w) := calc
    f*f=xcoord j a*xcoord j a := by rw [hfj]
    _=1+delta a*ycoord j a*ycoord j a := norm j a
    _=1+c*(delta a*c*w*w) := by rw [hw]; ring
  rw [hfnorm,mod_add_mul' _ _ hc]

/-- A relaxed auxiliary solution gives the signed residue of the displayed difference. -/
theorem signed_residue_of_relaxed_auxiliary (a c m i f t R : V)
    (hm : 0<m) (hi : 0<i) (hf : 0<f) (hc : 0<c)
    (hmy : ycoord m a=c)
    (hs : (i*c*c)*(i*c*c)+delta a=delta a*(f*f))
    (hbig : (a+2)*delta a*delta a<c) :
    SignMod c (absdiff (f*f*t*c) (f*f*R+c)) R := by
  have hfmod := square_mod_one_of_relaxed_auxiliary a c m i f hm hi hf hc hmy hs hbig
  apply absdiff_residue c (f*f*t*c) (f*f*R+c) R hc
  have hd : c∣f*f*t*c := ⟨f*f*t,by ring⟩
  have hmul : (f*f*R)%c=R%c := by
    have hh := same_mul hc hfmod (show R%c=R%c from rfl)
    simpa only [one_mul] using hh
  calc
    (f*f*t*c+R)%c=R%c := mod_add_remove_left_of_dvd hd hc
    _=(f*f*R)%c := hmul.symm
    _=(f*f*R+c)%c := (mod_add_remove_right hc).symm

end DiophantineConsistency.ArithmeticPellResidueAux
