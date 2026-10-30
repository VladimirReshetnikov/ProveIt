import DiophantineConsistency.AdaptiveDirectOrdinate86SignedV
import DiophantineConsistency.AdaptiveDirectOrdinate86StrongNorm
import DiophantineConsistency.ArithmeticPellHalfIndex

/-! Actual 86-zero signed residue needed for the direct-ordinate witness. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86Residue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptivePellIndices2011
open ArithmeticAdaptiveRankWindow2011 ArithmeticAdaptiveIndexComparison2011
open ArithmeticAdaptiveStrongNorm2011 ArithmeticAdaptiveTransport2011
open ArithmeticAdaptiveFirstDivisibility2011
open ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellClassification
open ArithmeticPellStrongDivisibility ArithmeticPellIndexDivisibility ArithmeticPellHalfIndex
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86AuxNorm
open AdaptiveDirectOrdinate86SignedV AdaptiveDirectOrdinate86StrongNorm
open AdaptiveDirectOrdinate86Comparison AdaptiveDirectOrdinate86Rank AdaptiveDirectOrdinate86Transport
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort xcoord ycoord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private theorem y_six (a : V) :
    ycoord 6 a=32*(a+2)*delta a*delta a+32*(a+2)*delta a+6*(a+2) := by
  have hx1 : xcoord 1 a=a+2 := by simpa using x_succ (0:V) a
  have hy1 : ycoord 1 a=1 := by simpa using y_succ (0:V) a
  conv_lhs =>
    simp only [show (6:V)=5+1 by ring, show (5:V)=4+1 by ring,
      show (4:V)=3+1 by ring, show (3:V)=2+1 by ring,
      show (2:V)=1+1 by ring, y_succ, x_succ, hx1, hy1]
  unfold delta
  ring

private theorem large_of_six (a p : V) (hp : 6≤p) :
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

private theorem same_mul {m x y z w : V} (hm : 0<m)
    (h : x%m=y%m) (h' : z%m=w%m) : (x*z)%m=(y*w)%m := by
  rw [mod_mul hm,mod_mul (a:=y) hm,h,h']

theorem expressionAt_signed_residue86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let c : V := v 9+v 7*(v 9+v 10)
    let I : V := v 4*c*c
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let z : V := magnitude (pairEval (eV (fun j => (p j:ℤ))) v)
    2≤I ∧ 2≤R ∧ 2*R<c ∧ SignMod c z R := by
  have hp := scaled_parameters_positive p v hb hv
  have hq : 0<1+v 0*(p 0:V) := lt_trans (by simp : (0:V)<1) hp.1
  have hw := expressionAt_rank_window86 p v hb hl hh hv hz
  have hcomp := expressionAt_comparison86 p v hb hl hh hv hz
  have hstrong := expressionAt_strong_norm86 p v hz
  let q : V := 1+v 0*(p 0:V)
  let Q : V := (v 6*v 7)*v 7
  let B : V := 2*(Q-1)+1
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := v 6*v 7+v 7
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let f : V := v 3
  let i : V := v 4
  let I : V := i*c*c
  let L : V := (f*f)*v 5*c
  let N : V := (f*f)*R+c
  let z : V := magnitude (L,N)
  obtain ⟨first,main,n,m,hfirst,hmain,hn13,hnm,hm14,hhalf,hroot,horient,hnx,hny,hmx,hmy,hnmod⟩ := hcomp
  have hk : 0<k := add_pos (hv 9) (hv 10)
  have hc : 0<c := add_pos (hv 9) (mul_pos (hv 7) hk)
  have hi : 0 < i := hv 4
  have hf : 0<f := hv 3
  have hm : 0<m := lt_of_lt_of_le (by simp : (0:V)<14) hm14
  obtain ⟨hR24,hupper⟩ := hw
  have hR : 0<R := lt_of_lt_of_le (by simp : (0:V)<24) hR24
  have hRlt : R+1<q^4 := by
    have hp : 0<q^3+q := add_pos (pow_pos hq _) hq
    calc
      R+1<(R+1)+(q^3+q) := lt_add_of_pos_right _ hp
      _=R+q^3+q+1 := by ring
      _≤q^4 := hupper
  have hm6 : (6:V)≤m := le_trans (by
    simpa only [show (6:V)+8=14 by ring] using (show (6:V)≤6+8 by simp)) hm14
  change ycoord m a=c at hmy
  change (2*n)%(q^4)=R+1 at hnmod
  have hbig : (a+2)*delta a*delta a<c := by
    rw [←hmy]
    exact large_of_six a m hm6
  have hD : ((3+4*a)+a*a)=delta a := by unfold delta; ring
  have hI : c*c*i=I := by dsimp [I]; ring
  have hs : I*I+delta a=delta a*(f*f) := by
    change ((c*c)*i)*((c*c)*i)+((3+4*a)+a*a)=((3+4*a)+a*a)*(f*f) at hstrong
    rw [hD,hI] at hstrong
    exact hstrong
  obtain ⟨j,_,hfj,hmj,_,_⟩ := relaxed_auxiliary a c m i f hm hi hf hmy.symm hs hbig
  have hcY : c∣ycoord j a := by
    rw [←hmy]
    exact (y_dvd_iff a m j).mpr hmj
  obtain ⟨w,hw⟩ := hcY
  have hfnorm : f*f=1+c*(delta a*c*w*w) := calc
    f*f=xcoord j a*xcoord j a := by rw [hfj]
    _=1+delta a*ycoord j a*ycoord j a := norm j a
    _=1+c*(delta a*c*w*w) := by rw [hw]; ring
  have hfmod : (f*f)%c=(1:V)%c := by rw [hfnorm,mod_add_mul' _ _ hc]
  have huc : SignMod c z R := by
    change SignMod c (absdiff L N) R
    apply absdiff_residue c L N R hc
    have hd : c∣L := ⟨f*f*v 5,by dsimp [L]; ring⟩
    have hmul : (f*f*R)%c=R%c := by
      have hh := same_mul hc hfmod (show R%c=R%c from rfl)
      simpa only [one_mul] using hh
    calc
      (L+R)%c=R%c := mod_add_remove_left_of_dvd hd hc
      _=(f*f*R)%c := hmul.symm
      _=(f*f*R+c)%c := (mod_add_remove_right hc).symm
      _=N%c := rfl
  have hc2 : 2≤c := by
    have h := add_le_add (pos_iff_one_le.mp (hv 9))
      (one_le_mul (pos_iff_one_le.mp (hv 7)) (pos_iff_one_le.mp hk))
    simpa only [one_add_one_eq_two] using h
  have hI2 : 2≤I := calc
    2≤c := hc2
    _≤c*c := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hc)
    _≤c*c*i := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hi)
    _=I := by dsimp [I]; ring
  have hg := expressionAt_transport_positive86 p v hb hv hz
  have hgap : v 1+v 2<q := tsub_pos_iff_lt.mp hg.2
  have hF : v 1≤q := le_trans (by simp : v 1≤v 1+v 2) (le_of_lt hgap)
  have hrep := signedV_rep p v hF
  have hzmag : magnitude (pairEval (eV (fun j => (p j:ℤ))) v)=z := magnitude_equivalent hrep
  dsimp only
  refine ⟨hI2,?_,hhalf,?_⟩
  · exact le_trans (by norm_num : (2:V)≤24) hR24
  · rw [hzmag]
    exact huc
end DiophantineConsistency.AdaptiveDirectOrdinate86Residue
