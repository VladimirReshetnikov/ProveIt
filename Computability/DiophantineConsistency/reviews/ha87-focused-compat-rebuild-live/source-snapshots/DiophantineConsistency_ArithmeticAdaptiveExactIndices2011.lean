import DiophantineConsistency.ArithmeticAdaptiveAuxNorm2011
import DiophantineConsistency.ArithmeticAdaptiveIndexComparison2011
import DiophantineConsistency.ArithmeticPellHalfIndex

/-! Exact adaptive Pell indices from the actual four carrier factors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveExactIndices2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptivePellIndices2011
open ArithmeticAdaptiveRankWindow2011 ArithmeticAdaptiveIndexComparison2011
open ArithmeticAdaptiveStrongNorm2011 ArithmeticAdaptiveAuxNorm2011
open ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellClassification
open ArithmeticPellStrongDivisibility ArithmeticPellIndexDivisibility ArithmeticPellHalfIndex
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

def ExactIndices (p : Fin 4 → ℕ) (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let M : V := (q*(q*q))*(v 0*(p 0:V))
  let U : V := v 7*(q*q)
  let Q : V := (v 6*v 7)*v 7
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := v 6*v 7+v 7
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  ∃ first main n m t : V, 0<first ∧ 0<main ∧ 13≤n ∧ n<m ∧ m=R ∧ 2*n=R+1 ∧
    k=R+1+4*Q*t ∧
    magnitude (pairEval (rootTerm (factors (fun j => (p j:ℤ))).1) v)=M*first ∧
    Equivalent (pairEval (rootTerm (factors (fun j => (p j:ℤ))).2.1) v) (natural (U*main)) ∧
    xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
    xcoord m a=main ∧ ycoord m a=c

theorem exact_indices_of_facts (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hq : 0<1+v 0*(p 0:V)) (hv : ∀j,0<v j)
    (hw : RankWindow p v) (hcomp : Comparison p v)
    (hstrong : StrongNorm v) (haux : AuxNorm p v) : ExactIndices p v := by
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
  let y : V := magnitude (L+v 11,N)
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
  have ha : I*I*z*z+y*y=1+I*I*y*y := by
    change ((c*c)*i)*((c*c)*i)*z*z+y*y=1+((c*c)*i)*((c*c)*i)*y*y at haux
    rw [hI] at haux
    exact haux
  have hmainnorm : main*main=1+delta a*c*c := calc
    main*main=xcoord m a*xcoord m a := by rw [hmx]
    _=1+delta a*ycoord m a*ycoord m a := norm m a
    _=1+delta a*c*c := by rw [hmy]
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
  have huf : SignMod f z c := by
    change SignMod f (absdiff L N) c
    apply absdiff_residue f L N c hf
    have hd1 : f∣L := ⟨f*v 5*c,by dsimp [L]; ring⟩
    have hd2 : f∣f*f*R := ⟨f*R,by ring⟩
    calc
      (L+c)%f=c%f := mod_add_remove_left_of_dvd hd1 hf
      _=(f*f*R+c)%f := (mod_add_remove_left_of_dvd hd2 hf).symm
      _=N%f := rfl
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
  have hy : 0<y := pos_iff_ne_zero.mpr (by
    intro hy0
    have hp : I*I*z*z=1 := by simpa only [hy0,mul_zero,zero_mul,add_zero] using ha
    have hd : I*I∣(1:V) := ⟨z*z,by simpa only [mul_assoc] using hp.symm⟩
    have hle : I*I≤1 := Arithmetic.le_of_dvd (by simp) hd
    have hIle : I≤I*I := le_mul_of_one_le_right (by simp) (le_trans (by simp : (1:V)≤2) hI2)
    exact (not_le_of_gt (lt_of_lt_of_le (by simp : (1:V)<2) hI2)) (le_trans hIle hle))
  have hs' : (i*c*c)*(i*c*c)+delta a=delta a*f*f := by
    simpa only [I,mul_assoc] using hs
  have ha' : (i*c*c)*(i*c*c)*z*z+y*y=1+(i*c*c)*(i*c*c)*y*y := by
    simpa only [I] using ha
  obtain ⟨_,hcr⟩ := half_index a c main f i R y z hc hi hf hR hy hmainnorm hs' hbig hhalf ha' huf huc
  have hmR : m=R := index_unique a m R (hmy.trans hcr)
  have hnR : n<R := by rwa [←hmR]
  have hsmall : 2*n<q^4+(R+1) := calc
    2*n<2*R := mul_lt_mul_of_pos_left hnR (by simp)
    _<q^4+(R+1) := by
      have hle : R≤R+1 := by simp
      have hlt : R<q^4 := lt_trans (lt_add_one R) hRlt
      simpa only [two_mul,add_assoc] using add_lt_add_of_lt_of_le hlt hle
  have hdiv : (2*n)/(q^4)=0 := by
    by_contra hz
    have hd : 1≤(2*n)/(q^4) := pos_iff_one_le.mp (pos_iff_ne_zero.mpr hz)
    have he : q^4+(R+1)≤2*n := calc
      q^4+(R+1)≤q^4*((2*n)/(q^4))+(R+1) :=
        _root_.add_le_add (le_mul_of_one_le_right (by simp) hd) (le_refl _)
      _=2*n := by rw [←hnmod]; exact div_add_mod _ _
    exact (not_le_of_gt hsmall) he
  have hnR1 : 2*n=R+1 := by
    have he := (div_add_mod (2*n) (q^4)).symm
    rw [hdiv,hnmod] at he
    simpa only [mul_zero,zero_add] using he
  have hQ : 0<Q := mul_pos (mul_pos (hv 6) (hv 7)) (hv 7)
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp hQ)
  have hB : B+1=2*Q := by
    dsimp [B]
    calc
      2*(Q-1)+1+1=2*(Q-1+1) := by ring
      _=2*Q := by rw [hQ1]
  change 2*ycoord n B=k at hny
  obtain ⟨t,ht⟩ := first_transport n B Q R k hB hny.symm hnR1.symm
  exact ⟨first,main,n,m,t,hfirst,hmain,hn13,hnm,hmR,hnR1,ht,hroot,horient,hnx,hny,hmx,hmy⟩

theorem expressionAt_exact_indices (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) : ExactIndices p v := by
  have hp := scaled_parameters_positive p v hb hv
  exact exact_indices_of_facts p v (lt_trans (by simp : (0:V)<1) hp.1) hv
    (expressionAt_rank_window p v hb hl hh hv hz) (expressionAt_comparison p v hb hl hh hv hz)
    (expressionAt_strong_norm p v hz) (expressionAt_aux_norm p v hb hv hz)

theorem current_exact_indices (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : ExactIndices currentPorts v := by
  have hp := current_parameters_positive v hv
  have hq : 0<1+v 0*(currentPorts 0:V) := by
    simpa only [currentPorts,Matrix.cons_val_zero] using lt_trans (by simp : (0:V)<1) hp.1
  exact exact_indices_of_facts currentPorts v hq hv (current_rank_window v hv hz)
    (current_comparison v hv hz) (current_strong_norm v hz) (current_aux_norm v hv hz)

theorem current_natural_exact_indices (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    ExactIndices currentPorts (fun j => v j+1) :=
  current_exact_indices _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptiveExactIndices2011
