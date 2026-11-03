import DiophantineConsistency.ArithmeticPellFirstIndex
import DiophantineConsistency.ArithmeticPellStrongDivisibility
import DiophantineConsistency.ArithmeticPellResidueAux

/-! # First and main Pell indices under the ordinary strong norm

The 14-positive 67/94 equation of package 188 replaces the maintained scaled
strong factor `f² − Delta (i c²)² = 1` by the ordinary relaxed norm
`(i c²)² = Delta (f² − 1)` (`native/PROOF.md` §6). This module re-proves the
maintained index stage for that norm, in every model of `𝗜𝚺₁`:

* `ordinary_half_index` is `ArithmeticPellHalfIndex.literal_half_index` with
  the relaxed norm. The residue `f² ≡ 1 (mod c)`, which the scaled norm gave
  directly, now comes from `relaxed_auxiliary` (`f = χ_a(m)`, `p ∣ m`), the
  ordinate divisibility `ψ_a(p) ∣ ψ_a(m)` and the Pell identity;
* `ordinary_first_main_indices` and `ordinary_first_indices` are verbatim copies of
  `ArithmeticPellFirstIndex.first_main_indices` and `maintained_first_indices`
  with only the strong hypothesis and that one call changed. Their conclusions
  are identical, so every later maintained client applies unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticCarrier94Indices
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellPeriodicity
open ArithmeticPellResidueClasses ArithmeticPellClassification
open ArithmeticPellIndexDivisibility ArithmeticPellHalfIndex
open ArithmeticPellFirstIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem one_le_of_pos {x : V} (h : 0<x) : 1≤x := by
  simpa using lt_iff_succ_le.mp h

private theorem add_le_right {x y : V} (h : x≤y) (z : V) : x+z≤y+z :=
  _root_.add_le_add h (le_refl z)

private theorem add_lt_left {x y : V} (h : x<y) (z : V) : z+x<z+y :=
  add_lt_add_of_le_of_lt (le_refl z) h

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
  exact lt_of_lt_of_le h ((y_strictMono a).monotone hp)

/-- `literal_half_index` for the ordinary relaxed strong norm. -/
theorem ordinary_half_index (a c d f i R y T : V)
    (hc : 0<c) (hi : 0<i) (hf : 0<f) (hR : 0<R) (hy : 0<y)
    (hmain : d*d=1+delta a*c*c)
    (hord : (i*c*c)*(i*c*c)+delta a=delta a*f*f)
    (hbig : (a+2)*delta a*delta a<c) (hhalf : 2*R<c)
    (haux : let I:=i*c*c
      let u:=absdiff (f*f*c*T) (f*f*R+c)
      I*I*u*u+y*y=1+I*I*y*y) :
    d=xcoord R a ∧ c=ycoord R a := by
  let u := absdiff (f*f*c*T) (f*f*R+c)
  obtain ⟨p,_,_,hcp⟩ := solution_index a d c hmain
  have hp : 0<p := pos_iff_ne_zero.mpr (fun hz => (ne_of_gt hc) (by simpa [hz] using hcp.symm))
  have hord' : (i*c*c)*(i*c*c)+delta a=delta a*(f*f) := by simpa only [mul_assoc] using hord
  obtain ⟨m,_,hfm,hpm,_,_⟩ := relaxed_auxiliary a c p i f hp hi hf hcp.symm hord' hbig
  have hf1 : (f*f)%c=(1:V)%c := by
    have hn := norm m a
    obtain ⟨t,ht⟩ : c∣ycoord m a := by rw [← hcp]; exact (ArithmeticPellStrongDivisibility.y_dvd_iff a p m).mpr hpm
    have he : f*f=1+c*(delta a*t*ycoord m a) := by
      rw [hfm,hn]
      nth_rewrite 1 [ht]
      ring
    rw [he,mod_add_mul' _ _ hc]
  have huf : SignMod f u c := by
    apply absdiff_residue _ _ _ _ hf
    rw [show f*f*c*T=f*(f*c*T) by ring,show f*f*R=f*(f*R) by ring]
    simp only [mod_mul_add' _ _ hf]
  have huc : SignMod c u R := by
    apply absdiff_residue _ _ _ _ hc
    calc
      (f*f*c*T+R)%c=(c*(f*f*T)+R)%c := by congr 1; ring
      _=R%c := mod_mul_add' _ _ hc
      _=(f*f*R)%c := by simpa only [one_mul] using (ArithmeticPellResidueAux.same_mul hc hf1 (z:=R) rfl).symm
      _=(f*f*R+c)%c := (mod_add_remove_right hc).symm
  exact half_index a c d f i R y u hc hi hf hR hy hmain hord hbig hhalf haux huf huc

theorem ordinary_first_main_indices (E Y k eta N d f i R y T : V)
    (hE : 0<E) (hY : 2≤Y) (hk : 0<k) (heta : 0<eta) (hN : 0<N)
    (hf : 0<f) (hi : 0<i) (hy : 0<y) (hR8 : 8≤R) (hRE : R+2<E)
    (hfirst : (E*N+k-R)*(E*N+k-R)=1+(E*Y)*(E*Y+1)*k*k)
    (hmain : d*d=1+delta (E+Y)*(k*Y+eta)*(k*Y+eta))
    (hord : (i*(k*Y+eta)*(k*Y+eta))*(i*(k*Y+eta)*(k*Y+eta))+delta (E+Y)=delta (E+Y)*f*f)
    (haux : let c:=k*Y+eta
      let I:=i*c*c
      let u:=absdiff (f*f*c*T) (f*f*R+c)
      I*I*u*u+y*y=1+I*I*y*y) :
    ∃ n h : V, 5≤n ∧ n<R ∧ 2*n=R+1 ∧
      E*N+k-R=xcoord n (2*(E*Y-1)+1) ∧
      k=2*ycoord n (2*(E*Y-1)+1) ∧
      d=xcoord R (E+Y) ∧ k*Y+eta=ycoord R (E+Y) ∧
      (E+Y+2)*delta (E+Y)*delta (E+Y)<k*Y+eta ∧ 2*R<k*Y+eta ∧
      0<h ∧ k=R+1+(4*E*Y)*h := by
  let Q:=E*Y
  let B:=2*(Q-1)+1
  let a:=E+Y
  let c:=k*Y+eta
  let tau:=E*N+k-R
  have hE1 : 1≤E := one_le_of_pos hE
  have hYpos : 0<Y := lt_of_lt_of_le (by simp : (0:V)<2) hY
  have hQ : 0<Q := mul_pos hE hYpos
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (one_le_of_pos hQ)
  have hR : 0<R := lt_of_lt_of_le (by simp : (0:V)<8) hR8
  have hR1 : R+1<E := lt_trans (by
    have h:=lt_add_one (R+1)
    simpa only [add_assoc,one_add_one_eq_two] using h) hRE
  have ht : R<E*N+k := calc
    R<R+2 := lt_add_of_pos_right _ (by simp)
    _<E := hRE
    _≤E*N := le_mul_of_one_le_right (by simp) (one_le_of_pos hN)
    _≤E*N+k := by simp
  have hta : tau+R=E*N+k := tsub_add_cancel_of_le (le_of_lt ht)
  have hn0 : tau*tau=1+ArithmeticPellFirstNorm.discriminant (Q-1)*k*k := by
    have hd : ArithmeticPellFirstNorm.discriminant (Q-1)=Q*(Q+1) := by
      unfold ArithmeticPellFirstNorm.discriminant
      rw [show Q-1+2=(Q-1+1)+1 by ring,hQ1]
    rw [hd]
    exact hfirst
  obtain ⟨n,r,h,_,hnx,hnk,htr,hkr⟩ := ArithmeticPellFirstNorm.solution_residues (Q-1) tau k hn0
  rw [hQ1] at htr hkr
  change xcoord n B=tau at hnx
  change 2*ycoord n B=k at hnk
  have hrem : k%E=R+1 := by
    have he : (R+1+E*(2*Y*r))%E=(E*N+k)%E := by
      congr 1
      calc
        R+1+E*(2*Y*r)=tau+R := by rw [htr]; dsimp [Q]; ring
        _=E*N+k := hta
    rw [mod_add_mul' _ _ hE,mod_mul_add' _ _ hE,mod_eq_self_of_lt hR1] at he
    exact he.symm
  have hnrem : (2*n)%E=R+1 := by
    have hh : k=2*n+E*(4*Y*h) := by rw [hkr]; dsimp [Q]; ring
    rw [hh,mod_add_mul' _ _ hE] at hrem
    exact hrem
  have hRk : R+1≤k := by rw [←hrem]; exact mod_le _ _
  have hRn : R+1≤2*n := by rw [←hnrem]; exact mod_le _ _
  have hn5 : 5≤n := by
    have h8 : (2:V)*4 < 2*n := by
      rw [show (2:V)*4=8 by ring]
      exact lt_of_le_of_lt hR8 (lt_of_lt_of_le (lt_add_one R) hRn)
    have h4 : (4:V)<n := lt_of_mul_lt_mul_left h8 (by simp)
    simpa only [show (4:V)+1=5 by ring] using lt_iff_succ_le.mp h4
  have hc : 0<c := lt_of_lt_of_le (mul_pos hk hYpos) (by simp : k*Y≤k*Y+eta)
  have hkc : k<c := calc
    k≤k*Y := le_mul_of_one_le_right (by simp) (le_trans (by simp : (1:V)≤2) hY)
    _<k*Y+eta := lt_add_of_pos_right _ heta
  have hhalf : 2*R<c := calc
    2*R<2*(R+1) := mul_lt_mul_of_pos_left (lt_add_one R) (by simp)
    _≤2*k := mul_le_mul_of_nonneg_left hRk (by simp)
    _≤k*Y := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hY (Arithmetic.zero_le k)
    _<k*Y+eta := lt_add_of_pos_right _ heta
  have hB : B+2=2*Q+1 := by
    dsimp [B]
    calc
      2*(Q-1)+1+2=2*(Q-1+1)+1 := by ring
      _=2*Q+1 := by rw [hQ1]
  have hab : a≤B := by
    have hEsub : E-1+1=E := tsub_add_cancel_of_le hE1
    have hYsub : Y-2+2=Y := tsub_add_cancel_of_le hY
    have he : a+2+(E-1)*(2*(Y-2)+3)+(Y-2)=B+2 := by
      rw [hB]
      calc
        a+2+(E-1)*(2*(Y-2)+3)+(Y-2)=
          (E-1+1)+(Y-2+2)+2+(E-1)*(2*(Y-2)+3)+(Y-2) := by rw [hEsub,hYsub]
        _=2*((E-1+1)*(Y-2+2))+1 := by ring
        _=2*Q+1 := by rw [hEsub,hYsub]
    have he' : a+2≤B+2 := by rw [←he]; simp
    exact (add_le_add_iff_right (2:V)).mp he'
  obtain ⟨p,_,_hpd,hpc⟩ := solution_index a d c hmain
  have hnp : n<p := by
    by_contra hn
    have hp : p≤n := le_of_not_gt hn
    have he : c≤k := calc
      c=ycoord p a := hpc.symm
      _≤ycoord n a := (y_strictMono a).monotone hp
      _≤ycoord n B := (base_mono a B hab n).2
      _≤2*ycoord n B := le_mul_of_one_le_left (by simp) (by simp)
      _=k := hnk
    exact (not_le_of_gt hkc) he
  have hp6 : 6≤p := by
    have h:=le_trans (add_le_right hn5 1) (lt_iff_succ_le.mp hnp)
    simpa only [show (5:V)+1=6 by ring] using h
  have hbig : (a+2)*delta a*delta a<c := by rw [←hpc]; exact large_of_six a p hp6
  obtain ⟨hdr,hcr⟩ := ordinary_half_index a c d f i R y T hc hi hf hR hy hmain hord hbig hhalf haux
  have hpR : p=R := index_unique a p R (hpc.trans hcr)
  have hnR : n<R := by rwa [hpR] at hnp
  have hsmall : 2*n<E+(R+1) := calc
    2*n<2*R := mul_lt_mul_of_pos_left hnR (by simp)
    _<E+(R+1) := by
      have hle : R≤R+1 := by simp
      have hlt : R<E := lt_trans (lt_add_one R) hR1
      simpa only [two_mul,add_assoc] using add_lt_add_of_lt_of_le hlt hle
  have hdiv : (2*n)/E=0 := by
    by_contra hz
    have hd : 1≤(2*n)/E := one_le_of_pos (pos_iff_ne_zero.mpr hz)
    have he : E+(R+1)≤2*n := calc
      E+(R+1)≤E*((2*n)/E)+(R+1) := add_le_right (le_mul_of_one_le_right (by simp) hd) _
      _=2*n := by rw [←hnrem]; exact div_add_mod _ _
    exact (not_le_of_gt hsmall) he
  have hnR1 : 2*n=R+1 := by
    simpa only [hdiv,mul_zero,zero_add,hnrem] using (div_add_mod (2*n) E).symm
  have hE_Q : E≤Q := le_mul_of_one_le_right (by simp) (le_trans (by simp : (1:V)≤2) hY)
  have hE_k : E<k := calc
    E≤Q := hE_Q
    _<2*Q+1 := lt_of_le_of_lt (le_mul_of_one_le_left (by simp) (by simp : (1:V)≤2)) (lt_add_one _)
    _≤4*(B+2) := by
      rw [hB]
      exact le_mul_of_one_le_left (by simp) (by simp)
    _=2*ycoord 2 B := by
      rw [y_two]; ring
    _≤2*ycoord n B := mul_le_mul_of_nonneg_left ((y_strictMono B).monotone
      (le_trans (by simpa only [show (2:V)+3=5 by ring] using (show (2:V)≤2+3 by simp)) hn5)) (by simp)
    _=k := hnk
  have hh : 0<h := by
    by_contra hn
    have hz : h=0 := le_antisymm (le_of_not_gt hn) (by simp)
    rw [hz,mul_zero,add_zero,hnR1] at hkr
    exact (not_lt_of_ge (le_of_lt hE_k)) (by rwa [hkr])
  refine ⟨n,h,hn5,hnR,hnR1,hnx.symm,hnk.symm,hdr,hcr,hbig,hhalf,hh,?_⟩
  rw [hkr,hnR1]
  dsimp [Q]
  ring

theorem ordinary_first_indices (beta K MC MF J F alpha z f i T s w N eta zeta y gamma : V)
    (hbeta : 0<beta) (hMC : MC<beta) (hMF : MF<2*beta)
    (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha) (hz : 0<z)
    (hf : 0<f) (hi : 0<i) (_hT : 0<T) (hs : 0<s) (hw : 0<w)
    (hN : 0<N) (heta : 0<eta) (hzeta : 0<zeta) (hy : 0<y) (_hgamma : 0<gamma) :
    let q:=beta*J+1
    let X:=w*q
    let Y:=s*q^3
    let E:=X*Y
    let k:=eta+zeta
    let c:=k*Y+eta
    let a:=E+Y
    let d:=X+a*c+gamma*(4*a+3)
    let R:=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
    let tau:=E*N+k-R
    let I:=i*c*c
    let u:=absdiff (f*f*c*T) (f*f*R+c)
    (K+w)*q+q=(K+w)*(F+alpha)+F+z*(q-1)+1 →
    tau*tau=1+(E*Y)*(E*Y+1)*k*k →
    d*d=1+delta a*c*c →
    (i*c*c)*(i*c*c)+delta a=delta a*f*f →
    I*I*u*u+y*y=1+I*I*y*y →
    ∃ n h : V, 5≤n ∧ n<R ∧ 2*n=R+1 ∧ tau=xcoord n (2*(E*Y-1)+1) ∧
      k=2*ycoord n (2*(E*Y-1)+1) ∧ d=xcoord R a ∧ c=ycoord R a ∧
      (a+2)*delta a*delta a<c ∧ 2*R<c ∧ 0<h ∧ k=R+1+(4*E*Y)*h := by
  dsimp only
  intro htransport hfirst hmain hstrict haux
  let q:=beta*J+1
  have hq2 : 2≤q := by
    have he:=add_le_right (one_le_mul (one_le_of_pos hbeta) (one_le_of_pos hJ)) 1
    simpa only [one_add_one_eq_two] using he
  have hq1 : 1≤q := le_trans (by simp : (1:V)≤2) hq2
  have hq3 : 2≤q^3 := calc
    2≤q := hq2
    _≤q*q := le_mul_of_one_le_right (by simp) hq1
    _≤q*q*q := le_mul_of_one_le_right (by simp) hq1
    _=q^3 := by ring
  have hY : 2≤s*q^3 := le_trans hq3 (le_mul_of_one_le_left (by simp) (one_le_of_pos hs))
  have hE : 0<(w*q)*(s*q^3) := mul_pos (mul_pos hw (lt_of_lt_of_le (by simp : (0:V)<2) hq2))
    (lt_of_lt_of_le (by simp : (0:V)<2) hY)
  have hk : 0<eta+zeta := add_pos heta hzeta
  obtain ⟨_,hR24,hRE⟩ := scalar_window q beta K MC MF J F alpha z w s
    hbeta hJ hF halpha hz hw hs hMC hMF rfl htransport
  have hR8 : (8:V)≤((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J :=
    le_trans (by simpa only [show (8:V)+16=24 by ring] using (show (8:V)≤8+16 by simp)) hR24
  have heq : w*s*q^4=(w*q)*(s*q^3) := by ring
  rw [heq] at hRE
  exact ordinary_first_main_indices ((w*q)*(s*q^3)) (s*q^3) (eta+zeta) eta N
    (w*q+((w*q)*(s*q^3)+s*q^3)*((eta+zeta)*(s*q^3)+eta)+gamma*(4*((w*q)*(s*q^3)+s*q^3)+3))
    f i (((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J) y T
    hE hY hk heta hN hf hi hy hR8 hRE hfirst hmain hstrict haux

end DiophantineConsistency.ArithmeticCarrier94Indices
