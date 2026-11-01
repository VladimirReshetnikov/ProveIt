import DiophantineConsistency.ArithmeticPellFirstIndex

/-! Internal power recovery from the maintained literal carrier equations.
The first/main indices are derived, and the doubled first ordinate is retained.
Constant-sixteen recurrence comparison uses only the represented base-two
exponential. Concrete port certification and cofinal witnesses are separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellPowerRecovery
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellFirstIndex ArithmeticPellHalfIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The Pell abscissa exceeds (b+1) times the ordinate. -/
theorem x_gt (b t : V) : (b+1)*ycoord t b<xcoord t b := by
  apply lt_of_mul_self_lt_mul_self₀ (by simp)
  have he : xcoord t b*xcoord t b=
      ((b+1)*ycoord t b)*((b+1)*ycoord t b)+(1+2*(b+1)*ycoord t b*ycoord t b) := by
    rw [norm]
    unfold delta
    ring
  rw [he]
  exact lt_add_of_pos_right _ (by simp)

/-- The strict lower step includes time zero. -/
theorem y_lower (b t : V) : (2*b+3)*ycoord t b<ycoord (t+1) b := by
  have hx := x_gt b t
  rw [y_succ]
  calc
    (2*b+3)*ycoord t b=(b+1)*ycoord t b+(b+2)*ycoord t b := by ring
    _<xcoord t b+(b+2)*ycoord t b := add_lt_add_of_lt_of_le hx (le_refl _)

/-- Positive time is necessary for this upper step. -/
theorem y_upper (b t : V) (ht : 0<t) : ycoord (t+1) b≤2*(b+2)*ycoord t b := by
  have hy : 1≤ycoord t b := le_trans (pos_iff_one_le.mp ht) (time_le_y t b)
  have hx : xcoord t b≤(b+2)*ycoord t b := by
    apply nonneg_le_nonneg_of_sq_le_sq (by simp)
    calc
      xcoord t b*xcoord t b=1+delta b*ycoord t b*ycoord t b := norm t b
      _≤ycoord t b*ycoord t b+delta b*ycoord t b*ycoord t b :=
        add_le_add_left (one_le_mul hy hy) _
      _=((b+2)*ycoord t b)*((b+2)*ycoord t b) := by unfold delta; ring
  rw [y_succ]
  calc
    xcoord t b+(b+2)*ycoord t b≤(b+2)*ycoord t b+(b+2)*ycoord t b := add_le_add_left hx _
    _=2*(b+2)*ycoord t b := by ring

private theorem exp_four_succ (r : V) : Exp.exp (4*(r+1))=16*Exp.exp (4*r) := by
  rw [show 4*(r+1)=(((4*r+1)+1)+1)+1 by ring,exp_succ,exp_succ,exp_succ,exp_succ]
  ring

private theorem paired_step (a b r : V)
    (hsep : 16*(2*(b+2))<(2*a+3)*(2*a+3))
    (ih : Exp.exp (4*r)*ycoord (r+1) b≤ycoord (2*r+1) a) :
    Exp.exp (4*(r+1))*ycoord (r+1+1) b<ycoord (2*(r+1)+1) a := by
  have hpos : 0<ycoord (2*r+1) a :=
    lt_of_lt_of_le (by simp : (0:V)<2*r+1) (time_le_y _ _)
  have htwo : (2*a+3)*(2*a+3)*ycoord (2*r+1) a<ycoord (2*(r+1)+1) a := calc
    (2*a+3)*(2*a+3)*ycoord (2*r+1) a=
        (2*a+3)*((2*a+3)*ycoord (2*r+1) a) := by ring
    _<(2*a+3)*ycoord (2*r+1+1) a :=
      mul_lt_mul_of_pos_left (y_lower a (2*r+1)) (by simp)
    _<ycoord (2*r+1+1+1) a := y_lower a (2*r+1+1)
    _=ycoord (2*(r+1)+1) a := by congr 1; ring
  calc
    Exp.exp (4*(r+1))*ycoord (r+1+1) b=
        (16*Exp.exp (4*r))*ycoord (r+1+1) b := by rw [exp_four_succ]
    _≤(16*Exp.exp (4*r))*(2*(b+2)*ycoord (r+1) b) :=
      mul_le_mul_of_nonneg_left (y_upper b (r+1) (by simp)) (by simp)
    _=(16*(2*(b+2)))*(Exp.exp (4*r)*ycoord (r+1) b) := by ring
    _≤(16*(2*(b+2)))*ycoord (2*r+1) a := mul_le_mul_of_nonneg_left ih (by simp)
    _<(2*a+3)*(2*a+3)*ycoord (2*r+1) a := mul_lt_mul_of_pos_right hsep hpos
    _<ycoord (2*(r+1)+1) a := htwo

/-- Explicit fixed syntax prevents automatic graph search from unfolding the
choice-defined exponential while assembling the induction predicate. -/
private def comparisonDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r a b. ∃ e u v, !expDef e (4*r) ∧ !yDef u (r+1) b ∧
    !yDef v (2*r+1) a ∧ e*u≤v”

private instance comparison_defined : 𝚺₁-Relation₃[V]
    (fun r a b : V => Exp.exp (4*r)*ycoord (r+1) b≤ycoord (2*r+1) a)
    via comparisonDef := .mk fun e => by
  simp [comparisonDef,Semiformula.eval_substs]

private instance comparison_definable : 𝚺₁-Relation₃[V]
    (fun r a b : V => Exp.exp (4*r)*ycoord (r+1) b≤ycoord (2*r+1) a) :=
  comparison_defined.to_definable

/-- A represented induction with an equality base case, at arbitrary internal r. -/
theorem paired_comparison (a b : V) (hsep : 16*(2*(b+2))<(2*a+3)*(2*a+3)) (r : V) :
    Exp.exp (4*r)*ycoord (r+1) b≤ycoord (2*r+1) a := by
  induction r using ISigma1.sigma1_succ_induction
  · exact HierarchySymbol.Definable.comp₃
      (P := fun r a b : V => Exp.exp (4*r)*ycoord (r+1) b≤ycoord (2*r+1) a)
      (f₁ := fun v => v 0) (f₂ := fun _ => a) (f₃ := fun _ => b)
      (by simp) (by simp) (by simp)
  case zero =>
    have hy (b : V) : ycoord 1 b=1 := by simpa using y_succ (0:V) b
    simp [hy]
  case succ r ih => exact le_of_lt (paired_step a b r hsep ih)

theorem paired_comparison_strict (a b : V) (hsep : 16*(2*(b+2))<(2*a+3)*(2*a+3))
    (r : V) (hr : 0<r) : Exp.exp (4*r)*ycoord (r+1) b<ycoord (2*r+1) a := by
  rcases zero_or_succ r with rfl|⟨r,rfl⟩
  · simp at hr
  · exact paired_step a b r hsep (paired_comparison a b hsep r)

/-- The factor is16 times the full upper-step multiplier2P. -/
theorem coefficient_gap (X Y : V) (hX : 16≤X) (hY : 1≤Y) :
    16*(2*(2*X*Y*Y+1))<(2*(Y*(X+1))+3)*(2*(Y*(X+1))+3) := by
  have hsq : 16*X≤(X+1)*(X+1) := calc
    16*X≤X*X := mul_le_mul_of_nonneg_right hX (by simp)
    _≤(X+1)*(X+1) := mul_le_mul (by simp) (by simp) (by simp) (by simp)
  have h17 : (17:V)≤Y*(X+1) := calc
    17=1*(16+1) := by ring
    _≤Y*(X+1) := mul_le_mul hY (add_le_add_left hX 1) (by simp) (by simp)
  have h204 : (204:V)≤12*Y*(X+1) := calc
    204=12*17 := by ring
    _≤12*(Y*(X+1)) := mul_le_mul_of_nonneg_left h17 (by simp)
    _=12*Y*(X+1) := by ring
  have hlarge : 64*X*Y*Y+204+9≤(2*(Y*(X+1))+3)*(2*(Y*(X+1))+3) := calc
    64*X*Y*Y+204+9=4*Y*Y*(16*X)+204+9 := by ring
    _≤4*Y*Y*((X+1)*(X+1))+12*Y*(X+1)+9 :=
      add_le_add_left (add_le_add (mul_le_mul_of_nonneg_left hsq (by simp)) h204) 9
    _=(2*(Y*(X+1))+3)*(2*(Y*(X+1))+3) := by ring
  apply lt_of_lt_of_le _ hlarge
  have hnum : (32:V)<204+9 := by norm_num
  have h := add_lt_add_of_le_of_lt (le_refl (64*X*Y*Y)) hnum
  simpa only [show 16*(2*(2*X*Y*Y+1))=64*X*Y*Y+32 by ring,add_assoc] using h

/-- The classified-coordinate helper retains the doubled first ordinate. -/
theorem power_bound (X Y r k c eta zeta : V) (hX : 16≤X) (hY : 1≤Y) (hr : 2≤r)
    (hck : c=k*Y+eta) (hkez : k=eta+zeta) (hz : 0<zeta)
    (hc : c=ycoord (2*r+1) (Y*(X+1)))
    (hk : k=2*ycoord (r+1) (2*(X*Y*Y-1)+1)) : Exp.exp (2*r+1)<Y := by
  let B:=2*(X*Y*Y-1)+1
  have hX1 : 1≤X := le_trans (by simp : (1:V)≤16) hX
  have hQ : 1≤X*Y*Y := one_le_mul (one_le_mul hX1 hY) hY
  have hQe : X*Y*Y-1+1=X*Y*Y := tsub_add_cancel_of_le hQ
  have hB : B+2=2*X*Y*Y+1 := calc
    B+2=2*(X*Y*Y-1+1)+1 := by dsimp [B]; ring
    _=2*X*Y*Y+1 := by rw [hQe]; ring
  have hsep : 16*(2*(B+2))<(2*(Y*(X+1))+3)*(2*(Y*(X+1))+3) := by
    rw [hB]; exact coefficient_gap X Y hX hY
  have hrp : 0<r := lt_of_lt_of_le (by simp : (0:V)<2) hr
  have hlow := paired_comparison_strict (Y*(X+1)) B hsep r hrp
  have hkpos : 0<k := by rw [hkez]; exact add_pos_of_nonneg_of_pos (by simp) hz
  have hinterval : c<k*(Y+1) := by
    rw [hck]
    have he : eta<k := by rw [hkez]; exact lt_add_of_pos_right eta hz
    have h := add_lt_add_of_le_of_lt (le_refl (k*Y)) he
    simpa only [mul_add,mul_one] using h
  have he : Exp.exp (4*r)*k<k*(2*(Y+1)) := calc
    Exp.exp (4*r)*k=2*(Exp.exp (4*r)*ycoord (r+1) B) := by rw [hk]; dsimp [B]; ring
    _<2*ycoord (2*r+1) (Y*(X+1)) := mul_lt_mul_of_pos_left hlow (by simp)
    _=2*c := by rw [hc]
    _<2*(k*(Y+1)) := mul_lt_mul_of_pos_left hinterval (by simp)
    _=k*(2*(Y+1)) := by ring
  have hupper : Exp.exp (4*r)<2*(Y+1) :=
    (mul_lt_mul_iff_of_pos_left hkpos).mp (by simpa only [mul_comm] using he)
  have hindex : 2*r+3≤4*r := by
    have h4 : (4:V)≤2*r := by simpa only [show (2:V)*2=4 by ring] using
      mul_le_mul_of_nonneg_left hr (by simp : (0:V)≤2)
    have h3 : (3:V)≤2*r := le_trans (by norm_num) h4
    have h := add_le_add (le_refl (2*r)) h3
    simpa only [show 2*r+2*r=4*r by ring] using h
  have hfloor : 2*Exp.exp (2*r+1)+2≤Exp.exp (4*r) := calc
    2*Exp.exp (2*r+1)+2≤2*Exp.exp (2*r+1)+2*Exp.exp (2*r+1) :=
      add_le_add (le_refl _) (le_mul_of_one_le_right (by simp) (one_le_exp _))
    _=Exp.exp (2*r+3) := by
      rw [show 2*r+3=(2*r+1+1)+1 by ring,exp_succ (2*r+1+1),exp_succ (2*r+1)]; ring
    _≤Exp.exp (4*r) := exp_monotone_le.mpr hindex
  have hfinal : 2*Exp.exp (2*r+1)+2<2*Y+2 := by
    simpa only [mul_add,mul_one] using lt_of_le_of_lt hfloor hupper
  exact (mul_lt_mul_iff_of_pos_left (by simp : (0:V)<2)).mp
    ((add_lt_add_iff_right (2:V)).mp hfinal)

/-- A nonnegative quotient at every internal time; no signed modular oracle. -/
theorem projection_quotient (a t : V) :
    ∃ z : V, xcoord t a=Exp.exp t+a*ycoord t a+(4*a+3)*z := by
  induction t using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0,by simp⟩
  case succ t ih =>
    obtain ⟨z,hz⟩ := ih
    refine ⟨ycoord t a+2*z,?_⟩
    rw [x_succ,y_succ,exp_succ,hz]
    unfold delta
    ring

/-- A small-range exact recovery from the literal main root formula. -/
theorem power_of_coordinates (X Y R c d gamma : V) (hY : Exp.exp R<Y)
    (hc : c=ycoord R (Y*(X+1))) (hd : d=xcoord R (Y*(X+1)))
    (hdef : d=X+Y*(X+1)*c+gamma*(4*(Y*(X+1))+3)) : X=Exp.exp R := by
  let a:=Y*(X+1)
  let H:=4*a+3
  have hY1 : 1≤Y := le_trans (one_le_exp R) (le_of_lt hY)
  have hXa : X<a := lt_of_lt_of_le (lt_add_one X)
    (le_mul_of_one_le_left (by simp) hY1)
  have hYa : Y≤a := le_mul_of_one_le_right (by simp) (by simp)
  have haH : a<H := lt_of_le_of_lt (le_mul_of_one_le_left (by simp) (by simp : (1:V)≤4))
    (lt_add_of_pos_right _ (by simp))
  have hH : 0<H := by dsimp [H]; simp
  obtain ⟨z,hz⟩ := projection_quotient a R
  have he : X+gamma*H=Exp.exp R+H*z := by
    apply add_right_cancel (b:=a*c)
    calc
      X+gamma*H+a*c=d := by rw [hdef]; dsimp [a,H]; ring
      _=xcoord R a := hd
      _=Exp.exp R+a*ycoord R a+H*z := hz
      _=Exp.exp R+H*z+a*c := by rw [hc]; dsimp [a]; ring
  have hm := congrArg (fun v : V => v%H) he
  rw [mod_add_mul X gamma hH,mod_add_mul' (Exp.exp R) z hH] at hm
  rwa [mod_eq_self_of_lt (lt_trans hXa haH),
    mod_eq_self_of_lt (lt_trans hY (lt_of_le_of_lt hYa haH))] at hm

/-- The actual maintained inputs derive the power and its represented graph.
MF is already the fourth source port, with its single beta shift. -/
theorem maintained_power (beta K MC MF J F alpha z f i T s w N eta zeta y gamma : V)
    (hbeta : 15≤beta) (hMC : MC<beta) (hMF : MF<2*beta)
    (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha) (hz : 0<z)
    (hf : 0<f) (hi : 0<i) (hT : 0<T) (hs : 0<s) (hw : 0<w)
    (hN : 0<N) (heta : 0<eta) (hzeta : 0<zeta) (hy : 0<y) (hgamma : 0<gamma) :
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
    let I:=delta a*i*c*c
    let u:=absdiff (f*f*c*T) (f*f*R+c)
    (K+w)*q+q=(K+w)*(F+alpha)+F+z*(q-1)+1 →
    tau*tau=1+(E*Y)*(E*Y+1)*k*k →
    d*d=1+delta a*c*c →
    f*f=1+delta a*(i*c*c)*(i*c*c) →
    I*I*u*u+y*y=1+I*I*y*y →
    X=Exp.exp R ∧ Exponential R X ∧ Exp.exp R<Y := by
  dsimp only
  intro ht hn hm hf' hu
  let q:=beta*J+1
  let X:=w*q
  let Y:=s*q^3
  let R:=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
  let k:=eta+zeta
  let c:=k*Y+eta
  let a:=X*Y+Y
  let d:=X+a*c+gamma*(4*a+3)
  have hb : 0<beta := lt_of_lt_of_le (by simp : (0:V)<15) hbeta
  obtain ⟨n,h,hn5,_,hnR,_,hk,hd,hc,_,_,_,_⟩ :=
    maintained_first_indices beta K MC MF J F alpha z f i T s w N eta zeta y gamma
      hb hMC hMF hJ hF halpha hz hf hi hT hs hw hN heta hzeta hy hgamma ht hn hm hf' hu
  change k=2*ycoord n (2*(X*Y*Y-1)+1) at hk
  change d=xcoord R a at hd
  change c=ycoord R a at hc
  change 2*n=R+1 at hnR
  have hq16 : (16:V)≤q := calc
    16=15+1 := by ring
    _≤beta+1 := add_le_add_left hbeta 1
    _≤beta*J+1 := add_le_add_left (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hJ)) 1
  have hX : (16:V)≤X := le_trans hq16 (le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp hw))
  have hq1 : 1≤q := le_trans (by simp : (1:V)≤16) hq16
  have hY : 1≤Y := by
    dsimp [Y]
    have hq3 : 1≤q^3 := by simpa only [show q^3=q*q*q by ring] using one_le_mul (one_le_mul hq1 hq1) hq1
    exact one_le_mul (pos_iff_one_le.mp hs) hq3
  let r:=n-1
  have hn1 : 1≤n := le_trans (by simp : (1:V)≤5) hn5
  have hrn : r+1=n := tsub_add_cancel_of_le hn1
  have hr : (2:V)≤r := by
    apply (add_le_add_iff_right (1:V)).mp
    rw [hrn,show (2:V)+1=3 by ring]
    exact le_trans (by simpa only [show (3:V)+2=5 by ring] using (show (3:V)≤3+2 by simp)) hn5
  have hR : R=2*r+1 := by
    apply add_right_cancel (b:=(1:V))
    calc
      R+1=2*n := hnR.symm
      _=(2*r+1)+1 := by rw [←hrn]; ring
  have ha : a=Y*(X+1) := by dsimp [a]; ring
  have hbound : Exp.exp R<Y := by
    rw [hR]
    apply power_bound X Y r k c eta zeta hX hY hr rfl rfl hzeta
    · simpa only [ha,hR] using hc
    · simpa only [hrn] using hk
  have hp : X=Exp.exp R := power_of_coordinates X Y R c d gamma hbound
    (by simpa only [ha] using hc) (by simpa only [ha] using hd)
    (by rw [←ha])
  exact ⟨hp,by change Exponential R X; rw [hp]; exact exponential_exp R,hbound⟩

end DiophantineConsistency.ArithmeticPellPowerRecovery
