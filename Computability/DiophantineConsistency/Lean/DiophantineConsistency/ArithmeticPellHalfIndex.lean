import DiophantineConsistency.ArithmeticPellIndexDivisibility
import DiophantineConsistency.ArithmeticPellResidueClasses

/-! Actual half-carrier index recovery at internal IΣ1 indices.
The odd quotient is exact natural division, never modular inversion.
Large-c and the rank half-window remain explicit caller obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellHalfIndex
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellPeriodicity
open ArithmeticPellResidueClasses ArithmeticPellClassification
open ArithmeticPellIndexDivisibility
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

-- Keep represented coordinates opaque to the definability simplifier.
attribute [local irreducible] xcoord ycoord

def SignMod (m x y : V) : Prop := x%m=y%m ∨ (x+y)%m=0

private theorem same_add {m x y z w : V} (hm : 0<m)
    (h : x%m=y%m) (h' : z%m=w%m) : (x+z)%m=(y+w)%m := by
  rw [mod_add hm,mod_add (a:=y) hm,h,h']

private theorem same_mul {m x y z w : V} (hm : 0<m)
    (h : x%m=y%m) (h' : z%m=w%m) : (x*z)%m=(y*w)%m := by
  rw [mod_mul hm,mod_mul (a:=y) hm,h,h']

theorem sign_symm {m x y : V} (h : SignMod m x y) : SignMod m y x := by
  rcases h with h|h
  · exact Or.inl h.symm
  · exact Or.inr (by simpa only [add_comm] using h)

theorem sign_trans {m x y z : V} (hm : 0<m)
    (h : SignMod m x y) (h' : SignMod m y z) : SignMod m x z := by
  rcases h with h|h <;> rcases h' with h'|h'
  · exact Or.inl (h.trans h')
  · exact Or.inr ((same_add hm h rfl).trans h')
  · exact Or.inr ((same_add hm rfl h'.symm).trans h)
  · apply Or.inl
    apply mod_add_cancel _ _ y _ hm
    exact h.trans (by simpa only [add_comm] using h'.symm)

theorem sign_square {m x y : V} (hm : 0<m) (h : SignMod m x y) :
    (x*x)%m=(y*y)%m := by
  rcases h with h|h
  · exact same_mul hm h h
  · have hz : (x+y)%m=(0:V)%m := by simpa using h
    have hx := same_mul hm (x:=x) (y:=x) rfl hz
    have hy := same_mul hm (x:=y) (y:=y) rfl hz
    apply mod_add_cancel _ _ (x*y) _ hm
    calc
      (x*x+x*y)%m=(x*(x+y))%m := by congr 1; ring
      _=0 := by simpa using hx
      _=(y*(x+y))%m := by simpa using hy.symm
      _=(y*y+x*y)%m := by congr 1; ring

theorem sign_reduce {m c x y : V} (hc : 0<c) (hd : c∣m)
    (h : SignMod m x y) : SignMod c x y := by
  rcases h with h|h
  · exact Or.inl (by simpa only [mod_reduce _ _ _ hc hd] using congrArg (fun t : V => t%c) h)
  · exact Or.inr (by simpa only [mod_reduce _ _ _ hc hd,zero_mod] using congrArg (fun t : V => t%c) h)

theorem sign_eq_of_half {m x y : V} (hx : 0<x) (hy : 0<y)
    (hxm : 2*x<m) (hym : 2*y<m) (h : SignMod m x y) : x=y := by
  have hx2 : x≤2*x := by simpa only [two_mul] using (show x≤x+x by simp)
  have hy2 : y≤2*y := by simpa only [two_mul] using (show y≤y+y by simp)
  rcases h with h|h
  · simpa only [mod_eq_self_of_lt (lt_of_le_of_lt hx2 hxm),
      mod_eq_self_of_lt (lt_of_le_of_lt hy2 hym)] using h
  · have hs : x+y<m := by
      apply Arithmetic.lt_of_mul_lt_mul_left (a:=(2:V))
      simpa only [mul_add,two_mul] using _root_.add_lt_add hxm hym
    rw [mod_eq_self_of_lt hs] at h
    exact False.elim ((ne_of_gt (add_pos hx hy)) h)

theorem y_two_step (t b : V) :
    ycoord (t+2) b+ycoord t b=2*(b+2)*ycoord (t+1) b := by
  rw [show t+2=(t+1)+1 by ring,y_succ,x_succ,y_succ]
  unfold delta
  ring

private theorem four_step (r : V→V) (B t : V)
    (h0 : r (t+2)+r t=2*B*r (t+1))
    (h1 : r (t+3)+r (t+1)=2*B*r (t+2))
    (h2 : r (t+4)+r (t+2)=2*B*r (t+3)) :
    r (t+4)+r t+2*r (t+2)=4*B*B*r (t+2) := by
  apply add_right_cancel (b:=2*B*r (t+1))
  calc
    (r (t+4)+r t+2*r (t+2))+2*B*r (t+1)=
        (r (t+4)+r (t+2))+(r (t+2)+r t)+2*B*r (t+1) := by ring
    _=2*B*r (t+3)+2*B*r (t+1)+2*B*r (t+1) := by rw [h2,h0]
    _=2*B*(r (t+3)+r (t+1))+2*B*r (t+1) := by ring
    _=4*B*B*r (t+2)+2*B*r (t+1) := by rw [h1]; ring

theorem odd_y_rec (h b : V) :
    ycoord (2*(h+2)+1) b+ycoord (2*h+1) b+2*ycoord (2*(h+1)+1) b=
      4*(b+2)*(b+2)*ycoord (2*(h+1)+1) b := by
  have h1 := y_two_step (2*h+1+1) b
  rw [show (2*h+1+1)+2=(2*h+1)+3 by ring,
    show (2*h+1+1)+1=(2*h+1)+2 by ring] at h1
  have h2 := y_two_step (2*h+1+2) b
  rw [show (2*h+1+2)+2=(2*h+1)+4 by ring,
    show (2*h+1+2)+1=(2*h+1)+3 by ring] at h2
  have hh := four_step (fun t => ycoord t b) (b+2) (2*h+1)
    (y_two_step _ b) h1 h2
  rw [show 2*h+1+4=2*(h+2)+1 by ring,
    show 2*h+1+2=2*(h+1)+1 by ring] at hh
  exact hh

theorem odd_x_rec (h b : V) :
    xcoord (2*(h+2)+1) b+xcoord (2*h+1) b+2*xcoord (2*(h+1)+1) b=
      4*(b+2)*(b+2)*xcoord (2*(h+1)+1) b := by
  have hh := x_reflection_add (2*h+1) 2 b
  have hx1 : xcoord 1 b=b+2 := by simpa using x_succ (0:V) b
  have hx2 := double_x_add_one (1:V) b
  rw [mul_one,hx1] at hx2
  calc
    xcoord (2*(h+2)+1) b+xcoord (2*h+1) b+2*xcoord (2*(h+1)+1) b=
        (xcoord (2*h+1+2*2) b+xcoord (2*h+1) b)+2*xcoord (2*h+1+2) b := by
      congr 2 <;> congr 1 <;> ring
    _=2*xcoord (2*h+1+2) b*(xcoord 2 b+1) := by rw [hh]; ring
    _=4*(b+2)*(b+2)*xcoord (2*(h+1)+1) b := by
      rw [hx2,show 2*h+1+2=2*(h+1)+1 by ring]; ring

theorem odd_x_dvd (h b : V) : b+2∣xcoord (2*h+1) b := by
  induction h using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    have hx1 : xcoord 1 b=b+2 := by simpa using x_succ (0:V) b
    simpa only [mul_zero,zero_add,hx1] using (dvd_refl (b+2))
  case succ h ih =>
    have he := x_reflection_add (2*h+1) 1 b
    have hx1 : xcoord 1 b=b+2 := by simpa using x_succ (0:V) b
    rw [hx1] at he
    have hs : b+2∣xcoord (2*(h+1)+1) b+xcoord (2*h+1) b := by
      refine ⟨2*xcoord (2*h+1+1) b,?_⟩
      calc
        xcoord (2*(h+1)+1) b+xcoord (2*h+1) b=
            xcoord (2*h+1+2*1) b+xcoord (2*h+1) b := by congr 2; ring
        _=(b+2)*(2*xcoord (2*h+1+1) b) := by rw [he]; ring
    exact ArithmeticPellStrongDivisibility.dvd_remove hs ih

noncomputable def oddQuotient (h b : V) : V := xcoord (2*h+1) b/(b+2)

instance odd_definable : 𝚺₁-Function₂[V] oddQuotient := by
  unfold oddQuotient
  definability

attribute [local irreducible] oddQuotient

theorem odd_exact (h b : V) : xcoord (2*h+1) b=(b+2)*oddQuotient h b := by
  unfold oddQuotient
  exact (mul_div_self_of_dvd.mpr (odd_x_dvd h b)).symm

theorem odd_zero (b : V) : oddQuotient 0 b=1 := by
  have he := odd_exact (0:V) b
  have hx1 : xcoord 1 b=b+2 := by simpa using x_succ (0:V) b
  have hb : 0<b+2 := by simp
  apply mul_left_cancel₀ (ne_of_gt hb)
  simpa only [mul_zero,zero_add,hx1,mul_one] using he.symm

theorem odd_one (b : V) : oddQuotient 1 b+3=4*(b+2)*(b+2) := by
  have h := x_reflection_add (1:V) 1 b
  have hx1 : xcoord 1 b=b+2 := by simpa using x_succ (0:V) b
  have hx2 := double_x_add_one (1:V) b
  rw [mul_one,hx1] at hx2
  have he := odd_exact (1:V) b
  rw [show (2:V)*1+1=3 by ring] at he
  apply mul_left_cancel₀ (ne_of_gt (show 0<b+2 by simp))
  calc
    (b+2)*(oddQuotient 1 b+3)=xcoord 3 b+(b+2)+2*(b+2) := by
      rw [show (b+2)*(oddQuotient 1 b+3)=(b+2)*oddQuotient 1 b+3*(b+2) by ring,
        ←he]
      ring
    _=2*(b+2)*(xcoord 2 b+1) := by
      have hh : xcoord 3 b+(b+2)=2*xcoord 2 b*(b+2) := by
        simpa only [show (1:V)+2*1=3 by ring,show (1:V)+1=2 by ring,hx1] using h
      rw [hh]; ring
    _=(b+2)*(4*(b+2)*(b+2)) := by rw [hx2]; ring

theorem odd_rec (h b : V) :
    oddQuotient (h+2) b+oddQuotient h b+2*oddQuotient (h+1) b=
      4*(b+2)*(b+2)*oddQuotient (h+1) b := by
  apply mul_left_cancel₀ (ne_of_gt (show 0<b+2 by simp))
  have he := odd_x_rec h b
  rw [odd_exact,odd_exact,odd_exact] at he
  simpa only [mul_add,mul_assoc,mul_left_comm,mul_comm] using he

/- The following algebraic transport has no inversion of the coefficient. -/
theorem transport_equal (m k l u0 u1 u2 v0 v1 v2 : V) (hm : 0<m)
    (hk : (k+l)%m=(4:V)%m)
    (hu : u2+u0+2*u1=k*u1) (hv : v2+v0+2*v1=l*v1)
    (h0 : u0%m=v0%m) (h1 : (u1+v1)%m=0) : u2%m=v2%m := by
  have hzero : (u1+v1)%m=(0:V)%m := by simpa using h1
  have h2zero : (2*(u1+v1))%m=0 := by simpa using same_mul hm (x:=(2:V)) rfl hzero
  have hkzero : (k*(u1+v1))%m=0 := by simpa using same_mul hm (x:=k) rfl hzero
  have hkey : (k*u1+2*v1)%m=(l*v1+2*u1)%m := by
    calc
      (k*u1+2*v1)%m=(k*u1+2*v1+2*(u1+v1))%m := by
        exact (mod_add_remove_right_of_dvd (mod_eq_zero_iff_dvd.mp h2zero) hm).symm
      _=(k*u1+2*u1+4*v1)%m := by congr 1; ring
      _=(k*u1+2*u1+(k+l)*v1)%m := same_add hm rfl (same_mul hm hk.symm rfl)
      _=(l*v1+2*u1+k*(u1+v1))%m := by congr 1; ring
      _=(l*v1+2*u1)%m := mod_add_remove_right_of_dvd (mod_eq_zero_iff_dvd.mp hkzero) hm
  apply mod_add_cancel _ _ (u0+2*u1+v0+2*v1) _ hm
  calc
    (u2+(u0+2*u1+v0+2*v1))%m=(k*u1+v0+2*v1)%m := by
      rw [show u2+(u0+2*u1+v0+2*v1)=(u2+u0+2*u1)+v0+2*v1 by ring,hu]
    _=(v0+(k*u1+2*v1))%m := by congr 1; ring
    _=(u0+(l*v1+2*u1))%m := same_add hm h0.symm hkey
    _=(v2+(u0+2*u1+v0+2*v1))%m := by
      rw [show v2+(u0+2*u1+v0+2*v1)=(v2+v0+2*v1)+u0+2*u1 by ring,hv]
      congr 1; ring

theorem transport_opposite (m k l u0 u1 u2 v0 v1 v2 : V) (hm : 0<m)
    (hk : (k+l)%m=(4:V)%m)
    (hu : u2+u0+2*u1=k*u1) (hv : v2+v0+2*v1=l*v1)
    (h0 : (u0+v0)%m=0) (h1 : u1%m=v1%m) : (u2+v2)%m=0 := by
  have hkey : (k*u1+l*v1)%m=(2*(u1+v1))%m := by
    calc
      (k*u1+l*v1)%m=(k*v1+l*v1)%m := same_add hm (same_mul hm rfl h1) rfl
      _=((k+l)*v1)%m := by congr 1; ring
      _=(4*v1)%m := same_mul hm hk rfl
      _=(2*(v1+v1))%m := by congr 1; ring
      _=(2*(u1+v1))%m := same_mul hm rfl (same_add hm h1.symm rfl)
  have he : (u2+v2+2*(u1+v1))%m=(0+2*(u1+v1))%m := by
    calc
      (u2+v2+2*(u1+v1))%m=(u2+v2+2*(u1+v1)+(u0+v0))%m :=
        (mod_add_remove_right_of_dvd (mod_eq_zero_iff_dvd.mp h0) hm).symm
      _=((u2+u0+2*u1)+(v2+v0+2*v1))%m := by congr 1; ring
      _=(2*(u1+v1))%m := by rw [hu,hv]; exact hkey
      _=(0+2*(u1+v1))%m := by rw [zero_add]
  simpa only [zero_mod] using mod_add_cancel (u2+v2) 0 (2*(u1+v1)) m hm he

/-- The ordinate after two Pell steps. -/
theorem y_two (a : V) : ycoord 2 a=2*(a+2) := by
  have h := y_two_step (0:V) a
  have hy1 : ycoord 1 a=1 := by simpa using y_succ (0:V) a
  simpa only [zero_add,y_zero,add_zero,hy1,mul_one] using h

theorem y_three (a : V) : ycoord 3 a+1=4*(a+2)*(a+2) := by
  have h := y_two_step (1:V) a
  have hy1 : ycoord 1 a=1 := by simpa using y_succ (0:V) a
  have hy2 := y_two a
  rw [show (1:V)+2=3 by ring,show (1:V)+1=2 by ring,hy1,hy2] at h
  exact h.trans (by ring)

/-- The sign alternates; no square root is cancelled modulo f. -/
theorem quotient_mod_norm (a I f h : V) (hI : 2≤I) (hf : 0<f)
    (hn : I*I+delta a=delta a*f*f) :
    SignMod f (oddQuotient h (I-2)) (ycoord (2*h+1) a) := by
  let b := I-2
  have hb : b+2=I := tsub_add_cancel_of_le hI
  have hcoef : (4*(b+2)*(b+2)+4*(a+2)*(a+2))%f=(4:V)%f := by
    have he : 4*(b+2)*(b+2)+4*(a+2)*(a+2)=4+f*(4*delta a*f) := by
      rw [hb]
      calc
        4*I*I+4*(a+2)*(a+2)=4+4*(I*I+delta a) := by unfold delta; ring
        _=4+f*(4*delta a*f) := by rw [hn]; ring
    rw [he,mod_add_mul' _ _ hf]
  have hfirst : (oddQuotient 1 b+ycoord 3 a)%f=0 := by
    have he : oddQuotient 1 b+ycoord 3 a=f*(4*delta a*f) := by
      apply add_right_cancel (b:=(4:V))
      calc
        (oddQuotient 1 b+ycoord 3 a)+4=
            (oddQuotient 1 b+3)+(ycoord 3 a+1) := by ring
        _=4*I*I+4*(a+2)*(a+2) := by rw [odd_one,y_three,hb]
        _=f*(4*delta a*f)+4 := by
          calc
            4*I*I+4*(a+2)*(a+2)=4*(I*I+delta a)+4 := by unfold delta; ring
            _=f*(4*delta a*f)+4 := by rw [hn]; ring
    rw [he,mod_mul_self_right]
  have all (t : V) :
      (oddQuotient t b%f=ycoord (2*t+1) a%f ∧
        (oddQuotient (t+1) b+ycoord (2*(t+1)+1) a)%f=0) ∨
      ((oddQuotient t b+ycoord (2*t+1) a)%f=0 ∧
        oddQuotient (t+1) b%f=ycoord (2*(t+1)+1) a%f) := by
    induction t using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      apply Or.inl
      constructor
      · have hy1 : ycoord 1 a=1 := by simpa using y_succ (0:V) a
        simp only [mul_zero,zero_add,odd_zero,hy1]
      · simpa only [zero_add,show (2:V)*1+1=3 by ring] using hfirst
    case succ t ih =>
      rcases ih with ⟨h0,h1⟩|⟨h0,h1⟩
      · apply Or.inr
        refine ⟨h1,?_⟩
        have he := transport_equal f (4*(b+2)*(b+2)) (4*(a+2)*(a+2))
          _ _ _ _ _ _ hf hcoef (odd_rec t b) (odd_y_rec t a) h0 h1
        simpa only [add_assoc,one_add_one_eq_two] using he
      · apply Or.inl
        refine ⟨h1,?_⟩
        have he := transport_opposite f (4*(b+2)*(b+2)) (4*(a+2)*(a+2))
          _ _ _ _ _ _ hf hcoef (odd_rec t b) (odd_y_rec t a) h0 h1
        simpa only [add_assoc,one_add_one_eq_two] using he
  rcases all h with h|h
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- Modulo an ordinate divisor the same quotient represents the signed odd index. -/
theorem quotient_mod_divisor (I c h : V) (hI : 2≤I) (hc : 0<c) (hd : c∣I) :
    SignMod c (oddQuotient h (I-2)) (2*h+1) := by
  let b := I-2
  have hb : b+2=I := tsub_add_cancel_of_le hI
  have hd4 : c∣4*I*I := by
    obtain ⟨v,hv⟩ := hd
    exact ⟨4*v*I,by rw [hv]; ring⟩
  have hcoef : (4*(b+2)*(b+2)+4)%c=(4:V)%c := by
    rw [hb]
    exact mod_add_remove_left_of_dvd hd4 hc
  have hfirst : (oddQuotient 1 b+3)%c=0 := by
    rw [odd_one,hb]
    exact mod_eq_zero_iff_dvd.mpr hd4
  have all (t : V) :
      (oddQuotient t b%c=(2*t+1)%c ∧
        (oddQuotient (t+1) b+(2*(t+1)+1))%c=0) ∨
      ((oddQuotient t b+(2*t+1))%c=0 ∧
        oddQuotient (t+1) b%c=(2*(t+1)+1)%c) := by
    induction t using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      exact Or.inl ⟨by simp [odd_zero],by simpa only [zero_add,show (2:V)*1+1=3 by ring] using hfirst⟩
    case succ t ih =>
      have ht : (2*(t+2)+1)+(2*t+1)+2*(2*(t+1)+1)=4*(2*(t+1)+1) := by ring
      rcases ih with ⟨h0,h1⟩|⟨h0,h1⟩
      · apply Or.inr
        refine ⟨h1,?_⟩
        have he := transport_equal c (4*(b+2)*(b+2)) 4
          _ _ _ _ _ _ hc hcoef (odd_rec t b) ht h0 h1
        simpa only [add_assoc,one_add_one_eq_two] using he
      · apply Or.inl
        refine ⟨h1,?_⟩
        have he := transport_opposite c (4*(b+2)*(b+2)) 4
          _ _ _ _ _ _ hc hcoef (odd_rec t b) ht h0 h1
        simpa only [add_assoc,one_add_one_eq_two] using he
  rcases all h with h|h
  · exact Or.inl h.1
  · exact Or.inr h.1

private theorem y_step_two (a j : V) (hj : 1≤j) :
    ycoord j a+2≤ycoord (j+1) a := by
  have hx : 2≤xcoord j a := by
    have h := lt_iff_succ_le.mp (lt_of_le_of_lt (le_trans hj (time_le_y j a)) (y_lt_x j a))
    simpa only [one_add_one_eq_two] using h
  rw [y_succ,add_comm (ycoord j a) 2]
  exact _root_.add_le_add hx (le_mul_of_one_le_left (by simp) (base_ge_one a))

theorem twice_index_lt_y (a p : V) (hp : 3≤p) : 2*p<ycoord p a := by
  have all (t : V) : 2*(t+3)<ycoord (t+3) a := by
    induction t using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      have ha : (2:V)≤a+2 := by simp
      have hsq : (4:V)≤(a+2)*(a+2) := by
        simpa only [show (2:V)*2=4 by ring] using mul_le_mul ha ha (by simp) (by simp)
      have h16 : (16:V)≤ycoord 3 a+1 := by
        rw [y_three]
        simpa only [show (4:V)*4=16 by ring,mul_assoc] using mul_le_mul_of_nonneg_left hsq (by simp : (0:V)≤4)
      have h716 : (7:V)<16 := by norm_num
      have h7 : (7:V)<ycoord 3 a+1 := lt_of_lt_of_le h716 h16
      have h6 : (6:V)<ycoord 3 a := by
        have hh : (6:V)+1<ycoord 3 a+1 := by simpa only [show (6:V)+1=7 by ring] using h7
        exact (add_lt_add_iff_right (1:V)).mp hh
      simpa only [zero_add,show (2:V)*3=6 by ring] using h6
    case succ t ih =>
      have hj : (1:V)≤t+3 := by
        exact le_trans (by simp : (1:V)≤3) (by simp)
      have he0 : 2*(t+3)+2<ycoord (t+3) a+2 := by
        simpa only [add_comm] using _root_.add_lt_add_right ih 2
      simpa only [show 2*(t+3)+2=2*(t+1+3) by ring,
        show t+3+1=t+1+3 by ring] using lt_of_lt_of_le he0 (y_step_two a (t+3) hj)
  have h := all (p-3)
  simpa only [tsub_add_cancel_of_le hp] using h

/-- Main and both auxiliary indices are derived from the actual norms. -/
theorem half_index (a c d f i R y u : V)
    (hc : 0<c) (hi : 0<i) (hf : 0<f) (hR : 0<R) (_hy : 0<y)
    (hmain : d*d=1+delta a*c*c)
    (hstrong : (i*c*c)*(i*c*c)+delta a=delta a*f*f)
    (hbig : (a+2)*delta a*delta a<c) (hhalf : 2*R<c)
    (haux : (i*c*c)*(i*c*c)*u*u+y*y=1+(i*c*c)*(i*c*c)*y*y)
    (huf : SignMod f u c) (huc : SignMod c u R) :
    d=xcoord R a ∧ c=ycoord R a := by
  obtain ⟨p,_,hd,hcp⟩ := solution_index a d c hmain
  have hp : 0<p := pos_iff_ne_zero.mpr (fun hz => (ne_of_gt hc) (by simpa [hz] using hcp.symm))
  have hdelta : (3:V)≤delta a := by
    unfold delta
    simpa only [one_mul] using mul_le_mul (show (1:V)≤a+1 by simp)
      (show (3:V)≤a+3 by simp) (by simp) (by simp)
  have hdd : (2:V)≤delta a*delta a := le_trans (le_trans (by rw [show (3:V)=2+1 by ring]; simp : (2:V)≤3) hdelta)
    (le_mul_of_one_le_right (by simp) (le_trans (by simp : (1:V)≤3) hdelta))
  have htwo : 2*(a+2)<c := lt_of_le_of_lt (calc
    2*(a+2)=(a+2)*2 := by ring
    _≤(a+2)*(delta a*delta a) := mul_le_mul_of_nonneg_left hdd (Arithmetic.zero_le (a+2))
    _=(a+2)*delta a*delta a := by ring) hbig
  have hp3 : 3≤p := by
    have hp2 : 2<p := by
      by_contra hn
      have hp' : p≤2 := le_of_not_gt hn
      have he := (y_strictMono a).monotone hp'
      rw [hcp,y_two] at he
      exact (not_lt_of_ge he) htwo
    simpa only [show (2:V)+1=3 by ring] using lt_iff_succ_le.mp hp2
  have hpc : 2*p<c := by rw [←hcp]; exact twice_index_lt_y a p hp3
  obtain ⟨m,hm,hfm,_,hcm,_⟩ := relaxed_auxiliary a c p i f hp hi hf hcp.symm (by simpa only [mul_assoc] using hstrong) hbig
  have hcmle : c≤m := Arithmetic.le_of_dvd hm hcm
  have hpm : 2*p≤m := le_trans (le_of_lt hpc) hcmle
  let I := i*c*c
  have hc1 : 1≤c := by simpa using lt_iff_succ_le.mp hc
  have hi1 : 1≤i := by simpa using lt_iff_succ_le.mp hi
  have hcI : c≤I := calc
    c≤i*c := le_mul_of_one_le_left (by simp) hi1
    _≤i*c*c := le_mul_of_one_le_right (by simp) hc1
  have hI2 : 2≤I := le_trans (le_trans (le_mul_of_one_le_right (by simp) (base_ge_one a)) (le_of_lt htwo)) hcI
  have hIpos : 0<I := lt_of_lt_of_le (by simp : (0:V)<2) hI2
  have hb : I-2+2=I := tsub_add_cancel_of_le hI2
  have hdI : 1+delta (I-2)=I*I := by
    calc
      1+delta (I-2)=(I-2+2)*(I-2+2) := by unfold delta; ring
      _=I*I := by rw [hb]
  have hnorm : (I*u)*(I*u)=1+delta (I-2)*y*y := by
    apply add_right_cancel (b:=y*y)
    calc
      (I*u)*(I*u)+y*y=1+I*I*y*y := by simpa only [I,mul_assoc,mul_comm,mul_left_comm] using haux
      _=(1+delta (I-2)*y*y)+y*y := by rw [←hdI]; ring
  obtain ⟨s,_,hxs,_⟩ := solution_index (I-2) (I*u) y hnorm
  have hdiv : I∣xcoord s (I-2) := ⟨u,hxs⟩
  obtain ⟨h,hs⟩ := odd_index_witness (I-2) s (by simpa only [hb] using hdiv)
  have hu : u=oddQuotient h (I-2) := by
    apply mul_left_cancel₀ (ne_of_gt hIpos)
    calc
      I*u=xcoord (2*h+1) (I-2) := by rw [←hs,hxs]
      _=I*oddQuotient h (I-2) := by rw [odd_exact,hb]
  have hyf : SignMod f u (ycoord s a) := by
    rw [hu,hs]
    exact quotient_mod_norm a I f h hI2 hf hstrong
  have hysq : (ycoord s a*ycoord s a)%f=(c*c)%f :=
    sign_square hf (sign_trans hf (sign_symm hyf) huf)
  have hdoub : xcoord (2*s) a%f=xcoord (2*p) a%f := by
    rw [double_x,double_x, hcp]
    have he := same_mul hf (x:=2*delta a) rfl hysq
    exact same_add hf rfl (by simpa only [mul_assoc] using he)
  have hstep : SignMod m s p := doubled_step_down a m p s hp hpm (Or.inl (by simpa only [←hfm] using hdoub))
  have hcis : SignMod c u s := by
    rw [hu,hs]
    exact quotient_mod_divisor I c h hI2 hc ⟨i*c,by dsimp [I]; ring⟩
  have hRp : SignMod c R p := sign_trans hc (sign_symm huc)
    (sign_trans hc hcis (sign_reduce hc hcm hstep))
  have hpr : R=p := sign_eq_of_half hR hp hhalf hpc hRp
  subst R
  exact ⟨hd.symm,hcp.symm⟩

noncomputable def absdiff (x y : V) : V := (x-y)+(y-x)

/-- Both signs, including equality, are handled by exact ordered differences. -/
theorem absdiff_residue (m L M v : V) (hm : 0<m)
    (he : (L+v)%m=M%m) : SignMod m (absdiff L M) v := by
  rcases le_total L M with h|h
  · have hu : absdiff L M=M-L := by simp only [absdiff,tsub_eq_zero_of_le h,zero_add]
    apply Or.inl
    apply mod_add_cancel _ _ L _ hm
    rw [hu,tsub_add_cancel_of_le h]
    exact he.symm.trans (by congr 1; ring)
  · have hu : absdiff L M=L-M := by simp only [absdiff,tsub_eq_zero_of_le h,add_zero]
    apply Or.inr
    have hh : ((absdiff L M+v)+M)%m=(0+M)%m := by
      rw [hu]
      calc
        ((L-M+v)+M)%m=((L-M+M)+v)%m := by congr 1; ring
        _=(0+M)%m := by rw [tsub_add_cancel_of_le h,zero_add]; exact he
    simpa only [zero_mod] using mod_add_cancel _ _ M _ hm hh

/-- The maintained strict factor supplies the full relaxed coefficient
delta(a)*i. The signed V is represented exactly as an absolute difference. -/
theorem literal_half_index (a c d f i R y T : V)
    (hc : 0<c) (hi : 0<i) (hf : 0<f) (hR : 0<R) (hy : 0<y)
    (hmain : d*d=1+delta a*c*c)
    (hstrict : f*f=1+delta a*(i*c*c)*(i*c*c))
    (hbig : (a+2)*delta a*delta a<c) (hhalf : 2*R<c)
    (haux : let I:=delta a*i*c*c
      let u:=absdiff (f*f*c*T) (f*f*R+c)
      I*I*u*u+y*y=1+I*I*y*y) :
    d=xcoord R a ∧ c=ycoord R a := by
  let u := absdiff (f*f*c*T) (f*f*R+c)
  have hd : 0<delta a := by unfold delta; exact mul_pos (by simp) (by simp)
  have hnorm : ((delta a*i)*c*c)*((delta a*i)*c*c)+delta a=delta a*f*f := by
    calc
      ((delta a*i)*c*c)*((delta a*i)*c*c)+delta a=
          delta a*(1+delta a*(i*c*c)*(i*c*c)) := by ring
      _=delta a*f*f := by rw [←hstrict]; ring
  have hf1 : (f*f)%c=(1:V)%c := by
    have he : f*f=1+c*(delta a*i*i*c*c*c) := by rw [hstrict]; ring
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
      _=(f*f*R)%c := by simpa only [one_mul] using (same_mul hc hf1 (z:=R) rfl).symm
      _=(f*f*R+c)%c := (mod_add_remove_right hc).symm
  exact half_index a c d f (delta a*i) R y u hc (mul_pos hd hi) hf hR hy
    hmain hnorm hbig hhalf haux huf huc

end DiophantineConsistency.ArithmeticPellHalfIndex

