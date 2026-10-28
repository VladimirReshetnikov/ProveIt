import DiophantineConsistency.ArithmeticPellRecurrence
import DiophantineConsistency.ArithmeticGcdNormalization

/-! Strong divisibility of the represented Pell ordinate at all internal
indices. Norm-derived natural Bezout certificates supply cancellation;
bounded Sigma1 descent on the sum of indices supplies the gcd identity.
The later large-c index forcing and full relaxed integrality are separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellStrongDivisibility
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticGcdNormalization
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem dvd_sum {h x y : V} (hx : h∣x) (hy : h∣y) : h∣x+y := by
  obtain ⟨u,hu⟩ := hx
  obtain ⟨v,hv⟩ := hy
  exact ⟨u+v,by rw [hu,hv]; ring⟩

private theorem dvd_product {h x : V} (hx : h∣x) (y : V) : h∣x*y := by
  obtain ⟨u,hu⟩ := hx
  exact ⟨u*y,by rw [hu]; ring⟩

/-- Divisible summand removal, also for divisor zero. -/
theorem dvd_remove {h x y : V} (hs : h∣x+y) (hy : h∣y) : h∣x := by
  have hc : Bez (x+y) y x := ⟨0,1,1,0,by ring⟩
  exact bez_divisor hc hs hy

private theorem gcd_same_common (a b c d : V)
    (h : ∀ z : V, (z∣a ∧ z∣b) ↔ (z∣c ∧ z∣d)) :
    gcdValue a b=gcdValue c d := by
  have hab := gcd_spec a b
  have hcd := gcd_spec c d
  have h₁ := (h (gcdValue a b)).mp ⟨hab.1,hab.2.1⟩
  have h₂ := (h (gcdValue c d)).mpr ⟨hcd.1,hcd.2.1⟩
  exact Arithmetic.dvd_antisymm (bez_divisor hcd.2.2 h₁.1 h₁.2)
    (bez_divisor hab.2.2 h₂.1 h₂.2)

theorem gcd_comm (a b : V) : gcdValue a b=gcdValue b a :=
  gcd_same_common a b b a (fun _ => and_comm)

theorem gcd_left_of_dvd (a b : V) (h : a∣b) : gcdValue a b=a := by
  apply Eq.symm
  apply (gcd_graph a b a).mp
  exact ⟨dvd_refl a,h,0,0,1,0,by simp⟩

@[simp] theorem gcd_zero_right (a : V) : gcdValue a 0=a :=
  gcd_left_of_dvd a 0 (dvd_zero a)

@[simp] theorem gcd_zero_left (a : V) : gcdValue 0 a=a := by
  rw [gcd_comm,gcd_zero_right]

theorem gcd_add_right (a b : V) : gcdValue a (a+b)=gcdValue a b := by
  apply gcd_same_common
  intro h
  constructor
  · rintro ⟨ha,hs⟩
    exact ⟨ha,dvd_remove (by simpa only [add_comm] using hs) ha⟩
  · rintro ⟨ha,hb⟩
    exact ⟨ha,dvd_sum ha hb⟩

/-- The actual norm supplies a unit certificate against any ordinate divisor.
No positivity of h or modular inverse premise is needed. -/
theorem norm_unit_certificate (b m h : V) (hm : h∣ycoord m b) :
    Bez (xcoord m b) h 1 := by
  obtain ⟨k,hk⟩ := hm
  refine ⟨0,delta b*k*ycoord m b,xcoord m b,0,?_⟩
  calc
    1+xcoord m b*0+h*(delta b*k*ycoord m b)=
        1+delta b*ycoord m b*ycoord m b := by rw [hk]; ring
    _=xcoord m b*xcoord m b := (norm m b).symm
    _=xcoord m b*xcoord m b+h*0 := by simp

theorem common_divisors_add (b m n h : V) :
    (h∣ycoord m b ∧ h∣ycoord (m+n) b) ↔
      (h∣ycoord m b ∧ h∣ycoord n b) := by
  constructor
  · rintro ⟨hm,hs⟩
    have htail : h∣ycoord m b*xcoord n b := dvd_product hm _
    have hhead : h∣xcoord m b*ycoord n b := by
      apply dvd_remove (y := ycoord m b*xcoord n b) _ htail
      rwa [←(addition m n b).2]
    exact ⟨hm,unit_certificate_cancel (norm_unit_certificate b m h hm) hhead⟩
  · rintro ⟨hm,hn⟩
    refine ⟨hm,?_⟩
    rw [(addition m n b).2]
    exact dvd_sum (by simpa only [mul_comm] using dvd_product hn (xcoord m b))
      (dvd_product hm (xcoord n b))

theorem gcd_y_add (b m n : V) :
    gcdValue (ycoord m b) (ycoord (m+n) b)=
      gcdValue (ycoord m b) (ycoord n b) :=
  gcd_same_common _ _ _ _ (common_divisors_add b m n)

/-- All indices are internal. The bounded two-variable invariant is Sigma1;
each positive branch decreases the sum and justifies its subtraction. -/
theorem strong_divisibility (b m n : V) :
    gcdValue (ycoord m b) (ycoord n b)=ycoord (gcdValue m n) b := by
  have bounded (k : V) : ∀ m≤k, ∀ n≤k, m+n≤k →
      gcdValue (ycoord m b) (ycoord n b)=ycoord (gcdValue m n) b := by
    induction k using ISigma1.sigma1_order_induction
    · definability
    case ind k ih =>
      intro m hm n hn hsum
      by_cases hm0 : m=0
      · subst m; simp
      by_cases hn0 : n=0
      · subst n; simp
      have hmp : 0<m := lt_of_le_of_ne (Arithmetic.zero_le m) (Ne.symm hm0)
      have hnp : 0<n := lt_of_le_of_ne (Arithmetic.zero_le n) (Ne.symm hn0)
      rcases le_total m n with hmn|hnm
      · have hnk : n<k := lt_of_lt_of_le
          (by simpa only [add_comm] using lt_add_of_pos_right n hmp) hsum
        have he : m+(n-m)=n := add_tsub_cancel_of_le hmn
        have hi := ih n hnk m hmn (n-m) tsub_le_self (by rw [he])
        calc
          gcdValue (ycoord m b) (ycoord n b)=
              gcdValue (ycoord m b) (ycoord (m+(n-m)) b) := by rw [he]
          _=gcdValue (ycoord m b) (ycoord (n-m) b) := gcd_y_add b m (n-m)
          _=ycoord (gcdValue m (n-m)) b := hi
          _=ycoord (gcdValue m n) b := by rw [←gcd_add_right m (n-m),he]
      · have hmk : m<k := lt_of_lt_of_le (lt_add_of_pos_right m hnp) hsum
        have he : n+(m-n)=m := add_tsub_cancel_of_le hnm
        have hi := ih m hmk n hnm (m-n) tsub_le_self (by rw [he])
        calc
          gcdValue (ycoord m b) (ycoord n b)=
              gcdValue (ycoord n b) (ycoord m b) := gcd_comm _ _
          _=gcdValue (ycoord n b) (ycoord (n+(m-n)) b) := by rw [he]
          _=gcdValue (ycoord n b) (ycoord (m-n) b) := gcd_y_add b n (m-n)
          _=ycoord (gcdValue n (m-n)) b := hi
          _=ycoord (gcdValue n m) b := by rw [←gcd_add_right n (m-n),he]
          _=ycoord (gcdValue m n) b := by rw [gcd_comm n m]
  exact bounded (m+n) m (by simp) n (by simp) le_rfl

private theorem y_add_ge (m r b : V) : ycoord m b+r≤ycoord (m+r) b := by
  have h₁ : ycoord r b≤xcoord m b*ycoord r b := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_x m b)
      (Arithmetic.zero_le (ycoord r b))
  have h₂ : ycoord m b≤ycoord m b*xcoord r b := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_x r b)
      (Arithmetic.zero_le (ycoord m b))
  rw [(addition m r b).2]
  calc
    ycoord m b+r≤ycoord m b+ycoord r b := add_le_add le_rfl (time_le_y r b)
    _≤ycoord m b*xcoord r b+xcoord m b*ycoord r b := add_le_add h₂ h₁
    _=xcoord m b*ycoord r b+ycoord m b*xcoord r b := add_comm _ _

/-- Actual growth, with no positive-modulus or standard-index assumption. -/
theorem y_strictMono (b : V) : StrictMono (fun m : V => ycoord m b) := by
  intro m n hmn
  have hlt : ycoord m b<ycoord m b+(n-m) :=
    lt_add_of_pos_right _ (tsub_pos_iff_lt.mpr hmn)
  have hle := y_add_ge m (n-m) b
  rw [add_tsub_cancel_of_le (le_of_lt hmn)] at hle
  exact lt_of_lt_of_le hlt hle

theorem y_dvd_iff (b m n : V) : ycoord m b∣ycoord n b ↔ m∣n := by
  constructor
  · intro h
    have hg : gcdValue (ycoord m b) (ycoord n b)=ycoord m b :=
      gcd_left_of_dvd _ _ h
    have he : gcdValue m n=m := (y_strictMono b).injective
      ((strong_divisibility b m n).symm.trans hg)
    have hn := (gcd_spec m n).2.1
    rwa [he] at hn
  · intro h
    have hg : gcdValue (ycoord m b) (ycoord n b)=ycoord m b := by
      rw [strong_divisibility,gcd_left_of_dvd m n h]
    have hn := (gcd_spec (ycoord m b) (ycoord n b)).2.1
    rwa [hg] at hn

/-- Multiplication of the actual gcd certificate; no cancellation of T. -/
theorem gcd_scale (T x y : V) : gcdValue (T*x) (T*y)=T*gcdValue x y := by
  have hg := gcd_spec x y
  obtain ⟨a,ha⟩ := hg.1
  obtain ⟨b,hb⟩ := hg.2.1
  obtain ⟨u,v,w,z,he⟩ := hg.2.2
  apply Eq.symm
  apply (gcd_graph (T*x) (T*y) (T*gcdValue x y)).mp
  refine ⟨⟨a,by rw [ha]; ring⟩,⟨b,by rw [hb]; ring⟩,u,v,w,z,?_⟩
  calc
    T*gcdValue x y+(T*x)*u+(T*y)*v=T*(gcdValue x y+x*u+y*v) := by ring
    _=T*(x*w+y*z) := by rw [he]
    _=(T*x)*w+(T*y)*z := by ring

/-- The scaled common-divisor consequence used later by relaxed integrality.
It does not yet supply the large-c estimate or force an index multiple. -/
theorem scaled_common_divisor (b m n T h : V)
    (hm : h∣T*ycoord m b) (hn : h∣T*ycoord n b) :
    h∣T*ycoord (gcdValue m n) b := by
  have hc := bez_divisor (gcd_spec (T*ycoord m b) (T*ycoord n b)).2.2 hm hn
  rwa [gcd_scale,strong_divisibility] at hc
end DiophantineConsistency.ArithmeticPellStrongDivisibility
