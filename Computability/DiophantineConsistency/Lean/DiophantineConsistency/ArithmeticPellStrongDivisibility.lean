import DiophantineConsistency.ArithmeticPellRecurrence
import DiophantineConsistency.ArithmeticGcdNormalization
import Mathlib.Algebra.Ring.Divisibility.Basic

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
    exact ⟨ha,dvd_add ha hb⟩

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
    have htail : h∣ycoord m b*xcoord n b := dvd_mul_of_dvd_left hm _
    have hhead : h∣xcoord m b*ycoord n b := by
      apply dvd_remove (y := ycoord m b*xcoord n b) _ htail
      rwa [←(addition m n b).2]
    exact ⟨hm,unit_certificate_cancel (norm_unit_certificate b m h hm) hhead⟩
  · rintro ⟨hm,hn⟩
    refine ⟨hm,?_⟩
    rw [(addition m n b).2]
    exact dvd_add (dvd_mul_of_dvd_right hn (xcoord m b))
      (dvd_mul_of_dvd_left hm (xcoord n b))

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
      have step (u v : V) (huv : u≤v) (hup : 0<u) (hvsum : u+v≤k) :
          gcdValue (ycoord u b) (ycoord v b)=ycoord (gcdValue u v) b := by
        have hvk : v<k := lt_of_lt_of_le
          (by simpa only [add_comm] using lt_add_of_pos_right v hup) hvsum
        have he : u+(v-u)=v := add_tsub_cancel_of_le huv
        have hi := ih v hvk u huv (v-u) tsub_le_self (by rw [he])
        calc
          gcdValue (ycoord u b) (ycoord v b)=
              gcdValue (ycoord u b) (ycoord (u+(v-u)) b) := by rw [he]
          _=gcdValue (ycoord u b) (ycoord (v-u) b) := gcd_y_add b u (v-u)
          _=ycoord (gcdValue u (v-u)) b := hi
          _=ycoord (gcdValue u v) b := by rw [←gcd_add_right u (v-u),he]
      rcases le_total m n with hmn|hnm
      · exact step m n hmn (pos_iff_ne_zero.mpr hm0) hsum
      · simpa only [gcd_comm (ycoord n b) (ycoord m b),gcd_comm n m] using
          step n m hnm (pos_iff_ne_zero.mpr hn0) (by simpa only [add_comm] using hsum)
  exact bounded (m+n) m (by simp) n (by simp) le_rfl

/-- Actual growth, with no positive-modulus or standard-index assumption. -/
theorem y_strictMono (b : V) : StrictMono (fun m : V => ycoord m b) :=
  ArithmeticPellRecurrence.ordinate_strictMono b

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
  refine ⟨⟨a,?_⟩,⟨b,?_⟩,u,v,w,z,?_⟩
  · exact (congrArg (fun z : V => T*z) ha).trans (by ring)
  · exact (congrArg (fun z : V => T*z) hb).trans (by ring)
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
