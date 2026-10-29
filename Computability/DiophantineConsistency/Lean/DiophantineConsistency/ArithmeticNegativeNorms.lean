import Foundation.FirstOrder.Arithmetic.IOpen.Basic
import Mathlib.Tactic.Ring

/-! Internal negative-unit exclusions for the maintained carrier factors.
Modulo four covers every square-minus-one discriminant, including base0/1.
The consecutive-product exclusion uses a bounded internal descent and the
absolute difference of its inverse root, without a signed-root hypothesis.
Signed product extraction and literal splitNatural binding are separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticNegativeNorms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Actual internal remainders, with no external residue-class oracle. -/
theorem square_mod_four (x : V) : (x*x)%4=0 ∨ (x*x)%4=1 := by
  obtain ⟨k,h|h⟩ := even_or_odd x
  · left
    rw [h,show (2*k)*(2*k)=(k*k)*4 by ring]
    exact mod_mul_self_left _ _
  · right
    rw [h,show (2*k+1)*(2*k+1)=(k*k+k)*4+1 by ring]
    exact mod_mul_add_of_lt _ _ (by simp : (1:V)<4)

/-- Uniform in A, including0 and1, and in t, including0. -/
theorem square_discriminant_ne_negative (A x t : V) :
    x*x+t*t+1 ≠ A*A*t*t := by
  intro he
  have h4 : (0:V)<4 := by simp
  have h12 : (1:V)<2 := by norm_num
  have h13 : (1:V)<3 := by norm_num
  have h1m : (1:V)%4=1 := by norm_num
  have h2m : (2:V)%4=2 := by norm_num
  have h3m : (3:V)%4=3 := by norm_num
  have hm := congrArg (fun z : V => z%4) he
  rw [show A*A*t*t=(A*A)*(t*t) by ring,
    mod_add (a:=x*x+t*t) (b:=1) h4,mod_add (a:=x*x) (b:=t*t) h4,
    mod_mul (a:=A*A) (b:=t*t) h4] at hm
  rcases square_mod_four x with hx|hx <;>
    rcases square_mod_four t with ht|ht <;>
    rcases square_mod_four A with hA|hA <;>
    simp only [hx,ht,hA,zero_add,add_zero,mul_zero,mul_one,
      one_add_one_eq_two,show (2:V)+1=3 by ring,zero_mod,h1m,h2m,h3m] at hm
  all_goals first
    | exact (ne_of_gt (by simp : (0:V)<1)) hm
    | exact (ne_of_gt (by simp : (0:V)<2)) hm
    | exact (ne_of_gt (by simp : (0:V)<3)) hm
    | exact (ne_of_gt h12) hm
    | exact (ne_of_gt h13) hm

private noncomputable def magnitude (x y : V) : V := (x-y)+(y-x)

private theorem magnitude_square (x y : V) :
    magnitude x y*magnitude x y+2*x*y=x*x+y*y := by
  have step (d x y : V) (he : d+x=y) : d*d+2*x*y=x*x+y*y := by
    rw [←he]
    ring
  rcases le_total x y with h|h
  · have he : y-x+x=y := tsub_add_cancel_of_le h
    simp only [magnitude,tsub_eq_zero_of_le h,zero_add]
    exact step (y-x) x y he
  · have he : x-y+y=x := tsub_add_cancel_of_le h
    simp only [magnitude,tsub_eq_zero_of_le h,add_zero]
    simpa only [mul_comm,mul_left_comm,mul_assoc,add_comm] using step (x-y) y x he

private theorem root_bound (n x y : V) (h : x*x+1=n*(n+1)*y*y) : x≤(n+1)*y := by
  have hsq : x*x<((n+1)*y)*((n+1)*y) := calc
    x*x<x*x+1 := lt_add_one _
    _=n*(n+1)*y*y := h
    _≤((n+1)*y)*((n+1)*y) := by
      have hm := mul_le_mul_of_nonneg_right (show n≤n+1 by simp) (Arithmetic.zero_le ((n+1)*y*y))
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hm
  exact le_of_lt (lt_of_mul_self_lt_mul_self₀ (by simp) hsq)

/-- The inverse ordinate decreases; the inverse root is an absolute difference. -/
theorem consecutive_negative_descent (n x y : V) (hn : 2≤n)
    (h : x*x+1=n*(n+1)*y*y) :
    ∃ u v : V, 0<v ∧ v<y ∧ u≤(n+1)*v ∧ u*u+1=n*(n+1)*v*v := by
  have hy : 0<y := pos_of_mul_pos_right (by rw [← h]; simp) (by simp)
  have hy1 := pos_iff_one_le.mp hy
  have h2 : (2:V)≤n*y*y := calc
    2≤n := hn
    _≤n*(y*y) := le_mul_of_one_le_right (by simp) (one_le_mul hy1 hy1)
    _=n*y*y := by ring
  have h1 : (1:V)<n*y*y := lt_of_lt_of_le (by simp : (1:V)<2) h2
  have hny : n*y<x := by
    apply lt_of_mul_self_lt_mul_self₀ (by simp)
    apply (add_lt_add_iff_right (1:V)).mp
    calc
      (n*y)*(n*y)+1<(n*y)*(n*y)+n*y*y := by
        simpa only [add_assoc] using add_lt_add_of_le_of_lt (le_refl ((n*y)*(n*y))) h1
      _=x*x+1 := by rw [h]; ring
  let A:=2*n+1
  let d:=n*(n+1)
  have hstrict : 2*x<A*y := by
    apply lt_of_mul_self_lt_mul_self₀ (by simp)
    calc
      (2*x)*(2*x)<(2*x)*(2*x)+(y*y+4) := lt_add_of_pos_right _ (by simp)
      _=(A*y)*(A*y) := by
        calc
          (2*x)*(2*x)+(y*y+4)=4*(x*x+1)+y*y := by ring
          _=4*(d*y*y)+y*y := by rw [h]
          _=(A*y)*(A*y) := by dsimp [A,d]; ring
  let v:=A*y-2*x
  let u:=magnitude (A*x) (2*d*y)
  have hvp : 0<v := tsub_pos_iff_lt.mpr hstrict
  have hv : v+2*x=A*y := tsub_add_cancel_of_le (le_of_lt hstrict)
  have hvsmall : v<y := by
    have he : v+2*n*y<y+2*n*y := calc
      v+2*n*y<v+2*x := by
        have h2x := mul_lt_mul_of_pos_left hny (by simp : (0:V)<2)
        simpa only [mul_assoc] using add_lt_add_of_le_of_lt (le_refl v) h2x
      _=A*y := hv
      _=y+2*n*y := by dsimp [A]; ring
    exact (add_lt_add_iff_right (2*n*y)).mp he
  let B:=4*A*d*x*y
  let C:=4*d*x*x+4*d*d*y*y
  have hu : u*u+B=(A*x)*(A*x)+(2*d*y)*(2*d*y) := by
    simpa only [show 2*(A*x)*(2*d*y)=B by dsimp [B]; ring] using
      magnitude_square (A*x) (2*d*y)
  have hvnorm : d*v*v+B=d*A*A*y*y+4*d*x*x := calc
    d*v*v+B=d*v*v+4*d*x*(A*y) := by dsimp [B]; ring
    _=d*(v+2*x)*(v+2*x)+4*d*x*x := by rw [←hv]; ring
    _=d*A*A*y*y+4*d*x*x := by rw [hv]; ring
  have hnew : u*u+1=d*v*v := by
    apply add_right_cancel (b:=B)
    calc
      (u*u+1)+B=(u*u+B)+1 := by ring
      _=((A*x)*(A*x)+(2*d*y)*(2*d*y))+1 := by rw [hu]
      _=C+(x*x+1) := by dsimp [C,A,d]; ring
      _=C+d*y*y := by rw [h]
      _=d*A*A*y*y+4*d*x*x := by dsimp [C,A,d]; ring
      _=d*v*v+B := hvnorm.symm
  exact ⟨u,v,hvp,hvsmall,root_bound n u v hnew,hnew⟩

/-- Bounded Delta0 root quantification supports genuine internal order induction. -/
theorem consecutive_ne_negative (n x y : V) (hn : 2≤n) : x*x+1≠n*(n+1)*y*y := by
  have bounded (y : V) : ∀ x≤(n+1)*y, x*x+1≠n*(n+1)*y*y := by
    induction y using ISigma1.sigma1_order_induction
    · definability
    case ind y ih =>
      intro x _ hx
      obtain ⟨u,v,_,hv,hbound,hnew⟩ := consecutive_negative_descent n x y hn hx
      exact ih v hv u hbound hnew
  intro h
  exact bounded y x (root_bound n x y h) h

/-- The actual main discriminant equals (a+2)²−1, without natural subtraction. -/
theorem main_ne_negative (a x t : V) : x*x+1≠((a+1)*(a+3))*t*t := by
  intro h
  apply square_discriminant_ne_negative (a+2) x t
  rw [show (a+2)*(a+2)*t*t=((a+1)*(a+3))*t*t+t*t by ring, ←h]
  ring

/-- No positivity of the strong square root is required. -/
theorem strong_ne_negative (a f i c : V) :
    f*f+1≠((a+1)*(a+3))*(i*c*c)*(i*c*c) := main_ne_negative a f (i*c*c)

/-- The square-coefficient auxiliary factor excludes−1 independently of strong. -/
theorem square_aux_ne_negative (S v y : V) :
    (S*v)*(S*v)+y*y+1≠S*S*y*y := square_discriminant_ne_negative S (S*v) y

end DiophantineConsistency.ArithmeticNegativeNorms
