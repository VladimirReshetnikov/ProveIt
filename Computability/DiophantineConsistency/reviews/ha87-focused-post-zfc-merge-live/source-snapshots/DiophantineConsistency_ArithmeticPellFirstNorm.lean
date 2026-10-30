import DiophantineConsistency.ArithmeticPellCongruences
import DiophantineConsistency.ArithmeticPellKnownUnit

/-! Classification of the actual first norm x²=1+Q(Q+1)k² in internal
arithmetic. Write Q=q+1 to avoid a hidden positivity/subtraction premise.
Descent by the explicit unit(2Q+1,2) proves the doubled second coordinate;
no external fundamental-unit or parity theorem is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellFirstNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellCongruences
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def discriminant (q : V) : V := (q+1)*(q+2)

theorem positive_x (q x k : V) (h : x*x=1+discriminant q*k*k) : 0<x := by
  exact pos_of_mul_pos_left (b := x) (by rw [h]; simp) (Arithmetic.zero_le x)

theorem x_bound (q x k : V) (h : x*x=1+discriminant q*k*k) : x≤(q+2)*k+1 := by
  apply nonneg_le_nonneg_of_sq_le_sq (Arithmetic.zero_le _)
  calc
    x*x=1+discriminant q*k*k := h
    _≤(1+discriminant q*k*k)+((q+2)*k*k+2*(q+2)*k) := by simp
    _=((q+2)*k+1)*((q+2)*k+1) := by unfold discriminant; ring

/-- There is no solution at ordinate1: its square would lie strictly
between the consecutive squares (q+1)² and (q+2)². -/
theorem two_le_ordinate (q x k : V) (hk : 0<k)
    (h : x*x=1+discriminant q*k*k) : 2≤k := by
  by_contra hn
  have hle : k≤1 := lt_two_iff_le_one.mp (lt_of_not_ge hn)
  have ho : k=1 := le_antisymm hle (pos_iff_one_le.mp hk)
  subst k
  simp only [mul_one] at h
  have hlo : q+1<x := by
    apply lt_of_mul_self_lt_mul_self₀ (by simp)
    calc
      (q+1)*(q+1)<(q+1)*(q+1)+(q+2) := by simp
      _=x*x := by rw [h]; unfold discriminant; ring
  have hhi : x<q+2 := by
    apply lt_of_mul_self_lt_mul_self₀ (by simp)
    calc
      x*x<x*x+(q+1) := by simp
      _=(q+2)*(q+2) := by rw [h]; unfold discriminant; ring
  have hge : q+2≤x := by simpa [show q+1+1=q+2 by ring] using lt_iff_succ_le.mp hlo
  exact (not_lt_of_ge hge) hhi

theorem norm_advance_iff (q x k : V) :
    ((2*q+3)*x+2*discriminant q*k)*((2*q+3)*x+2*discriminant q*k)=
      1+discriminant q*(2*x+(2*q+3)*k)*(2*x+(2*q+3)*k) ↔
      x*x=1+discriminant q*k*k := by
  simpa only [mul_comm (discriminant q) (2 : V)] using
    ArithmeticPellKnownUnit.advance_iff (discriminant q) (2*q+3) 2 x k (by
      unfold discriminant; ring)

/-- Descent uses the actual unit(2Q+1,2) and proves both inverse
identities over natural arithmetic before descending on the ordinate. -/
theorem descent (q x k : V) (hk : 0<k) (h : x*x=1+discriminant q*k*k) :
    ∃ u v : V, 0<u ∧ v<k ∧ u*u=1+discriminant q*v*v ∧
      x=(2*q+3)*u+2*discriminant q*v ∧ k=2*u+(2*q+3)*v := by
  have hD : 0 < discriminant q := by unfold discriminant; exact mul_pos (by simp) (by simp)
  have hF : (2*q+3)*(2*q+3)=1+discriminant q*2*2 := by
    unfold discriminant
    ring
  obtain ⟨u, v, hu, hv, hn, hx, hy⟩ :=
    ArithmeticPellKnownUnit.minimal_unit_descent (discriminant q) (2*q+3) 2 x k
      hD (lt_of_lt_of_le (by norm_num : (1:V)<3) (by simp)) (by norm_num) hF
      (fun x k hk h => two_le_ordinate q x k hk h) hk h
  refine ⟨u, v, hu, hv, hn, ?_, hy⟩
  simpa only [mul_comm (discriminant q) (2 : V)] using hx

theorem solution_index (q x k : V) (h : x*x=1+discriminant q*k*k) :
    ∃ time : V, time≤k ∧ xcoord time (2*q+1)=x ∧ 2*ycoord time (2*q+1)=k := by
  have bounded (k : V) : ∀ x≤(q+2)*k+1, x*x=1+discriminant q*k*k →
      ∃ time : V, time≤k ∧ xcoord time (2*q+1)=x ∧ 2*ycoord time (2*q+1)=k := by
    induction k using ISigma1.sigma1_order_induction
    · unfold discriminant
      definability
    case ind k ih =>
      intro x hx hn
      by_cases hk : k=0
      · subst k
        have hx1 : x=1 := le_antisymm (by simpa using hx)
          (by simpa using lt_iff_succ_le.mp (positive_x q x 0 hn))
        subst x
        exact ⟨0,le_refl _,by simp,by simp⟩
      · have hkp : 0<k := pos_iff_ne_zero.mpr hk
        obtain ⟨u,v,_,hv,hu,hix,hik⟩ := descent q x k hkp hn
        obtain ⟨time,ht,hxu,hyv⟩ := ih v hv u (x_bound q u v hu) hu
        refine ⟨time+1,lt_iff_succ_le.mp (lt_of_le_of_lt ht hv),?_,?_⟩
        · rw [x_succ,hxu,hix,←hyv]
          unfold delta discriminant
          ring
        · rw [y_succ,hxu,hik,←hyv]
          ring
  exact bounded k x (x_bound q x k h) h

theorem norm_iff_index (q x k : V) :
    x*x=1+discriminant q*k*k ↔
      ∃ time : V, time≤k ∧ xcoord time (2*q+1)=x ∧ 2*ycoord time (2*q+1)=k := by
  constructor
  · exact solution_index q x k
  · rintro ⟨time,_,rfl,rfl⟩
    have h := norm time (2*q+1)
    calc
      xcoord time (2*q+1)*xcoord time (2*q+1)=
          1+delta (2*q+1)*ycoord time (2*q+1)*ycoord time (2*q+1) := h
      _=1+discriminant q*(2*ycoord time (2*q+1))*(2*ycoord time (2*q+1)) := by
        unfold delta discriminant
        ring

theorem even_ordinate (q x k : V) (h : x*x=1+discriminant q*k*k) :
    ∃ y : V, k=2*y := by
  obtain ⟨time,_,_,hy⟩ := solution_index q x k h
  exact ⟨ycoord time (2*q+1),hy.symm⟩

theorem positive_solution_index (q x k : V) (hk : 0<k)
    (h : x*x=1+discriminant q*k*k) :
    ∃ time : V, 0<time ∧ time≤k ∧ xcoord time (2*q+1)=x ∧ 2*ycoord time (2*q+1)=k := by
  obtain ⟨time,ht,hx,hy⟩ := solution_index q x k h
  have hp : 0<time := pos_iff_ne_zero.mpr (fun ht0 => (ne_of_gt hk) (by simpa [ht0] using hy.symm))
  exact ⟨time,hp,ht,hx,hy⟩

/-- The literal first-norm parameter Q is arbitrary positive internal data.
The subtraction Q-1 is used only after proving its required bound. -/
theorem positive_parameter_solution (Q x k : V) (hQ : 0<Q)
    (h : x*x=1+Q*(Q+1)*k*k) :
    ∃ time : V, time≤k ∧ xcoord time (2*(Q-1)+1)=x ∧
      2*ycoord time (2*(Q-1)+1)=k := by
  have hQ1 : 1≤Q := by simpa using lt_iff_succ_le.mp hQ
  have he : Q-1+1=Q := tsub_add_cancel_of_le hQ1
  apply solution_index (Q-1) x k
  have hd : discriminant (Q-1)=Q*(Q+1) := by
    unfold discriminant
    rw [show Q-1+2=(Q-1+1)+1 by ring,he]
  rwa [hd]

/-- Classification also proves evenness and the actual first-carrier
residue quotients, rather than assuming the doubled ordinate beforehand. -/
theorem solution_residues (q x k : V) (h : x*x=1+discriminant q*k*k) :
    ∃ time r s : V, time≤k ∧ xcoord time (2*q+1)=x ∧ 2*ycoord time (2*q+1)=k ∧
      x=1+2*(q+1)*r ∧ k=2*time+4*(q+1)*s := by
  obtain ⟨time,ht,hx,hk⟩ := solution_index q x k h
  have hm : 2*(q+1)∣(2*q+1)+1 := ⟨1,by ring⟩
  obtain ⟨r,s,hr,hs⟩ := residue_quotients time (2*q+1) (2*(q+1)) hm
  refine ⟨time,r,s,ht,hx,hk,by rwa [hx] at hr,?_⟩
  rw [←hk,hs]
  ring

end DiophantineConsistency.ArithmeticPellFirstNorm
