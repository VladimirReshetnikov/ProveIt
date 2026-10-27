import DiophantineConsistency.ArithmeticPellCongruences

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

private theorem square_le (x z : V) (h : x*x≤z*z) : x≤z := by
  by_contra hn
  exact (not_lt_of_ge h) (mul_self_lt_mul_self (by simp) (lt_of_not_ge hn))

theorem positive_x (q x k : V) (h : x*x=1+discriminant q*k*k) : 0<x := by
  have h1 : 1≤x*x := by rw [h]; simp
  by_contra hn
  have hz : x=0 := le_antisymm (le_of_not_gt hn) (Arithmetic.zero_le x)
  simp [hz] at h1

theorem x_bound (q x k : V) (h : x*x=1+discriminant q*k*k) : x≤(q+2)*k+1 := by
  apply square_le
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
  rcases le_one_iff_eq_zero_or_one.mp hle with hz|ho
  · rw [hz] at hk
    exact (lt_irrefl (0:V)) hk
  · subst k
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
    have hge := lt_iff_succ_le.mp hlo
    rw [show q+1+1=q+2 by ring] at hge
    exact (not_lt_of_ge hge) hhi

theorem norm_advance_iff (q x k : V) :
    ((2*q+3)*x+2*discriminant q*k)*((2*q+3)*x+2*discriminant q*k)=
      1+discriminant q*(2*x+(2*q+3)*k)*(2*x+(2*q+3)*k) ↔
      x*x=1+discriminant q*k*k := by
  let d := discriminant q
  let a := 2*q+3
  let common := 4*d*x*x+4*a*d*x*k+4*d*d*k*k
  have hl : (a*x+2*d*k)*(a*x+2*d*k)=x*x+common := by
    dsimp [a,d,discriminant,common]
    ring
  have hr : 1+d*(2*x+a*k)*(2*x+a*k)=(1+d*k*k)+common := by
    dsimp [a,d,discriminant,common]
    ring
  change (a*x+2*d*k)*(a*x+2*d*k)=1+d*(2*x+a*k)*(2*x+a*k) ↔ x*x=1+d*k*k
  rw [hl,hr]
  exact add_right_cancel_iff

/-- Descent uses the actual unit(2Q+1,2) and proves both inverse
identities over natural arithmetic before descending on the ordinate. -/
theorem descent (q x k : V) (hk : 0<k) (h : x*x=1+discriminant q*k*k) :
    ∃ u v : V, 0<u ∧ v<k ∧ u*u=1+discriminant q*v*v ∧
      x=(2*q+3)*u+2*discriminant q*v ∧ k=2*u+(2*q+3)*v := by
  let a := 2*q+3
  let d := discriminant q
  have ha : 0<a := lt_of_lt_of_le (by simp : (0:V)<3) (by simp : (3:V)≤a)
  have hid : (a*x)*(a*x)=(2*d*k)*(2*d*k)+(a*a+d*k*k) := by
    rw [show (a*x)*(a*x)=a*a*(x*x) by ring,h]
    dsimp [a,d,discriminant]
    ring
  have hdk : 2*d*k<a*x := by
    apply lt_of_mul_self_lt_mul_self₀ (by simp)
    rw [hid]
    exact lt_add_of_pos_right _ (lt_of_lt_of_le (mul_pos ha ha) (by simp))
  have hk2 := two_le_ordinate q x k hk h
  have h4 : 4≤k*k := by
    calc
      4=(2:V)*2 := by ring
      _≤k*k := mul_le_mul hk2 hk2 (by simp) (by simp)
  have hxle : 2*x≤a*k := by
    apply square_le
    calc
      (2*x)*(2*x)=4+4*d*k*k := by
        rw [show (2*x)*(2*x)=4*(x*x) by ring,h]
        ring
      _≤k*k+4*d*k*k := _root_.add_le_add_right h4 _
      _=(a*k)*(a*k) := by dsimp [a,d,discriminant]; ring
  have hxlow : (q+1)*k<x := by
    apply lt_of_mul_self_lt_mul_self₀ (by simp)
    have he : x*x=((q+1)*k)*((q+1)*k)+(1+(q+1)*k*k) := by
      rw [h]
      unfold discriminant
      ring
    rw [he]
    exact lt_add_of_pos_right _ (by simp)
  let u := a*x-2*d*k
  let v := a*k-2*x
  have hu : 0<u := tsub_pos_iff_lt.mpr hdk
  have hux : u+2*d*k=a*x := tsub_add_cancel_of_le (le_of_lt hdk)
  have hvk : v+2*x=a*k := tsub_add_cancel_of_le hxle
  have hv : v<k := by
    have hl : 2*(q+1)*k<2*x := by
      simpa only [mul_assoc] using mul_lt_mul_of_pos_left hxlow (by simp : (0:V)<2)
    have he : 2*(q+1)*k+v<2*(q+1)*k+k := by
      calc
        2*(q+1)*k+v<2*x+v := _root_.add_lt_add_right hl v
        _=a*k := by rw [add_comm (2*x) v,hvk]
        _=2*(q+1)*k+k := by dsimp [a]; ring
    exact (add_lt_add_iff_left _).mp he
  have hix : a*u+2*d*v=x := by
    apply add_right_cancel (b := 2*a*d*k+4*d*x)
    calc
      (a*u+2*d*v)+(2*a*d*k+4*d*x)=a*(u+2*d*k)+2*d*(v+2*x) := by ring
      _=a*(a*x)+2*d*(a*k) := by rw [hux,hvk]
      _=x+(2*a*d*k+4*d*x) := by dsimp [a,d,discriminant]; ring
  have hik : 2*u+a*v=k := by
    apply add_right_cancel (b := 4*d*k+2*a*x)
    calc
      (2*u+a*v)+(4*d*k+2*a*x)=2*(u+2*d*k)+a*(v+2*x) := by ring
      _=2*(a*x)+a*(a*k) := by rw [hux,hvk]
      _=k+(4*d*k+2*a*x) := by dsimp [a,d,discriminant]; ring
  have hn : u*u=1+discriminant q*v*v := by
    apply (norm_advance_iff q u v).mp
    change (a*u+2*d*v)*(a*u+2*d*v)=1+d*(2*u+a*v)*(2*u+a*v)
    rw [hix,hik]
    exact h
  exact ⟨u,v,hu,hv,hn,hix.symm,hik.symm⟩

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
      · have hkp : 0<k := by
          rcases Arithmetic.zero_le k with he|hp
          · exact False.elim (hk he.symm)
          · exact hp
        obtain ⟨u,v,_,hv,hu,hix,hik⟩ := descent q x k hkp hn
        obtain ⟨time,ht,hxu,hyv⟩ := ih v hv u (x_bound q u v hu) hu
        refine ⟨time+1,lt_iff_succ_le.mp (lt_of_le_of_lt ht hv),?_,?_⟩
        · rw [x_succ,hxu]
          calc
            ((2*q+1)+2)*u+delta (2*q+1)*ycoord time (2*q+1)=
                (2*q+3)*u+2*discriminant q*(2*ycoord time (2*q+1)) := by
              unfold delta discriminant
              ring
            _=(2*q+3)*u+2*discriminant q*v := by rw [hyv]
            _=x := hix.symm
        · rw [y_succ,hxu]
          calc
            2*(u+((2*q+1)+2)*ycoord time (2*q+1))=
                2*u+(2*q+3)*(2*ycoord time (2*q+1)) := by ring
            _=2*u+(2*q+3)*v := by rw [hyv]
            _=k := hik.symm
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
  have hp : 0<time := by
    by_contra hn
    have ht0 : time=0 := le_antisymm (le_of_not_gt hn) (Arithmetic.zero_le time)
    have hk0 : k=0 := by simpa [ht0] using hy.symm
    exact (ne_of_gt hk) hk0
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
