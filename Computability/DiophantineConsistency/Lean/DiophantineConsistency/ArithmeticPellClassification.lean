import DiophantineConsistency.ArithmeticPellRecurrence

/-! Descent and complete solution classification for the represented Pell
sequence, uniformly in every IΣ1 model. The index is internal and bounded
by the solution's ordinate. Carrier congruences are separate obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellClassification
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_x (b x y : V) (h : x*x=1+delta b*y*y) : 0<x := by
  exact pos_of_mul_pos_left (b := x) (by rw [h]; simp) (Arithmetic.zero_le x)

/-- The bound makes the later induction invariant a bounded universal. -/
theorem x_bound (b x y : V) (h : x*x=1+delta b*y*y) : x≤(b+2)*y+1 := by
  apply nonneg_le_nonneg_of_sq_le_sq (Arithmetic.zero_le _)
  calc
    x*x=1+delta b*y*y := h
    _≤(1+delta b*y*y)+(y*y+2*(b+2)*y) := by simp
    _=((b+2)*y+1)*((b+2)*y+1) := by unfold delta; ring

theorem norm_advance_iff (b x y : V) :
    ((b+2)*x+delta b*y)*((b+2)*x+delta b*y)=
      1+delta b*(x+(b+2)*y)*(x+(b+2)*y) ↔ x*x=1+delta b*y*y := by
  constructor
  · intro h
    have he := norm_advance_balance b x y
    rw [h] at he
    exact (add_left_cancel he).symm
  · exact norm_step b x y

/-- Every positive-ordinate solution has a strictly smaller solution and
is exactly its forward recurrence step. Natural subtraction is justified. -/
theorem descent (b x y : V) (hy : 0<y) (h : x*x=1+delta b*y*y) :
    ∃ u v : V, 0<u ∧ v<y ∧ u*u=1+delta b*v*v ∧
      x=(b+2)*u+delta b*v ∧ y=u+(b+2)*v := by
  let a := b+2
  let d := delta b
  have ha : 0<a := lt_of_lt_of_le (by simp : (0:V)<1) (base_ge_one b)
  have hid : (a*x)*(a*x)=(d*y)*(d*y)+(a*a+d*y*y) := by
    rw [show (a*x)*(a*x)=a*a*(x*x) by ring,h]
    dsimp [a,d,delta]
    ring
  have hdy : d*y<a*x := by
    apply lt_of_mul_self_lt_mul_self₀ (by simp)
    rw [hid]
    exact lt_add_of_pos_right _ (lt_of_lt_of_le (mul_pos ha ha) (by simp))
  have hxle : x≤a*y := by
    apply nonneg_le_nonneg_of_sq_le_sq (Arithmetic.zero_le _)
    calc
      x*x=1+d*y*y := h
      _≤y*y+d*y*y := by
        simpa only [add_comm] using
          _root_.add_le_add_right (one_le_mul (pos_iff_one_le.mp hy) (pos_iff_one_le.mp hy)) (d*y*y)
      _=(a*y)*(a*y) := by dsimp [a,d,delta]; ring
  have hxlow : (b+1)*y<x := by
    apply lt_of_mul_self_lt_mul_self₀ (by simp)
    have hi : x*x=((b+1)*y)*((b+1)*y)+(1+2*(b+1)*y*y) := by
      rw [h]
      unfold delta
      ring
    rw [hi]
    exact lt_add_of_pos_right _ (by simp)
  let u := a*x-d*y
  let v := a*y-x
  have hu : 0<u := tsub_pos_iff_lt.mpr hdy
  have hux : u+d*y=a*x := tsub_add_cancel_of_le (le_of_lt hdy)
  have hvy : v+x=a*y := tsub_add_cancel_of_le hxle
  have hv : v<y := by
    have he := _root_.add_lt_add_left hxlow v
    have he' : (b+1)*y+v<(b+1)*y+y := by
      calc
        (b+1)*y+v<x+v := he
        _=a*y := by rw [add_comm x v,hvy]
        _=(b+1)*y+y := by dsimp [a]; ring
    simpa only [add_lt_add_iff_left] using he'
  have hix : a*u+d*v=x := by
    apply add_right_cancel (b := a*d*y+d*x)
    calc
      (a*u+d*v)+(a*d*y+d*x)=a*(u+d*y)+d*(v+x) := by ring
      _=a*(a*x)+d*(a*y) := by rw [hux,hvy]
      _=x+(a*d*y+d*x) := by dsimp [a,d,delta]; ring
  have hiy : u+a*v=y := by
    apply add_right_cancel (b := d*y+a*x)
    calc
      (u+a*v)+(d*y+a*x)=(u+d*y)+a*(v+x) := by ring
      _=a*x+a*(a*y) := by rw [hux,hvy]
      _=y+(d*y+a*x) := by dsimp [a,d,delta]; ring
  have hn : u*u=1+delta b*v*v := by
    apply (norm_advance_iff b u v).mp
    change (a*u+d*v)*(a*u+d*v)=1+d*(u+a*v)*(u+a*v)
    rw [hix,hiy]
    exact h
  exact ⟨u,v,hu,hv,hn,hix.symm,hiy.symm⟩

/-- Bounded-universal Sigma1 induction, not an unbounded predicate oracle. -/
theorem solution_index (b x y : V) (h : x*x=1+delta b*y*y) :
    ∃ time : V, time≤y ∧ xcoord time b=x ∧ ycoord time b=y := by
  have bounded (y : V) : ∀ x≤(b+2)*y+1, x*x=1+delta b*y*y →
      ∃ time : V, time≤y ∧ xcoord time b=x ∧ ycoord time b=y := by
    induction y using ISigma1.sigma1_order_induction
    · unfold delta
      definability
    case ind y ih =>
      intro x hx hn
      by_cases hy : y=0
      · subst y
        have hx1 : x=1 := le_antisymm (by simpa using hx)
          (pos_iff_one_le.mp (positive_x b x 0 hn))
        subst x
        exact ⟨0,le_refl _,by simp,by simp⟩
      · have hyp : 0<y := pos_iff_ne_zero.mpr hy
        obtain ⟨u,v,_,hv,hu,hix,hiy⟩ := descent b x y hyp hn
        obtain ⟨time,ht,hxv,hyv⟩ := ih v hv u (x_bound b u v hu) hu
        refine ⟨time+1,lt_iff_succ_le.mp (lt_of_le_of_lt ht hv),?_,?_⟩
        · rw [x_succ,hxv,hyv]
          exact hix.symm
        · rw [y_succ,hxv,hyv]
          exact hiy.symm
  exact bounded y x (x_bound b x y h) h

theorem norm_iff_index (b x y : V) :
    x*x=1+delta b*y*y ↔
      ∃ time : V, time≤y ∧ xcoord time b=x ∧ ycoord time b=y := by
  constructor
  · exact solution_index b x y
  · rintro ⟨time,_,rfl,rfl⟩
    exact norm time b

end DiophantineConsistency.ArithmeticPellClassification
