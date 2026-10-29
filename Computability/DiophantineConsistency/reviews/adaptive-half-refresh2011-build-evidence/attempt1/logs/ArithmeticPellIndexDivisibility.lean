import DiophantineConsistency.ArithmeticPellIntegralSolution

/-! Exact natural quotient certificates finish the ordinate-to-index step.
All indices are internal to the IΣ1 model. No cubic congruence, power
cancellation, supplied coprimality or desired divisibility is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellIndexDivisibility
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticGcdNormalization
open ArithmeticPellCommonUnit ArithmeticPellIntegralSolution
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Successor swaps these two exact nonnegative quotient shapes. The
statement needs no separately represented parity predicate. -/
theorem quotient_alternatives (a j : V) :
    (∃ u v : V, xcoord j a=1+delta a*u ∧
      ycoord j a=(a+2)*j+delta a*v) ∨
    (∃ u v : V, xcoord j a=a+2+delta a*u ∧
      ycoord j a=j+delta a*v) := by
  induction j using ISigma1.sigma1_succ_induction
  · unfold delta
    definability
  case zero => exact Or.inl ⟨0,0,by simp,by simp⟩
  case succ j ih =>
    rcases ih with ⟨u,v,hx,hy⟩|⟨u,v,hx,hy⟩
    · refine Or.inr ⟨(a+2)*u+(a+2)*j+delta a*v,u+j+(a+2)*v,?_,?_⟩
      all_goals
        simp only [x_succ, y_succ, hx, hy, delta]
        ring
    · refine Or.inl ⟨1+(a+2)*u+j+delta a*v,u+(a+2)*v,?_,?_⟩
      all_goals
        simp only [x_succ, y_succ, hx, hy, delta]
        ring

/-- An actual natural Bezout certificate at every index, including zero. -/
theorem index_certificate (a j : V) : Bez (ycoord j a) (delta a) j := by
  rcases quotient_alternatives a j with ⟨_,v,_,hy⟩|⟨_,v,_,hy⟩
  · refine ⟨0,j+(a+2)*v,a+2,0,?_⟩
    rw [hy]
    unfold delta
    ring
  · exact ⟨0,v,1,0,by rw [hy]; ring⟩

/-- The scale is absorbed into the second coefficients, so it may be zero. -/
theorem certificate_scale_left {x y g : V} (h : Bez x y g) (s : V) :
    Bez (s*x) y (s*g) := by
  obtain ⟨u,v,w,z,he⟩ := h
  refine ⟨u,s*v,w,s*z,?_⟩
  calc
    s*g+(s*x)*u+y*(s*v)=s*(g+x*u+y*v) := by ring
    _=s*(x*w+y*z) := by rw [he]
    _=(s*x)*w+y*(s*z) := by ring

/-- The scale is absorbed into the first coefficients, without cancellation. -/
theorem certificate_scale_right {x y g : V} (h : Bez x y g) (s : V) :
    Bez x (s*y) (s*g) := by
  obtain ⟨u,v,w,z,he⟩ := h
  refine ⟨s*u,v,s*w,z,?_⟩
  calc
    s*g+x*(s*u)+(s*y)*v=s*(g+x*u+y*v) := by ring
    _=s*(x*w+y*z) := by rw [he]
    _=x*(s*w)+(s*y)*z := by ring

/-- Both zero indices are included. The shifted base is constructed only
in the positive-p branch, after proving its subtraction is justified. -/
theorem ordinate_divides_index (a p m : V) (hpm : p∣m)
    (hdiv : ycoord p a*ycoord p a∣delta a*ycoord m a) :
    ycoord p a∣m := by
  by_cases hp0 : p=0
  · have hm : m=0 := by simpa [hp0] using hpm
    simp [hp0,hm]
  have hp : 0<p := pos_iff_ne_zero.mpr hp0
  let c := ycoord p a
  let F := xcoord p a
  have hc : 0<c := lt_of_lt_of_le hp (time_le_y p a)
  have hc1 : 1≤c := pos_iff_one_le.mp hc
  have hF1 : 1<F := lt_of_le_of_lt hc1 (y_lt_x a p)
  have hF2 : 2≤F := by simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp hF1
  let B := F-2
  have hBF : B+2=F := tsub_add_cancel_of_le hF2
  have hdB : delta B=delta a*c*c := by
    apply add_left_cancel (a := (1:V))
    calc
      1+delta B=(B+2)*(B+2) := by unfold delta; ring
      _=F*F := by rw [hBF]
      _=1+delta a*c*c := norm p a
  have hcomp := composition B a p hBF
  obtain ⟨k,hk⟩ := hpm
  have hym : ycoord m a=ycoord k B*c := by
    rw [hk,←(hcomp k).2]
  obtain ⟨v,hv⟩ := hdiv
  change delta a*ycoord m a=(c*c)*v at hv
  have hcancel : delta a*ycoord k B=c*v := by
    apply mul_left_cancel₀ (ne_of_gt hc)
    calc
      c*(delta a*ycoord k B)=delta a*ycoord m a := by rw [hym]; ring
      _=(c*c)*v := hv
      _=c*(c*v) := by ring
  have hcY : c∣delta a*ycoord k B := ⟨v,hcancel⟩
  have hcB : c∣delta B := ⟨delta a*c,by rw [hdB]; ring⟩
  have hcDk : c∣delta a*k :=
    bez_divisor (certificate_scale_left (index_certificate B k) (delta a)) hcY hcB
  have hcert : Bez c (delta a*k) (p*k) := by
    simpa only [mul_comm] using certificate_scale_right (index_certificate a p) k
  have hlast : c∣p*k := bez_divisor hcert (dvd_refl c) hcDk
  simpa only [hk] using hlast

/-- The same actual m returned by IntegralSolution receives both divisibilities. -/
theorem relaxed_auxiliary (a c p i f : V)
    (hp : 0<p) (hi : 0<i) (hf : 0<f) (hcp : c=ycoord p a)
    (hnorm : (i*c*c)*(i*c*c)+delta a=delta a*(f*f))
    (hbig : (a+2)*delta a*delta a<c) :
    ∃ m : V, 0<m ∧ f=xcoord m a ∧ p∣m ∧ c∣m ∧
      i*c*c=delta a*ycoord m a := by
  obtain ⟨m,hm,hpm,hf',hr⟩ := integral_solution a c p i f hp hi hf hcp hnorm hbig
  have hdiv : c*c∣delta a*ycoord m a := ⟨i,by rw [←hr]; ring⟩
  have hcm : c∣m := by
    rw [hcp] at hdiv ⊢
    exact ordinate_divides_index a p m hpm hdiv
  exact ⟨m,hm,hf',hpm,hcm,hr⟩

/-- The existing positive-f adapter supplies the same actual truncated input. -/
theorem relaxed_auxiliary_tsub (a c p i f : V)
    (hp : 0<p) (hi : 0<i) (hf : 0<f) (hcp : c=ycoord p a)
    (hnorm : (i*c*c)*(i*c*c)=delta a*(f*f-1))
    (hbig : (a+2)*delta a*delta a<c) :
    ∃ m : V, 0<m ∧ f=xcoord m a ∧ p∣m ∧ c∣m ∧
      i*c*c=delta a*ycoord m a := by
  exact relaxed_auxiliary a c p i f hp hi hf hcp
    (norm_tsub_to_add (delta a) f (i*c*c) hf hnorm) hbig
end DiophantineConsistency.ArithmeticPellIndexDivisibility
