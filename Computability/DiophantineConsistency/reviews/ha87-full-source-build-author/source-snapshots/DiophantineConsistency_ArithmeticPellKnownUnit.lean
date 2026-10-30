import DiophantineConsistency.ArithmeticPellClassification

/-! Classify an arbitrary positive discriminant from one known positive unit.
The bounded least-ordinate search is derived in the internal model. Descent
then uses Sigma1 order induction at internal ordinates, retaining the scale
of the least unit. No unbounded Pell existence or external classification
oracle is used. The later common-discriminant/integrality steps are separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellKnownUnit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem norm_x_bound (D x y : V) (h : x*x=1+D*y*y) :
    x≤(D+1)*y+1 := by
  apply nonneg_le_nonneg_of_sq_le_sq (Arithmetic.zero_le _)
  calc
    x*x=1+D*y*y := h
    _≤(1+D*y*y)+((D*D+D+1)*y*y+2*(D+1)*y) := by simp
    _=((D+1)*y+1)*((D+1)*y+1) := by ring

/-- The seed supplies a bounded nonempty search. The resulting ordinate is
least among all positive solutions, including solutions outside the box. -/
theorem least_unit (D A S : V) (hD : 0<D) (_hA : 1<A) (hS : 0<S)
    (hseed : A*A=1+D*S*S) :
    ∃ F v : V, 1<F ∧ 0<v ∧ F≤A ∧ v≤S ∧ F*F=1+D*v*v ∧
      ∀ x y : V, 0<y → x*x=1+D*y*y → v≤y := by
  let P : V → Prop := fun y => 0<y ∧ y≤S ∧ ∃ x≤A, x*x=1+D*y*y
  have hP : 𝚺₀-Predicate P := by dsimp [P]; definability
  obtain ⟨v,hv,hmin⟩ := ISigma0.least_number hP
    (show P S from ⟨hS,le_rfl,A,le_rfl,hseed⟩)
  obtain ⟨hvpos,hvS,F,hFA,hF⟩ := hv
  have hFp : 1<F := by
    apply lt_of_mul_self_lt_mul_self₀ (by simp)
    simpa only [one_mul] using
      (show (1:V)<F*F by rw [hF]; exact lt_add_of_pos_right _ (mul_pos (mul_pos hD hvpos) hvpos))
  refine ⟨F,v,hFp,hvpos,hFA,hvS,hF,?_⟩
  intro x y hy hn
  by_contra hnot
  have hyv : y<v := lt_of_not_ge hnot
  have hyS : y≤S := le_trans (le_of_lt hyv) hvS
  have hxA : x≤A := by
    apply nonneg_le_nonneg_of_sq_le_sq (Arithmetic.zero_le _)
    rw [hn,hseed]
    simpa only [mul_assoc,add_comm] using _root_.add_le_add_left (mul_le_mul_of_nonneg_left
      (mul_self_le_mul_self (by simp) hyS) (Arithmetic.zero_le D)) 1
  exact hmin y hyv ⟨hy,hyS,x,hxA,hn⟩

theorem advance_iff (D F v x y : V) (hF : F*F=1+D*v*v) :
    (F*x+D*v*y)*(F*x+D*v*y)=1+D*(v*x+F*y)*(v*x+F*y) ↔
      x*x=1+D*y*y := by
  let common := D*v*v*x*x+2*F*D*v*x*y+D*D*v*v*y*y
  have hl : (F*x+D*v*y)*(F*x+D*v*y)=x*x+common := by
    calc
      _=(F*F)*(x*x)+2*F*D*v*x*y+D*D*v*v*y*y := by ring
      _=x*x+common := by rw [hF]; dsimp [common]; ring
  have hr : 1+D*(v*x+F*y)*(v*x+F*y)=(1+D*y*y)+common := by
    calc
      _=1+D*v*v*x*x+2*F*D*v*x*y+D*(F*F)*y*y := by ring
      _=(1+D*y*y)+common := by rw [hF]; dsimp [common]; ring
  rw [hl,hr]
  exact add_right_cancel_iff

/-- Natural subtractions are justified by the norm identities and minimality.
Only the stated least-ordinate property is used by this helper. -/
theorem minimal_unit_descent (D F v x y : V)
    (_hD : 0<D) (hFpos : 1<F) (hvpos : 0<v) (hF : F*F=1+D*v*v)
    (hmin : ∀ x y : V, 0<y → x*x=1+D*y*y → v≤y)
    (hy : 0<y) (hn : x*x=1+D*y*y) :
    ∃ u z : V, 0<u ∧ z<y ∧ u*u=1+D*z*z ∧
      x=F*u+D*v*z ∧ y=v*u+F*z := by
  have hFy : v*x≤F*y := by
    apply nonneg_le_nonneg_of_sq_le_sq (Arithmetic.zero_le _)
    apply (add_le_add_iff_right (y*y)).mp
    calc
      (v*x)*(v*x)+y*y=(F*y)*(F*y)+v*v := by
        calc
          _=(v*v)*(x*x)+y*y := by ring
          _=(F*F)*(y*y)+v*v := by rw [hn,hF]; ring
          _=_ := by ring
      _≤(F*y)*(F*y)+y*y := by
        simpa only [add_comm] using _root_.add_le_add_left
          (mul_self_le_mul_self (by simp) (hmin x y hy hn)) ((F*y)*(F*y))
  have hFx : D*v*y<F*x := by
    apply lt_of_mul_self_lt_mul_self₀ (by simp)
    have hid : (F*x)*(F*x)=(D*v*y)*(D*v*y)+(F*F+D*y*y) := by
      calc
        _=(F*F)*(x*x) := by ring
        _=_ := by rw [hn,hF]; ring
    rw [hid]
    exact lt_add_of_pos_right _ (lt_of_lt_of_le
      (mul_pos (lt_trans (by simp) hFpos) (lt_trans (by simp) hFpos)) (by simp))
  let e := F-1
  have he : e+1=F := tsub_add_cancel_of_le (le_of_lt hFpos)
  have hd : D*v*v=e*e+2*e := by
    apply add_left_cancel (a := (1:V))
    rw [←hF,←he]
    ring
  have hlow : e*y<v*x := by
    apply lt_of_mul_self_lt_mul_self₀ (by simp)
    have hid : (v*x)*(v*x)=(e*y)*(e*y)+(v*v+2*e*y*y) := by
      calc
        _=v*v*(x*x) := by ring
        _=v*v+(D*v*v)*y*y := by rw [hn]; ring
        _=_ := by rw [hd]; ring
    rw [hid]
    exact lt_add_of_pos_right _ (lt_of_lt_of_le (mul_pos hvpos hvpos) (by simp))
  let u := F*x-D*v*y
  let z := F*y-v*x
  have hu : 0<u := tsub_pos_iff_lt.mpr hFx
  have hux : u+D*v*y=F*x := tsub_add_cancel_of_le (le_of_lt hFx)
  have hzy : z+v*x=F*y := tsub_add_cancel_of_le hFy
  have hz : z<y := by
    have hh : e*y+z<e*y+y := by
      calc
        e*y+z<v*x+z := by simpa only [add_comm] using _root_.add_lt_add_right hlow z
        _=F*y := by rw [add_comm (v*x) z,hzy]
        _=e*y+y := by rw [←he]; ring
    simpa only [add_lt_add_iff_left] using hh
  have hix : F*u+D*v*z=x := by
    apply add_right_cancel (b := F*D*v*y+D*v*v*x)
    calc
      _=F*(u+D*v*y)+D*v*(z+v*x) := by ring
      _=F*(F*x)+D*v*(F*y) := by rw [hux,hzy]
      _=(F*F)*x+F*D*v*y := by ring
      _=x+(F*D*v*y+D*v*v*x) := by rw [hF]; ring
  have hiy : v*u+F*z=y := by
    apply add_right_cancel (b := D*v*v*y+F*v*x)
    calc
      _=v*(u+D*v*y)+F*(z+v*x) := by ring
      _=v*(F*x)+F*(F*y) := by rw [hux,hzy]
      _=F*v*x+(F*F)*y := by ring
      _=y+(D*v*v*y+F*v*x) := by rw [hF]; ring
  have hun : u*u=1+D*z*z := (advance_iff D F v u z hF).mp (by simpa only [hix,hiy] using hn)
  exact ⟨u,z,hu,hz,hun,hix.symm,hiy.symm⟩

/-- The bounded-universal invariant is Sigma1, including its internal index. -/
theorem minimal_unit_classification (D b v : V)
    (hD : 0<D) (hv : 0<v) (hF : (b+2)*(b+2)=1+D*v*v)
    (hmin : ∀ x y : V, 0<y → x*x=1+D*y*y → v≤y) :
    ∀ x y : V, x*x=1+D*y*y →
      ∃ n : V, n≤y ∧ x=xcoord n b ∧ y=v*ycoord n b := by
  have hd : delta b=D*v*v := by
    apply add_left_cancel (a := (1:V))
    calc
      1+delta b=(b+2)*(b+2) := by unfold delta; ring
      _=1+D*v*v := hF
  have bounded (y : V) : ∀ x≤(D+1)*y+1, x*x=1+D*y*y →
      ∃ n : V, n≤y ∧ x=xcoord n b ∧ y=v*ycoord n b := by
    induction y using ISigma1.sigma1_order_induction
    · definability
    case ind y ih =>
      intro x hx hn
      by_cases hy : y=0
      · subst y
        have hx1 : x=1 := by
          apply le_antisymm (by simpa using hx)
          have hxpos : 0<x := pos_of_mul_pos_left (by rw [hn]; simp) (by simp)
          simpa using lt_iff_succ_le.mp hxpos
        exact ⟨0,by simp,by simpa using hx1,by simp⟩
      · have hyp : 0<y := pos_iff_ne_zero.mpr hy
        have hbase : 1<b+2 := lt_of_lt_of_le (by simp : (1:V)<2) (by simp)
        obtain ⟨u,z,_,hz,hu,hix,hiy⟩ :=
          minimal_unit_descent D (b+2) v x y hD hbase hv hF hmin hyp hn
        obtain ⟨n,hnz,hux,hzy⟩ := ih z hz u (norm_x_bound D u z hu) hu
        refine ⟨n+1,lt_iff_succ_le.mp (lt_of_le_of_lt hnz hz),?_,?_⟩
        · rw [x_succ,hd,←hux,hix,hzy]
          ring
        · rw [y_succ,←hux,hiy,hzy]
          ring
  intro x y hn
  exact bounded y x (norm_x_bound D x y hn) hn

/-- A known unit supplies the finite minimum; no least-unit or index premise.
All solutions, including ordinate zero, use the same derived base and scale. -/
theorem known_unit_classification (D A S : V)
    (hD : 0<D) (hA : 1<A) (hS : 0<S) (hseed : A*A=1+D*S*S) :
    ∃ b v : V, 0<v ∧ b+2≤A ∧ v≤S ∧
      (b+2)*(b+2)=1+D*v*v ∧
      ∀ x y : V, x*x=1+D*y*y →
        ∃ n : V, n≤y ∧ x=xcoord n b ∧ y=v*ycoord n b := by
  obtain ⟨F,v,hFp,hvp,hFA,hvS,hF,hmin⟩ := least_unit D A S hD hA hS hseed
  have h2 : (2:V)≤F := by simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp hFp
  let b := F-2
  have hb : b+2=F := tsub_add_cancel_of_le h2
  refine ⟨b,v,hvp,?_,hvS,?_,?_⟩
  · simpa only [hb] using hFA
  · simpa only [hb] using hF
  · exact minimal_unit_classification D b v hD hvp (by simpa only [hb] using hF) hmin
end DiophantineConsistency.ArithmeticPellKnownUnit
