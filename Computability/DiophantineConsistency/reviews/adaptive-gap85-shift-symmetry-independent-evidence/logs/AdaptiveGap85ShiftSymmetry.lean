import DiophantineConsistency.AdaptiveGap85Units

/-! A signed algebraic shift preserving all four actual 85 factors. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ShiftSymmetry
open AdaptiveGap85Literal AdaptiveGap85Factors AdaptiveGap85Units

/-- Increase C and compensate in T, r and gamma. The subtraction is integer
subtraction; positivity of the shifted witness is a separate question. -/
def shift (p : Fin 4 → ℤ) (w : Fin 13 → ℤ) : Fin 13 → ℤ :=
  let b := w 0*p 0
  let q := 1+b
  let k := w 9+w 10
  let c := w 9+w 7*k
  let U := w 7*(q*q)
  let H := q*q-1
  let A := w 6+p 1*q
  let d := b*c*U
  ![w 0,w 1,w 2+d,w 3,w 4,w 5-b*U*H,w 6,w 7,w 8+d*A*k+c*U*A,
    w 9,w 10,w 11,w 12+b*c*H]

private theorem first_eval (p : Fin 4 → ℤ) (w : Fin 13 → ℤ) :
    ((AdaptiveGap85Factors.factors p).1).eval w=1+(core p w).A0 := by
  simp [AdaptiveGap85Factors.factors,core,Expr.eval]
private theorem main_eval (p : Fin 4 → ℤ) (w : Fin 13 → ℤ) :
    ((AdaptiveGap85Factors.factors p).2.1).eval w=1+(core p w).A1 := by
  simp [AdaptiveGap85Factors.factors,core,Expr.eval]
private theorem aux_eval (p : Fin 4 → ℤ) (w : Fin 13 → ℤ) :
    ((AdaptiveGap85Factors.factors p).2.2.1).eval w=(core p w).Fa := by
  simp [AdaptiveGap85Factors.factors,core,Expr.eval]
private theorem strong_eval (p : Fin 4 → ℤ) (w : Fin 13 → ℤ) :
    ((AdaptiveGap85Factors.factors p).2.2.2).eval w=(core p w).Fs := by
  simp [AdaptiveGap85Factors.factors,core,Expr.eval]

private theorem shift_root (p : Fin 4 → ℤ) (w : Fin 13 → ℤ) :
    (core p (shift p w)).Z=(core p w).Z := by
  dsimp [core,shift]
  ring
private theorem shift_main (p : Fin 4 → ℤ) (w : Fin 13 → ℤ) :
    (core p (shift p w)).Dstar=(core p w).Dstar := by
  dsimp [core,shift]
  ring
private theorem shift_aux (p : Fin 4 → ℤ) (w : Fin 13 → ℤ) :
    (core p (shift p w)).V=(core p w).V := by
  dsimp [core,shift]
  ring

/-- All four actual factor values are invariant under the integer shift. -/
theorem factors_preserved (p : Fin 4 → ℤ) (w : Fin 13 → ℤ) :
    ((AdaptiveGap85Factors.factors p).1).eval (shift p w)=((AdaptiveGap85Factors.factors p).1).eval w ∧
    ((AdaptiveGap85Factors.factors p).2.1).eval (shift p w)=((AdaptiveGap85Factors.factors p).2.1).eval w ∧
    ((AdaptiveGap85Factors.factors p).2.2.1).eval (shift p w)=((AdaptiveGap85Factors.factors p).2.2.1).eval w ∧
    ((AdaptiveGap85Factors.factors p).2.2.2).eval (shift p w)=((AdaptiveGap85Factors.factors p).2.2.2).eval w := by
  have hM : (core p (shift p w)).M=(core p w).M := by dsimp [core,shift]
  have hell : (core p (shift p w)).ell=(core p w).ell := by dsimp [core,shift]
  have hk : (core p (shift p w)).k=(core p w).k := by dsimp [core,shift]
  have hU : (core p (shift p w)).U=(core p w).U := by dsimp [core,shift]
  have hc : (core p (shift p w)).c=(core p w).c := by dsimp [core,shift]
  have hD : (core p (shift p w)).Delta=(core p w).Delta := by dsimp [core,shift]
  have hI : (core p (shift p w)).I=(core p w).I := by dsimp [core,shift]
  have hf : shift p w 3=w 3 := by dsimp [shift]
  have hy : shift p w 11=w 11 := by dsimp [shift]
  have h0 : (core p (shift p w)).A0=(core p w).A0 := by
    change (core p (shift p w)).Z*(core p (shift p w)).Z -
      ((core p (shift p w)).M*(core p (shift p w)).M)*
        (1+(core p (shift p w)).ell*((core p (shift p w)).ell+(core p (shift p w)).k)) =
      (core p w).Z*(core p w).Z - ((core p w).M*(core p w).M)*
        (1+(core p w).ell*((core p w).ell+(core p w).k))
    rw [shift_root,hM,hell,hk]
  have h1 : (core p (shift p w)).A1=(core p w).A1 := by
    change (core p (shift p w)).Dstar*(core p (shift p w)).Dstar -
      ((core p (shift p w)).U*(core p (shift p w)).U)*
        (1+(core p (shift p w)).Delta*((core p (shift p w)).c*(core p (shift p w)).c)) =
      (core p w).Dstar*(core p w).Dstar - ((core p w).U*(core p w).U)*
        (1+(core p w).Delta*((core p w).c*(core p w).c))
    rw [shift_main,hU,hD,hc]
  have ha : (core p (shift p w)).Fa=(core p w).Fa := by
    change shift p w 11*shift p w 11 - (core p (shift p w)).Delta*(shift p w 3*shift p w 3-1)*
      (shift p w 11*shift p w 11-(core p (shift p w)).V*(core p (shift p w)).V) =
      w 11*w 11 - (core p w).Delta*(w 3*w 3-1)*(w 11*w 11-(core p w).V*(core p w).V)
    rw [shift_aux,hD,hf,hy]
  have hs : (core p (shift p w)).Fs=(core p w).Fs := by
    change 1+((core p (shift p w)).I*(core p (shift p w)).I-
      (core p (shift p w)).Delta*(shift p w 3*shift p w 3-1)) =
      1+((core p w).I*(core p w).I-(core p w).Delta*(w 3*w 3-1))
    rw [hI,hD,hf]
  rw [first_eval,first_eval,main_eval,main_eval,aux_eval,aux_eval,strong_eval,strong_eval,h0,h1,ha,hs]
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- The exact 85 integer polynomial is unchanged, for arbitrary ports and inputs. -/
theorem polynomial_preserved (p : Fin 4 → ℤ) (w : Fin 13 → ℤ) :
    (expressionAt85 p).eval (shift p w)=(expressionAt85 p).eval w := by
  obtain ⟨h0,h1,ha,hs⟩ := factors_preserved p w
  rw [expression_factors]
  change ((AdaptiveGap85Factors.factors p).2.2.2).eval (shift p w) *
    (((AdaptiveGap85Factors.factors p).2.2.1).eval (shift p w) *
      (((AdaptiveGap85Factors.factors p).1).eval (shift p w) *
        ((AdaptiveGap85Factors.factors p).2.1).eval (shift p w))) - 1 =
    ((AdaptiveGap85Factors.factors p).2.2.2).eval w *
    (((AdaptiveGap85Factors.factors p).2.2.1).eval w *
      (((AdaptiveGap85Factors.factors p).1).eval w * ((AdaptiveGap85Factors.factors p).2.1).eval w)) - 1
  rw [h0,h1,ha,hs]

/-- If T exceeds the explicit decrement, the shifted witness remains positive
and violates the positive-gap inequality. -/
theorem shift_positive_and_gap (p : Fin 4 → ℤ) (w : Fin 13 → ℤ)
    (hb : 0<p 0) (hK : 0≤p 1) (hw : ∀j,0<w j)
    (hT : let b := w 0*p 0
      let q := 1+b
      let U := w 7*(q*q)
      b*U*(q*q-1)<w 5) :
    (∀j,0<shift p w j) ∧
      ¬(shift p w 1+shift p w 2<1+shift p w 0*p 0) := by
  let b : ℤ := w 0*p 0
  let q : ℤ := 1+b
  let k : ℤ := w 9+w 10
  let c : ℤ := w 9+w 7*k
  let U : ℤ := w 7*(q*q)
  let H : ℤ := q*q-1
  let A : ℤ := w 6+p 1*q
  have hb' : 0<b := mul_pos (hw 0) hb
  have hq : 0<q := by dsimp [q]; linarith
  have hk : 0<k := add_pos (hw 9) (hw 10)
  have hc : 0<c := add_pos (hw 9) (mul_pos (hw 7) hk)
  have hU : 0<U := mul_pos (hw 7) (mul_pos hq hq)
  have hH : 0<H := by dsimp [H,q]; nlinarith [hb']
  have hA : 0<A := add_pos_of_pos_of_nonneg (hw 6) (mul_nonneg hK (le_of_lt hq))
  change b*U*H<w 5 at hT
  have h2 : 0<w 2+b*c*U := add_pos (hw 2) (mul_pos (mul_pos hb' hc) hU)
  have h5 : 0<w 5-b*U*H := sub_pos.mpr hT
  have h8 : 0<w 8+b*c*U*A*k+c*U*A :=
    add_pos (add_pos (hw 8) (mul_pos (mul_pos (mul_pos (mul_pos hb' hc) hU) hA) hk)) (mul_pos (mul_pos hc hU) hA)
  have h12 : 0<w 12+b*c*H := add_pos (hw 12) (mul_pos (mul_pos hb' hc) hH)
  have hb1 : 1≤b := by omega
  have hc1 : 1≤c := by omega
  have hU1 : 1≤U := by omega
  have hbc : b≤b*c := by nlinarith [hb',hc1]
  have hdelta : b≤b*c*U := by nlinarith [hbc,hb',hc1,hU1]
  constructor
  · intro j
    fin_cases j <;> dsimp [shift] <;>
      first | exact hw 0 | exact hw 1 | exact h2 | exact hw 3 | exact hw 4 |
        exact h5 | exact hw 6 | exact hw 7 | exact h8 | exact hw 9 |
        exact hw 10 | exact hw 11 | exact h12
  · change ¬(w 1+(w 2+b*c*U)<1+b)
    have hf := hw 1
    have hg := hw 2
    omega

/-- Any zero meeting the explicit T bound is sent to a positive zero for which
the reverse gap fails. This theorem does not assert that such a zero exists. -/
theorem shifted_zero_breaks_gap (p : Fin 4 → ℤ) (w : Fin 13 → ℤ)
    (hb : 0<p 0) (hK : 0≤p 1) (hw : ∀j,0<w j)
    (hT : let b := w 0*p 0
      let q := 1+b
      let U := w 7*(q*q)
      b*U*(q*q-1)<w 5)
    (hz : (expressionAt85 p).eval w=0) :
    (∀j,0<shift p w j) ∧ (expressionAt85 p).eval (shift p w)=0 ∧
      ¬(shift p w 1+shift p w 2<1+shift p w 0*p 0) := by
  obtain ⟨hp,hgap⟩ := shift_positive_and_gap p w hb hK hw hT
  exact ⟨hp,(polynomial_preserved p w).trans hz,hgap⟩

end DiophantineConsistency.AdaptiveGap85ShiftSymmetry
