import DiophantineConsistency.AdaptiveGap85FirstStrongBinding
import DiophantineConsistency.AdaptiveGap85StrongSeed

/-! The artificial first/strong family has a nonunit main factor. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace DiophantineConsistency.AdaptiveGap85StrongOrientedMain
open AdaptiveGap85Literal AdaptiveGap85Factors AdaptiveGap85WeakFamily AdaptiveGap85FamilyBinding AdaptiveGap85FirstStrongBinding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85StrongSeed ArithmeticPellRecurrence

/-- The main factor does not depend on the chosen strong Pell seed. -/
theorem main_factor_value (f i : ℤ) :
    ((factors (ports 1 1 1 0)).2.1).eval (witnessStrong 1 1 0 1 f i)=47261953 := by
  norm_num [factors,Expr.eval,ports,witnessStrong]
  change (47261953:ℤ)=47261953
  rfl
/-- Every witness in this artificial family has nonzero full polynomial. -/
theorem full_polynomial_ne_zero (f i : ℤ) :
    (expressionAt85 (ports 1 1 1 0)).eval (witnessStrong 1 1 0 1 f i) ≠ 0 := by
  intro hz
  rw [expression_factors] at hz
  change ((factors (ports 1 1 1 0)).2.2.2).eval (witnessStrong 1 1 0 1 f i) *
      (((factors (ports 1 1 1 0)).2.2.1).eval (witnessStrong 1 1 0 1 f i) *
        (((factors (ports 1 1 1 0)).1).eval (witnessStrong 1 1 0 1 f i) *
          ((factors (ports 1 1 1 0)).2.1).eval (witnessStrong 1 1 0 1 f i))) - 1 = 0 at hz
  rw [main_factor_value] at hz
  have hd : (47261953:ℤ) ∣ 1 := by
    refine ⟨((factors (ports 1 1 1 0)).2.2.2).eval (witnessStrong 1 1 0 1 f i) *
      (((factors (ports 1 1 1 0)).2.2.1).eval (witnessStrong 1 1 0 1 f i) *
        ((factors (ports 1 1 1 0)).1).eval (witnessStrong 1 1 0 1 f i)),?_⟩
    calc
      (1:ℤ)=((factors (ports 1 1 1 0)).2.2.2).eval (witnessStrong 1 1 0 1 f i) *
        (((factors (ports 1 1 1 0)).2.2.1).eval (witnessStrong 1 1 0 1 f i) *
          (((factors (ports 1 1 1 0)).1).eval (witnessStrong 1 1 0 1 f i) * 47261953)) := by linarith
      _=47261953*(((factors (ports 1 1 1 0)).2.2.2).eval (witnessStrong 1 1 0 1 f i) *
        (((factors (ports 1 1 1 0)).2.2.1).eval (witnessStrong 1 1 0 1 f i) *
          ((factors (ports 1 1 1 0)).1).eval (witnessStrong 1 1 0 1 f i))) := by ring
  norm_num at hd

def rank (w : Fin 13 → ℤ) : ℤ :=
  let q := 1+w 0
  ((q-w 1)*q-w 2)*(q^2-1)+w 0

/-- The first and strong units plus a positive exact small rank do not force
F+C<q for arbitrary ports. No main/auxiliary unit or full zero is claimed. -/
theorem strong_oriented_nonzero_example :
    ∃ w : Fin 13 → ℤ, (∀ j,0<w j) ∧
      ((factors (ports 1 1 1 0)).1).eval w=1 ∧
      ((factors (ports 1 1 1 0)).2.2.2).eval w=1 ∧
      w 0=1 ∧ w 1=1 ∧ w 2=2 ∧ w 6=1 ∧ w 7=8 ∧ w 9=1 ∧ w 10=1 ∧
      rank w=1 ∧ rank w+1=2*1 ∧ rank w+2*1<(1+w 0)^4 ∧
      ¬(w 1+w 2<1+w 0) ∧
      (expressionAt85 (ports 1 1 1 0)).eval w ≠ 0 := by
  obtain ⟨f,i,hf,hi,hs⟩ := strong_seed_at_successor (V:=ℕ) 16
  have hs' : (17*17*i)*(17*17*i)+323=323*(f*f) := by simpa [delta] using hs
  have hstrong : let Y : ℤ := (1+1)^3
      let c := 1+2*Y
      let Delta := (2*Y+1)*(2*Y+3)
      (c*c*(i:ℤ))*(c*c*(i:ℤ))+Delta=Delta*((f:ℤ)*(f:ℤ)) := by
    dsimp
    exact_mod_cast hs'
  have hfac := first_and_strong_actual 1 1 0 1 (f:ℤ) (i:ℤ) 1 0 (by norm_num) hstrong
  let w := witnessStrong 1 1 0 1 (f:ℤ) (i:ℤ)
  refine ⟨w,?_,hfac.1,hfac.2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j
    fin_cases j <;> simp [w,witnessStrong] <;> first | exact_mod_cast hf | exact_mod_cast hi
  all_goals first | exact full_polynomial_ne_zero (f:ℤ) (i:ℤ) | rfl | norm_num [w,witnessStrong,rank]
end DiophantineConsistency.AdaptiveGap85StrongOrientedMain
