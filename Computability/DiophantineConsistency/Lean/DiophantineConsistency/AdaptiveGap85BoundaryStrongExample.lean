import DiophantineConsistency.AdaptiveGap85Factors
import DiophantineConsistency.AdaptiveGap85StrongSeed

/-! A strict artificial-port example with F=q, C=1 and first/strong units. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85BoundaryStrongExample
open AdaptiveGap85Literal AdaptiveGap85Factors AdaptiveGap85StrongSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence

def ports : Fin 4 → ℤ := ![2,4,0,3]
def witness (f i : ℤ) : Fin 13 → ℤ := ![1,3,1,f,i,1,1,27,8,1,1,1,1]
def rank (w : Fin 13 → ℤ) : ℤ :=
  let q := 1+w 0*ports 0
  ((q-w 1)*q-w 2)*(q^2-1)+w 0*(ports 2+ports 3*q)

theorem first_factor (f i : ℤ) : ((factors ports).1).eval (witness f i)=1 := by
  norm_num [factors,Expr.eval,ports,witness]
  change (0:ℤ)=0
  rfl

theorem main_factor (f i : ℤ) : ((factors ports).2.1).eval (witness f i)=68720812858 := by
  norm_num [factors,Expr.eval,ports,witness]
  change (68720812858:ℤ)=68720812858
  rfl

theorem strong_factor (f i : ℤ)
    (h : (55*55*i)*(55*55*i)+3135=3135*(f*f)) :
    ((factors ports).2.2.2).eval (witness f i)=1 := by
  simp [factors,Expr.eval,ports,witness]
  nlinarith [h]

theorem full_polynomial_ne_zero (f i : ℤ) : (expressionAt85 ports).eval (witness f i) ≠ 0 := by
  intro hz
  rw [expression_factors] at hz
  change ((factors ports).2.2.2).eval (witness f i) *
      (((factors ports).2.2.1).eval (witness f i) *
        (((factors ports).1).eval (witness f i) * ((factors ports).2.1).eval (witness f i))) - 1 = 0 at hz
  rw [main_factor] at hz
  have hd : (68720812858:ℤ) ∣ 1 := by
    refine ⟨((factors ports).2.2.2).eval (witness f i) *
      (((factors ports).2.2.1).eval (witness f i) * ((factors ports).1).eval (witness f i)),?_⟩
    calc
      (1:ℤ)=((factors ports).2.2.2).eval (witness f i) *
        (((factors ports).2.2.1).eval (witness f i) * (((factors ports).1).eval (witness f i) * 68720812858)) := by linarith
      _=68720812858*(((factors ports).2.2.2).eval (witness f i) *
        (((factors ports).2.2.1).eval (witness f i) * ((factors ports).1).eval (witness f i))) := by ring
  norm_num at hd

/-- Even with strict actual-style port bounds, positive exact small rank and
first/strong units do not imply the reverse gap. This is not a full zero. -/
theorem boundary_strong_nonzero_example :
    ∃ w : Fin 13 → ℤ, (∀ j,0<w j) ∧
      ((factors ports).1).eval w=1 ∧ ((factors ports).2.2.2).eval w=1 ∧
      0<ports 0 ∧ 0<ports 1 ∧ ports 2<ports 0 ∧ ports 0≤ports 3 ∧ ports 3<2*ports 0 ∧
      w 0=1 ∧ w 1=3 ∧ w 2=1 ∧ w 6=1 ∧ w 7=27 ∧ w 9=1 ∧ w 10=1 ∧
      rank w=1 ∧ rank w+1=2*1 ∧ rank w+2*1<(1+w 0*ports 0)^4 ∧
      ¬(w 1+w 2<1+w 0*ports 0) ∧ (expressionAt85 ports).eval w ≠ 0 := by
  obtain ⟨f,i,hf,hi,hs⟩ := strong_seed_at_successor (V:=ℕ) 54
  have hs' : (55*55*i)*(55*55*i)+3135=3135*(f*f) := by simpa [delta] using hs
  have hstrong : (55*55*(i:ℤ))*(55*55*(i:ℤ))+3135=3135*((f:ℤ)*(f:ℤ)) := by exact_mod_cast hs'
  let w := witness (f:ℤ) (i:ℤ)
  refine ⟨w,?_,first_factor _ _,strong_factor _ _ hstrong,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j
    fin_cases j <;> simp [w,witness] <;> first | exact_mod_cast hf | exact_mod_cast hi
  all_goals first | exact full_polynomial_ne_zero (f:ℤ) (i:ℤ) | rfl | norm_num [w,witness,ports,rank]
end DiophantineConsistency.AdaptiveGap85BoundaryStrongExample
