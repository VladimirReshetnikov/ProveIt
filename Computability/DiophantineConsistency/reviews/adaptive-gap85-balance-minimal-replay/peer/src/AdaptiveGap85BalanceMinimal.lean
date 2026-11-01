import DiophantineConsistency.AdaptiveGap85BalanceProgress

/-! A minimal positive zero cannot admit the decreasing balance shift.
Existence of such a minimum is a separate definability/least-number task. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85BalanceMinimal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal AdaptiveGap85BalanceModel
open AdaptiveGap85BalanceProgress
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A zero minimizing F+C either lacks enough C or lacks enough r for one
positive balance step. This does not assert that such a minimum exists. -/
theorem minimal_zero_has_blocker (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<v 0*(p 0:V)) (hv : ∀ i,0<v i)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v)
    (hmin : ∀ w : Fin 13 → V, (∀ i,0<w i) →
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) w →
      v 1+v 2≤w 1+w 2) :
    let b := v 0*(p 0:V)
    let q := 1+b
    let A := v 6+(p 1:V)*q
    let k := v 9+v 10
    v 2≤q*b ∨ v 8≤q*(A+1)*(b*k+1) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let A : V := v 6+(p 1:V)*q
  let k : V := v 9+v 10
  change v 2≤q*b ∨ v 8≤q*(A+1)*(b*k+1)
  by_cases hc : v 2≤q*b
  · exact Or.inl hc
  by_cases hr : v 8≤q*(A+1)*(b*k+1)
  · exact Or.inr hr
  have hc' : q*b*(1:V)<v 2 := by simpa using lt_of_not_ge hc
  have hr' : q*(1:V)*(A+1)*(b*k+1)<v 8 := by simpa using lt_of_not_ge hr
  have hs := positive_zero_shift p v 1 hv hc' hr' hz
  have hle := hmin (shift p v 1) hs.1 hs.2.1
  have hlt := gap_strictly_decreases p v 1 hb (by simp) (le_of_lt hc')
  exact False.elim ((not_lt_of_ge hle) hlt)
end DiophantineConsistency.AdaptiveGap85BalanceMinimal
