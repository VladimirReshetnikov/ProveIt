import DiophantineConsistency.AdaptiveGap85ThirdCurrent

/-! A first-coordinate-minimal positive zero cannot admit the third shift.
Existence of such a minimum is a separate least-number task. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ThirdMinimal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal AdaptiveGap85ThirdModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem minimal_first_has_blocker (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hp : 0<(p 0:V)) (hv : ∀ i,0<v i)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v)
    (hmin : ∀ w : Fin 13 → V, (∀ i,0<w i) →
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) w → v 1≤w 1) :
    let b := v 0*(p 0:V)
    let q := 1+b
    let A := v 6+(p 1:V)*q
    let U := v 7*(q*q)
    let c := v 9+v 7*(v 9+v 10)
    v 1≤A*(c*U) ∨ v 12≤(q*q-1)*(A+1)*c := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let A : V := v 6+(p 1:V)*q
  let U : V := v 7*(q*q)
  let c : V := v 9+v 7*(v 9+v 10)
  change v 1≤A*(c*U) ∨ v 12≤(q*q-1)*(A+1)*c
  by_cases hF : v 1≤A*(c*U)
  · exact Or.inl hF
  by_cases hg : v 12≤(q*q-1)*(A+1)*c
  · exact Or.inr hg
  have hF' : A*(c*U*(1:V))<v 1 := by simpa using lt_of_not_ge hF
  have hg' : (q*q-1)*(A+1)*c*(1:V)<v 12 := by simpa using lt_of_not_ge hg
  have hs := AdaptiveGap85ThirdCurrent.positive_zero_shift p v 1 hp hv hF' hg' hz
  have hle := hmin (shift p v 1) hs.1 hs.2
  have hlt := AdaptiveGap85ThirdCurrent.first_strictly_decreases p v 1 hv (by simp) (le_of_lt hF')
  exact False.elim ((not_lt_of_ge hle) hlt)
end DiophantineConsistency.AdaptiveGap85ThirdMinimal
