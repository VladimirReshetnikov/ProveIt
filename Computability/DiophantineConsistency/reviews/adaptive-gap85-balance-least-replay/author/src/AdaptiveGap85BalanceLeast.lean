import DiophantineConsistency.AdaptiveGap85BalanceMinimal

/-! Conditional least-number use for the positive-zero balance score.
Sigma-one definability of the score predicate is an explicit premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85BalanceLeast
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal AdaptiveGap85BalanceMinimal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def zeroScore (p : Fin 4 → ℕ) (m : V) : Prop :=
  ∃ v : Fin 13 → V, (∀ i,0<v i) ∧
    InternalZero (expressionAt85 (fun j => (p j:ℤ))) v ∧ m=v 1+v 2

/-- A definable nonempty set of positive-zero scores has a minimizing zero
whose balance step is blocked. The Σ₁ definability premise is not discharged. -/
theorem exists_minimal_blocked (p : Fin 4 → ℕ)
    (hp : 0<(p 0:V)) (hdef : 𝚺₁-Predicate (zeroScore (V:=V) p))
    (hex : ∃ v : Fin 13 → V, (∀ i,0<v i) ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    ∃ v : Fin 13 → V, (∀ i,0<v i) ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) v ∧
      (let b := v 0*(p 0:V); let q := 1+b;
       let A := v 6+(p 1:V)*q; let k := v 9+v 10;
       v 2≤q*b ∨ v 8≤q*(A+1)*(b*k+1)) := by
  obtain ⟨u,hu,huz⟩ := hex
  have hwit : zeroScore (V:=V) p (u 1+u 2) := ⟨u,hu,huz,rfl⟩
  obtain ⟨m,⟨v,hv,hz,hm⟩,hmin⟩ := InductionOnHierarchy.least_number 𝚺 1 hdef hwit
  have hleast : ∀ w : Fin 13 → V, (∀ i,0<w i) →
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) w →
      v 1+v 2≤w 1+w 2 := by
    intro w hwp hwz
    apply le_of_not_gt
    intro hlt
    apply hmin (w 1+w 2)
    · simpa only [hm] using hlt
    · exact ⟨w,hwp,hwz,rfl⟩
  exact ⟨v,hv,hz,minimal_zero_has_blocker p v (mul_pos (hv 0) hp) hv hz hleast⟩
end DiophantineConsistency.AdaptiveGap85BalanceLeast
