import IPRADerivations.Foundations.ApproximateWitness

/-! Conditional object-language estimate for transfer of dyadic route minima.
For an enumeration of (word,i,j), K is its largest index. Costs are
natural numerators over one common denominator. The input score terms
each contain the candidate index and one packed geometric parameter. -/
namespace Oloid.ObjectMesh
open LeanProofs LeanProofs.IPRA LeanProofs.ConciseIPRA
open LeanProofs.IPRA.Probability.FiniteLaws (Mn mn_le)
open LeanProofs.IPRA.Foundations.ApproximateWitness (argmin argmin_spec)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def premises (f g r : PTm 2) (K H p E : PTm n) : Fm PTm n :=
  let j := argmin g H p
  let i := inst2 r j p
  le i K ⋏ le (inst2 f i p) (inst2 g j p + E)

theorem transfer (f g r : PTm 2) (K H p E : PTm n)
    (h : Γ ⊢[PRAAx] premises f g r K H p E) :
    Γ ⊢[PRAAx] le (Mn f K p) (Mn g H p + E) := by
  let j := argmin g H p
  let i := inst2 r j p
  have feasible : Γ ⊢[PRAAx] le i K := Prf.andE₁ h
  have cost : Γ ⊢[PRAAx] le (inst2 f i p) (inst2 g j p + E) := Prf.andE₂ h
  have equal : Γ ⊢[PRAAx] inst2 g j p ≐ Mn g H p := Prf.andE₂ (argmin_spec g H p)
  exact le_trans (mn_le f feasible)
    (le_congr (.eqRefl _) (congrAdd equal (.eqRefl _)) cost)

def transferFormula (f g r : PTm 2) : Fm PTm 4 :=
  premises f g r (var 0) (var 1) (var 2) (var 3) ⟶
  le (Mn f (var 0) (var 2)) (Mn g (var 1) (var 2) + var 3)

/-- A universally closed object theorem for each choice of three
primitive-recursive score/rounding expressions. -/
theorem transfer_closed (f g r : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    univ 4 (transferFormula f g r) :=
  closeUniv 4 (.impI (transfer _ _ _ _ _ _ _ Prf.hyp0))

end Oloid.ObjectMesh
