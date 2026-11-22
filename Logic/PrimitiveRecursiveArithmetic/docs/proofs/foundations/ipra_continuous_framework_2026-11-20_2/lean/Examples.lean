import ContinuousSyntax

/-! A sharp example: adding the midpoint to a two-endpoint net changes the
    quantified tent-function maximum by exactly the atomic distortion. -/

namespace QuantitativeIPRA.Examples

open QuantitativeIPRA.Continuous

abbrev Atom (n : Nat) := Fin n

def coarse : Model Atom where
  last := 1
  atomic := fun a ρ => 2 * ρ a

def fine : Model Atom where
  last := 2
  atomic := fun a ρ => ρ a

def nearby (i j : Nat) : Prop := Close 1 (2 * i) j

theorem coarse_fine : Correspondence coarse fine nearby 1 where
  total := {
    left := by
      intro i hi
      refine ⟨2 * i, ?_, ?_⟩
      · change 2 * i ≤ 2
        change i ≤ 1 at hi
        omega
      · exact close_refl 1 (2 * i)
    right := by
      intro j hj
      change j ≤ 2 at hj
      by_cases h : j ≤ 1
      · refine ⟨0, by decide, ?_⟩
        change Close 1 0 j
        constructor <;> omega
      · refine ⟨1, by decide, ?_⟩
        change Close 1 2 j
        constructor <;> omega }
  atoms := by
    intro n a ρ σ _ _ hR
    exact hR a

def tent : Formula Atom 0 :=
  .supremum (.minimum (.atom (0 : Fin 1)) (.complement 2 (.atom (0 : Fin 1))))

def emptyEnv : Fin 0 → Nat := Fin.elim0

theorem coarse_tent : eval coarse tent emptyEnv = 0 := by decide
theorem fine_tent : eval fine tent emptyEnv = 1 := by decide

theorem tent_transfer :
    Close 1 (eval coarse tent emptyEnv) (eval fine tent emptyEnv) :=
  formula_transfer coarse_fine tent emptyEnv emptyEnv
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

theorem tent_error_is_sharp :
    ¬ Close 0 (eval coarse tent emptyEnv) (eval fine tent emptyEnv) := by
  rw [coarse_tent, fine_tent]
  simp [Close]

end QuantitativeIPRA.Examples
