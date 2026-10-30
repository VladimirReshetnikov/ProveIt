import DiophantineConsistency.HerbrandExistentialSequents

/-! Interpret existential formulas using a finite list of syntactic terms. -/
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandBoundedSemantics
open LO LO.FirstOrder
open scoped LO.FirstOrder

/-- Formula-node count, independent of the sizes of terms. -/
def logicalSize {L : Language} {ξ : Type} : {n : ℕ} → Semiformula L ξ n → ℕ
  | _, .rel _ _ => 0
  | _, .nrel _ _ => 0
  | _, ⊤ => 0
  | _, ⊥ => 0
  | _, p ⋏ q => logicalSize p + logicalSize q + 1
  | _, p ⋎ q => logicalSize p + logicalSize q + 1
  | _, ∀⁰ p => logicalSize p + 1
  | _, ∃⁰ p => logicalSize p + 1

theorem logicalSize_rew {L : Language} {ξ η : Type} {n m : ℕ}
    (φ : Semiformula L ξ n) (w : Rew L ξ n η m) : logicalSize (w ▹ φ) = logicalSize φ := by
  induction φ using Semiformula.rec' generalizing η m with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => rfl
  | hnrel r v => rfl
  | hand p q ihp ihq => simp [logicalSize, ihp, ihq]
  | hor p q ihp ihq => simp [logicalSize, ihp, ihq]
  | hall p ih => simp [logicalSize, ih]
  | hexs p ih => simp [logicalSize, ih]

/-- Universal quantifiers are deliberately interpreted as false; the
extraction theorem uses only derivations with no universal-rule nodes. -/
def boundedEval {L : Language} {M : Type} [Structure L M]
    (terms : List (SyntacticTerm L)) (e : ℕ → M) : Proposition L → Prop
  | .rel r v => Structure.rel r (Semiterm.val ![] e ∘ v)
  | .nrel r v => ¬Structure.rel r (Semiterm.val ![] e ∘ v)
  | ⊤ => True
  | ⊥ => False
  | p ⋏ q => boundedEval terms e p ∧ boundedEval terms e q
  | p ⋎ q => boundedEval terms e p ∨ boundedEval terms e q
  | ∀⁰ _ => False
  | ∃⁰ p => ∃ t ∈ terms, boundedEval terms e (p/[t])
termination_by φ => logicalSize φ
decreasing_by
  all_goals simp_wf
  all_goals simp [logicalSize, logicalSize_rew]

end DiophantineConsistency.HerbrandBoundedSemantics
