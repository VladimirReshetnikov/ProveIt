import DiophantineConsistency.GapCircuitSteps66
import DiophantineConsistency.ArithmeticDAGPowers

/-! # Exact input translation between the two pinned H2082 parent circuits
The positive circuit uses internal j = input7-1. The natural circuit adds one
to the other eight inputs. A finite reference certificate and local evaluator
uniqueness prove that the two counted circuits implement this translation. -/
namespace DiophantineConsistency.GapCircuitTranslation66
open ArithmeticDAG GapCircuitSteps66
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
variable {R : Type*} [CommRing R]

/-- References for all retained positive-circuit registers. Register 7 is handled
separately because the positive program also stores its unshifted j input. -/
def positiveToNatural (i : ℕ) : ℕ :=
  if i<7 then i+10 else if i=8 then 17 else if i=9 then 9 else if i=10 then 7
    else i+7

private theorem reference_certificate : ∀ i : Fin 477, 11 ≤ i.val → i.val ≠ 421 →
    positiveToNatural i.val < 484 ∧
    (∀ j : Fin 9, GapCircuit66.naturalNodes.getD (positiveToNatural i.val) (.literal 0) ≠ .input j) ∧
    NodeRel (fun j k => j≠7 ∧ positiveToNatural j=k)
      (GapCircuit66.positiveNodes.getD i.val (.literal 0))
      (GapCircuit66.naturalNodes.getD (positiveToNatural i.val) (.literal 0)) := by
  decide +kernel

private theorem evalAt_input_irrelevant (p : Fin 11 → R) (x y : Fin 9 → R)
    (v : ℕ → R) (n : Node 9 11) (h : ∀ j, n ≠ .input j) :
    n.evalAt p x v = n.evalAt p y v := by
  cases n <;> simp only [Node.evalAt]
  exact False.elim (h _ rfl)

/-- The exact 443-operation positive parent is the exact 450-operation natural
parent with every input decreased by one. This is an identity over any ring. -/
theorem positiveValue_eq_naturalValue (p : Fin 11 → R) (x : Fin 9 → R) :
    GapCircuit66.positiveValue p x =
      GapCircuit66.naturalValue p (fun i => x i-1) := by
  let y : Fin 9 → R := fun i => x i-1
  let u : ℕ → R := naturalRegister p y
  let v : ℕ → R := fun i => if i=7 then x 7 else u (positiveToNatural i)
  have href (i j : ℕ) (h : i≠7 ∧ positiveToNatural i=j) : u j = v i := by
    simp only [v,if_neg h.1,h.2]
  have hv : ∀ i < GapCircuit66.positiveNodes.length,
      v i = (GapCircuit66.positiveNodes.getD i (.literal 0)).evalAt p x v := by
    intro i hi
    have hi' : i<477 := by simpa only [GapCircuit66.positive_length] using hi
    by_cases he : i<11
    · interval_cases i <;>
        simp [v,u,y,positiveToNatural,GapCircuit66.positiveNodes,Node.evalAt,
          natural_step_0,natural_step_1,natural_step_2,natural_step_3,natural_step_4,
          natural_step_5,natural_step_6,natural_step_7,natural_step_8,natural_step_9,
          natural_step_10,natural_step_11,natural_step_12,natural_step_13,
          natural_step_14,natural_step_15,natural_step_16,natural_step_17]
    · by_cases hswap : i = 421
      · subst i
        change naturalRegister p y 428 = naturalRegister p y 15*naturalRegister p y 7
        rw [natural_step_428]
        ring
      have h11 : 11 ≤ i := by omega
      obtain ⟨hm,hn,hr⟩ := reference_certificate ⟨i,hi'⟩ h11 hswap
      have hvself : v i=u (positiveToNatural i) := by
        simp only [v,if_neg (show i≠7 by omega)]
      calc
        v i = u (positiveToNatural i) := hvself
        _ = (GapCircuit66.naturalNodes.getD (positiveToNatural i) (.literal 0)).evalAt p y u :=
          run_node_equation p y GapCircuit66.naturalNodes
            GapCircuit66.natural_topological _ (by simpa only [GapCircuit66.natural_length] using hm)
        _ = (GapCircuit66.naturalNodes.getD (positiveToNatural i) (.literal 0)).evalAt p x u :=
          evalAt_input_irrelevant p y x u _ hn
        _ = (GapCircuit66.positiveNodes.getD i (.literal 0)).evalAt p x v :=
          evalAt_of_NodeRel p x _ _ _ v u hr href
  change value GapCircuit66.positiveNodes 476 p x = u 483
  rw [value_eq_of_node_equations p x GapCircuit66.positiveNodes
    GapCircuit66.positive_topological 476 (by rw [GapCircuit66.positive_length];decide) v hv]
  simp only [v,positiveToNatural]
  rfl

end DiophantineConsistency.GapCircuitTranslation66
