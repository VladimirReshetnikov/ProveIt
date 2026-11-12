import ModelEquivalence75To74

/-! Source-only specialization of the explicit discreteness premise. This
reuses the difference-ring positive-gap lemma directly; no ModelArithmetic
import, Lean elaboration or provider claim. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelDiscrete7574Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The internal model's positive elements are at least one; its difference
ring inherits that discrete-order property. -/
theorem difference_ring_discrete : Discrete (DiffRing V) :=
  fun _ hx => one_le_of_pos (fun a ha => pos_iff_one_le.mp ha) hx

/-- Proposed 75↔74 model zero equivalence at explicit positive beta and
nonnegative K representations. -/
theorem positive_zero_iff (p : Fin 4 → ℤ) (beta K : V)
    (hb : 0<beta) (hbeta : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) :
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P75NegativePell.graph p).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P74PositiveGuard.graph p).output v) :=
  ModelEquivalence7574Draft.positive_zero_iff p beta K difference_ring_discrete hb hbeta hK

/-- Natural-port specialization; K is nonnegative by its natural type. -/
theorem positive_zero_iff_natural_ports (p : Fin 4 → ℕ) (hb : 0<(p 0 : V)) :
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P75NegativePell.graph (fun j => (p j : ℤ))).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P74PositiveGuard.graph (fun j => (p j : ℤ))).output v) :=
  ModelEquivalence7574Draft.positive_zero_iff_natural_ports p difference_ring_discrete hb

end DiophantineConsistency.ModelDiscrete7574Draft

#print axioms DiophantineConsistency.ModelDiscrete7574Draft.difference_ring_discrete
#print axioms DiophantineConsistency.ModelDiscrete7574Draft.positive_zero_iff_natural_ports
