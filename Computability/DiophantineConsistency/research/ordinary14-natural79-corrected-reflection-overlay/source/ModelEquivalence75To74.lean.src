import Positive75To74
import OwnZeroGuardStrict74

/-! Source-only conditional model equivalence. Discreteness, positive beta,
and beta/K port casts remain explicit; all imported sources are unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelEquivalence7574Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed positive-zero equivalence from each graph's own zero. -/
theorem positive_zero_iff (p : Fin 4 → ℤ) (beta K : V)
    (hd : Discrete (DiffRing V)) (hb : 0<beta)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K) :
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P75NegativePell.graph p).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P74PositiveGuard.graph p).output v) := by
  constructor
  · rintro ⟨v,hv,hz⟩
    exact Positive75To74Draft.forward_map p v hv hz
  · rintro ⟨v,hv,hz⟩
    have hstrict := OwnZeroGuardStrict74Draft.strict_of_zero p beta K v hd hbeta hK hb hv hz
    exact Positive75To74Draft.reverse_map p v hv hstrict hz

/-- Natural-port specialization, still retaining explicit model discreteness. -/
theorem positive_zero_iff_natural_ports (p : Fin 4 → ℕ)
    (hd : Discrete (DiffRing V)) (hb : 0<(p 0 : V)) :
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P75NegativePell.graph (fun j => (p j : ℤ))).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero (P74PositiveGuard.graph (fun j => (p j : ℤ))).output v) := by
  apply positive_zero_iff (fun j => (p j : ℤ)) (p 0 : V) (p 1 : V) hd hb
  · simpa only using (P72Root.cast_port p 0)
  · simpa only using (P72Root.cast_port p 1)

end DiophantineConsistency.ModelEquivalence7574Draft

#print axioms DiophantineConsistency.ModelEquivalence7574Draft.positive_zero_iff
#print axioms DiophantineConsistency.ModelEquivalence7574Draft.positive_zero_iff_natural_ports
