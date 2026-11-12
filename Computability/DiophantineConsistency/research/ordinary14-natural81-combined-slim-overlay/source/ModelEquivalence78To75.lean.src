import Model75To78
import Model78To75
import DiophantineConsistency.Compact44.P72Root

/-! Source-only pointwise 75/78 comparison. Component drafts are unelaborated;
no provider, endpoint or external file binding is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelEquivalence7875Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed pointwise comparison at the same valuation and integer ports. -/
theorem zero_iff (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hb : 0<beta) (hv : ∀ j, 0<v j) :
    InternalZero (P75NegativePell.graph p).output v ↔
      InternalZero (P78AuxRoot.graph p).output v := by
  exact ⟨Model75To78Draft.zero_78_of_75_zero p beta v hbeta hb hv,
    Model78To75Draft.zero_of_78_zero p v⟩

/-- Natural-port specialization; the positive model beta is cast from p 0. -/
theorem zero_iff_natural_ports (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hb : 0<(p 0 : V)) (hv : ∀ j, 0<v j) :
    InternalZero (P75NegativePell.graph (fun j => (p j : ℤ))).output v ↔
      InternalZero (P78AuxRoot.graph (fun j => (p j : ℤ))).output v := by
  have hbeta : (((fun j => (p j : ℤ)) 0 : ℤ) : DiffRing V)=ι (p 0 : V) := P72Root.cast_port p 0
  exact zero_iff (fun j => (p j : ℤ)) (p 0 : V) v hbeta hb hv

end DiophantineConsistency.ModelEquivalence7875Draft

#print axioms DiophantineConsistency.ModelEquivalence7875Draft.zero_iff
#print axioms DiophantineConsistency.ModelEquivalence7875Draft.zero_iff_natural_ports
