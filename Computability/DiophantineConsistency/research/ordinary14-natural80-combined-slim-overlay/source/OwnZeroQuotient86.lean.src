import FirstFields86
import QuotientFacts

/-! Source-only 86 own-zero q-cubed quotient and first-root composition.
All graph imports remain unelaborated; no witness map or endpoint follows. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.OwnZeroQuotient86Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open FirstFields86Draft QCubeQuotientFactsDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- An 86 own-zero with positive beta,J,Y yields positive s,tau, with
Y=q³*s and tau² equal to the first radicand. No sign is selected. -/
theorem quotient_and_root (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hJ : 0<v 0) (hY : 0<v 7)
    (hport : (p 0 : DiffRing V)=ι beta)
    (hz : InternalZero (P86ResidueGraph.graph p).output v) :
    ∃ s tau : V, 0<s ∧ v 7=Q beta v*s ∧ 0<tau ∧ tau*tau=radicand v := by
  have hb : 0<b beta v := by dsimp [b]; exact mul_pos hJ hbeta
  have hD : 0<radicand v := by dsimp [radicand]; simp
  have hf := (fields_of_zero p v hz).1
  rw [first_eval p beta v hport] at hf
  have hfield := sub_eq_zero.mp hf
  simpa only [q,Q,b,M] using
    QCubeQuotientFactsDraft.quotient_and_root (b beta v) (v 7) (firstP v) (v 8)
      (radicand v) hb hY hD (by simpa only [q,Q,b,M] using hfield)

end DiophantineConsistency.OwnZeroQuotient86Draft

#print axioms DiophantineConsistency.OwnZeroQuotient86Draft.quotient_and_root
