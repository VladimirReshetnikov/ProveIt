import ZeroFields
import PositiveClient

/-! Source-only first natural norm from the 84 graph's own zero. The imported
sources are unelaborated drafts; no Pell index or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FirstNorm84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open DirectFirstRootModelDraft DirectFirstRootGraphClientDraft DirectFirstRootPositiveClientDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The 84 own-zero first field supplies its positive natural magnitude and
first norm. Beta/J positivity and the beta cast are explicit. -/
theorem first_norm (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hJ : 0<v 0) (hport : (p 0 : DiffRing V)=ι beta)
    (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    0<magnitude (firstP beta v,v 8) ∧
    magnitude (firstP beta v,v 8)*magnitude (firstP beta v,v 8)=radicand beta v := by
  have hf := (ZeroFields8485Draft.fields84 p v hz).1
  change DirectFirstRootGraphClientDraft.eval (P84QcubeGraph.graph p).A0 v=0 at hf
  have he := old_first_eval p beta v (v 8) hport
  rw [putRoot_self] at he
  rw [he] at hf
  exact root_of_scaled_residual (scale beta v) (firstP beta v) (v 8) (radicand beta v)
    (scale_positive beta v hbeta hJ) (radicand_positive beta v) hf

end DiophantineConsistency.FirstNorm84Draft

#print axioms DiophantineConsistency.FirstNorm84Draft.first_norm
