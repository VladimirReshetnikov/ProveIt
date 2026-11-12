import FirstNormClient
import DiophantineConsistency.ArithmeticPellFirstNorm

/-! Source-only first Pell-index extraction. All graph/client imports remain
unelaborated; no exact rank index or endpoint result is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FirstIndex84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticPellRecurrence DirectFirstRootGraphClientDraft FirstNorm84Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Classify the first norm from the 84 own-zero under explicit positive
beta and slots J,w,s. No rank or main index is inferred here. -/
theorem first_index (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7)
    (hport : (p 0 : DiffRing V)=ι beta)
    (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    let Q := (X beta v*Y beta v)*Y beta v
    let tau := magnitude (firstP beta v,v 8)
    let K := k v
    ∃ n : V, n≤K ∧ xcoord n (2*(Q-1)+1)=tau ∧
      2*ycoord n (2*(Q-1)+1)=K := by
  let Q := (X beta v*Y beta v)*Y beta v
  let tau := magnitude (firstP beta v,v 8)
  let K := k v
  have hq : 0<q beta v := by dsimp [q]; simp
  have hX : 0<X beta v := by dsimp [X]; exact mul_pos hq hw
  have hY : 0<Y beta v := by dsimp [Y]; exact mul_pos (mul_pos hq (mul_pos hq hq)) hs
  have hQ : 0<Q := by dsimp [Q]; exact mul_pos (mul_pos hX hY) hY
  have hn := (first_norm p beta v hbeta hJ hport hz).2
  have hnorm : tau*tau=1+Q*(Q+1)*K*K := by
    rw [hn]
    dsimp [tau,Q,K,radicand,firstP,ell]
    ring
  exact ArithmeticPellFirstNorm.positive_parameter_solution Q tau K hQ hnorm

end DiophantineConsistency.FirstIndex84Draft

#print axioms DiophantineConsistency.FirstIndex84Draft.first_index
