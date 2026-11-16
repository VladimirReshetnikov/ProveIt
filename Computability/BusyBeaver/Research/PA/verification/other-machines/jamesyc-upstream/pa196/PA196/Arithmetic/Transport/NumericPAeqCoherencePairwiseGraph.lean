module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherencePairwiseCode
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqValueCoherence

namespace PA196.Arithmetic.Transport.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def pairwiseCodeGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out p q. ∃ x y a b pair iso body inner, !qqBvarDef x 1 ∧ !qqBvarDef y 0 ∧
    !(substs1Graph RelationalSource.language) a x p ∧ !(substs1Graph RelationalSource.language) b y q ∧
    !qqAndDef pair a b ∧ !NumericPAeqValueIsoGuard.isoCodeGraph iso x y ∧
    !(impGraph RelationalSource.language) body pair iso ∧ !qqAllDef inner body ∧ !qqAllDef out inner”
theorem pairwiseCode_graph (out p q:V):
    pairwiseCodeGraph.val.Evalb ![out,p,q] ↔ out=pairwiseCode p q := by
  simp [pairwiseCodeGraph,pairwiseCode,NumericPAeqValueIsoGuard.isoCode,NumericPAeqValueIsoGuard.isoCode_graph,Matrix.comp_vecCons'']
#print axioms pairwiseCode_graph
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence
