import PA194SuccUniqueSchematic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
namespace PA194SuccUniqueSchematic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping PA194Schematic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
/-- Naming an element means it is E-related to some underlying value. -/
def nameValue {n : ℕ} (i : Fin n) : Semiformula L Empty n :=
  ∃⁰ (V 0 ⋏ E i.succ 0)
/-- Naming a successor output means it is E-related to an output of S on a value. -/
def nameSuccessor {n : ℕ} (i : Fin n) : Semiformula L Empty n :=
  ∃⁰ ((∃⁰ (V 0 ⋏ S 0 1)) ⋏ E i.succ 0)
def namesUnique : Sentence L := ∀⁰ (∀⁰ ((nameValue 1 ⋏ nameValue 0) 🡒 E 1 0))
def valuesSelf : Sentence L := ∀⁰ (V 0 🡒 E 0 0)
def equivSymmetric : Sentence L := ∀⁰ (∀⁰ (E 1 0 🡒 E 0 1))
def equivTransitive : Sentence L := ∀⁰ (∀⁰ (∀⁰ ((E 2 1 ⋏ E 1 0) 🡒 E 2 0)))
def successorNamesUnique : Sentence L := ∀⁰ (∀⁰ ((nameSuccessor 1 ⋏ nameSuccessor 0) 🡒 E 1 0))
def namingSchema : Sentence L := namesUnique 🡒 (valuesSelf 🡒 (equivSymmetric 🡒
  (equivTransitive 🡒 (successorCoherent 🡒 successorNamesUnique))))

theorem namingSchema_valid (M : Type) [Nonempty M] [Structure L M] : M↓[L] ⊧ namingSchema := by
  change (Semiformula.Eval (L := L) (M := M) ![] Empty.elim) namingSchema
  simp [namingSchema,namesUnique,valuesSelf,equivSymmetric,equivTransitive,successorCoherent,
    successorNamesUnique,nameValue,nameSuccessor,V,E,S,Semiformula.eval_all,Semiformula.eval_ex,Semiformula.eval_rel]
  intro huniq hself hsym htrans hcoh n n' b a ha hsa hnb b' a' ha' hsa' hn'b'
  have haa' := huniq a a' a ha (hself a ha) a' ha' (hself a' ha')
  have hbb' := hcoh a a' b b' haa' hsa hsa'
  exact htrans n b' n' (htrans n b b' hnb hbb') (hsym n' b' hn'b')

theorem namingCertificate {W : Type} [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {K : Language} [K.Encodable] [K.LORDefinable]
    (σ : (i : Pred) → Bootstrapping.Semiformula W K (arity i)) (T : Theory K) [T.Δ₁] :
    T.internalize W ⊢ PA194Schematic.instS σ namingSchema :=
  PA194Schematic.instS_provable_of_valid σ T namingSchema namingSchema_valid

#print axioms namingSchema_valid
#print axioms namingCertificate
end PA194SuccUniqueSchematic
