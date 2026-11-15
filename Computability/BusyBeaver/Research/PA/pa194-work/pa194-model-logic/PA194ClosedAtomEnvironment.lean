import PA194ClosedTermEnvironment
import PA194FormulaScope
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ClosedEnvironment
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194PAeqBind PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem closedAtomEnvironment {k v P Q : V} (hv : IsUTermVec PA194PAeq.language k v)
    (hz : atomFreeBound k v = 0) (hb : nth P 0 = nth Q 0)
    (h0 : (0 : V) < k) (h1 : (1 : V) < k) :
    atomicEquality P (nth v 0) (nth v 1) = atomicEquality Q (nth v 0) (nth v 1) := by
  have hchild : ∀ i < k, termFreeBound (nth v i) = 0 := by
    intro i hi
    apply le_antisymm _ zero_le
    have hle : nth (termFreeBoundVec k v) i ≤ listMax (termFreeBoundVec k v) :=
      nth_le_listMax (by simpa [termFreeBoundVec_len hv] using hi)
    simpa [termFreeBoundVec_nth hv hi,atomFreeBound] using hle.trans (le_of_eq hz)
  have hrel (i : V) : SameTermContext (binaryParameters P i) (binaryParameters Q i) := by
    simp [SameTermContext,binaryParameters,hb]
  have ha := closedTermEnvironment (hv.2 0 h0) (binaryParameters P 1) (binaryParameters Q 1) (hrel 1) (hchild 0 h0)
  have hc := closedTermEnvironment (hv.2 1 h1) (binaryParameters P 0) (binaryParameters Q 0) (hrel 0) (hchild 1 h1)
  simp only [atomicEquality,ha,hc]
#print axioms closedAtomEnvironment
end generic
end PA194ClosedEnvironment
