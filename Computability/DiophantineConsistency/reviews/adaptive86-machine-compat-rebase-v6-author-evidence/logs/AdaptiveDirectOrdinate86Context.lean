import DiophantineConsistency.AdaptiveFirstRootFactor87Syntax
import DiophantineConsistency.ArithmeticSignedPairs

/-! Arbitrary expression contexts respect signed-pair equivalence in every
    IΣ₁ model. This is a generic tool, not an 86-equation equivalence. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.AdaptiveDirectOrdinate86Context
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax ArithmeticSignedPairs

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {σ τ : Type*}

private theorem add_equiv {p q r s : Pair V} (h : Equivalent p q) (k : Equivalent r s) :
    Equivalent (pairAdd p r) (pairAdd q s) := by
  change p.1+q.2=p.2+q.1 at h
  change r.1+s.2=r.2+s.1 at k
  change (p.1+r.1)+(q.2+s.2)=(p.2+r.2)+(q.1+s.1)
  calc
    _=(p.1+q.2)+(r.1+s.2) := by ring
    _=(p.2+q.1)+(r.2+s.1) := by rw [h,k]
    _=_ := by ring

private theorem sub_equiv {p q r s : Pair V} (h : Equivalent p q) (k : Equivalent r s) :
    Equivalent (pairSub p r) (pairSub q s) := by
  apply add_equiv h
  change r.2+s.1=r.1+s.2
  exact k.symm

/-- Equivalent signed inputs stay equivalent through any syntax context. -/
theorem splitEval_subst_equiv (e : Expr σ) (f g : σ → Expr τ) (v : τ → V)
    (h : ∀ i, Equivalent (splitEval (f i) v) (splitEval (g i) v)) :
    Equivalent (splitEval (e.subst f) v) (splitEval (e.subst g) v) := by
  induction e with
  | constant c => exact equivalent_refl _
  | var i => exact h i
  | add p q hp hq =>
      change Equivalent (splitEval (p.subst f + q.subst f) v)
        (splitEval (p.subst g + q.subst g) v)
      rw [splitEval_add,splitEval_add]
      exact add_equiv hp hq
  | sub p q hp hq =>
      change Equivalent (splitEval (p.subst f - q.subst f) v)
        (splitEval (p.subst g - q.subst g) v)
      rw [splitEval_sub,splitEval_sub]
      exact sub_equiv hp hq
  | mul p q hp hq =>
      change Equivalent (splitEval (p.subst f * q.subst f) v)
        (splitEval (p.subst g * q.subst g) v)
      rw [splitEval_mul,splitEval_mul]
      exact equivalent_multiply hp hq

/-- Equivalent signed evaluations have the same zero test. -/
theorem equivalent_zero_iff {p q : Pair V} (h : Equivalent p q) :
    p.1=p.2 ↔ q.1=q.2 := by
  change p.1+q.2=p.2+q.1 at h
  constructor
  · intro hp
    have h' : p.1+q.2=p.1+q.1 := by simpa only [hp] using h
    exact (add_left_cancel h').symm
  · intro hq
    have h' : p.1+q.1=p.2+q.1 := by simpa only [hq] using h
    exact add_right_cancel h'

end DiophantineConsistency.AdaptiveDirectOrdinate86Context
