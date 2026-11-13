module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateNeighborhoodCongruence
@[expose] public section

/-! Exact finite reserve-binder change for neighborhood equality. -/
namespace M6.PA.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCheckerBlueprint ActualHeadGraphs
universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]



/-- Open contexts may be generalized only with actual vacuity certificates. -/
noncomputable def Context.generalize {Γ : List V} {a : V} (p : Context Γ a) (x : V)
    (vacuity : ∀ h, h ∈ Γ → Certificate (wim h (wal x h))) : Context Γ (wal x a) :=
  match p with
  | .assumption h => .mp (.assumption h) (.closed (vacuity _ h))
  | .closed d => .closed (.all x d)
  | .mp p q => (p.generalize x vacuity).forallMP x (q.generalize x vacuity)

noncomputable def neighborhoodBinderChangeCore (a b z z' : V)
    (hza : z ≠ a) (hzb : z ≠ b) (hna : z' ≠ a) (hnb : z' ≠ b) :
    Certificate (wim (neighborhoodEquality a b z) (neighborhoodEquality a b z')) := by
  classical
  by_cases he : z' = z
  · subst z'; exact identity _
  have hnz : z ≠ z' := Ne.symm he
  let h : Context [neighborhoodEquality a b z] (neighborhoodEquality a b z) := .assumption (by simp)
  let hs := Context.mp h (.closed (neighborhoodSymmetryCore a b z))
  let l := Context.andIntro
    (.mp h (.closed (neighborhoodRightCongruenceCore a b z z' hza hzb hnz)))
    (.mp hs (.closed (neighborhoodRightCongruenceCore b a z z' hzb hza hnz)))
  let r := Context.andIntro
    (.mp h (.closed (neighborhoodLeftCongruenceCore a b z z' hza hzb hnz)))
    (.mp hs (.closed (neighborhoodLeftCongruenceCore b a z z' hzb hza hnz)))
  have hv : ∀ f, f ∈ [neighborhoodEquality a b z] → Certificate (wim f (wal z' f)) := by
    intro f hf
    have hf' : f = neighborhoodEquality a b z := List.mem_singleton.mp hf
    subst f
    simpa only [neighborhood_expr_eq] using neighborhoodEqualityVacuity a b z z' hna hnb he
  exact (Context.andIntro (l.generalize z' hv) (r.generalize z' hv)).deduction.empty


noncomputable def neighborhoodBinderChange (a b z z' : V)
    (hza : z ≠ a) (hzb : z ≠ b) (hna : z' ≠ a) (hnb : z' ≠ b) :
    Certificate (wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0)
      (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z' 0)) := by
  rw [neighborhood_expr_eq,neighborhood_expr_eq]
  exact neighborhoodBinderChangeCore a b z z' hza hzb hna hnb

#print axioms Context.generalize
#print axioms neighborhoodBinderChangeCore
#print axioms neighborhoodBinderChange
end M6.PA.ActualCertificateEquivalence

