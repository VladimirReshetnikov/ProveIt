module
public import M6PA.Theory
public import M6PA.Calibration.ActualRelationalEquivalence
@[expose] public section

/-! Explicit binder change for the membership-only equality replacement.
This is a finite actual-basis proof, not an assumed alpha-conversion rule. -/
namespace M6.PA.NativeCalculus.ActualBasis

def neighborhoodBinderChange (a b z z' : Nat)
    (hza : z ≠ a) (hzb : z ≠ b) (hna : z' ≠ a) (hnb : z' ≠ b) :
    Proof (wim (neighborhoodEquality a b z) (neighborhoodEquality a b z')) := by
  by_cases he : z' = z
  · subst z'; exact identity _
  have hnz : z ≠ z' := Ne.symm he
  let h : Context [neighborhoodEquality a b z] (neighborhoodEquality a b z) := .assumption (by simp)
  let hs := Context.mp h (.closed (neighborhoodSymmetry a b z))
  let l := Context.andIntro
    (.mp h (.closed (neighborhoodRightCongruence a b z z' hza hzb hnz)))
    (.mp hs (.closed (neighborhoodRightCongruence b a z z' hzb hza hnz)))
  let r := Context.andIntro
    (.mp h (.closed (neighborhoodLeftCongruence a b z z' hza hzb hnz)))
    (.mp hs (.closed (neighborhoodLeftCongruence b a z z' hzb hza hnz)))
  have hv : ∀ f, f ∈ [neighborhoodEquality a b z] → Proof (wim f (wal z' f)) := by
    intro f hf
    have hf' : f = neighborhoodEquality a b z := List.mem_singleton.mp hf
    subst f
    exact neighborhoodEqualityVacuity a b z z' hna hnb he
  exact (Context.andIntro (l.generalize z' hv) (r.generalize z' hv)).deduction.empty

#print axioms neighborhoodBinderChange
end M6.PA.NativeCalculus.ActualBasis

