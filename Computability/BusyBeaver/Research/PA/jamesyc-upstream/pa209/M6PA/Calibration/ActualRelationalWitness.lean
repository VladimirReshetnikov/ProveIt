module
public import M6PA.Theory
public import M6PA.Calibration.ActualRelationalBinders
@[expose] public section

/-! The primitive-equality witness from actual R1 is converted to a
membership-only equality witness using ONLY special-label primitive vacuity.
Arbitrary-label primitive equality-vacuity is neither assumed nor proved. -/
namespace M6.PA.NativeCalculus.ActualBasis

def primitiveToSpecialNeighborhood (a b : Nat) :
    Proof (wim (weq a b) (neighborhoodEquality a b (wel a b))) := by
  let k := wel a b
  let h : Context [weq a b] (weq a b) := .assumption (by simp)
  let hs := Context.mp h (.closed (primitiveSymmetry a b))
  let l := Context.andIntro
    (.mp h (.closed (memLeftRewrite k a b)))
    (.mp hs (.closed (memLeftRewrite k b a)))
  let r := Context.andIntro
    (.mp h (.closed (memRightRewrite k a b)))
    (.mp hs (.closed (memRightRewrite k b a)))
  have hv : ∀ f, f ∈ [weq a b] → Proof (wim f (wal k f)) := by
    intro f hf
    have hf' : f = weq a b := List.mem_singleton.mp hf
    subst f
    exact fromCore (ActualCore.actualSpecialVacuity a b)
  exact (Context.andIntro (l.generalize k hv) (r.generalize k hv)).deduction.empty

def primitiveToNeighborhood (a b z : Nat) (hza : z ≠ a) (hzb : z ≠ b) :
    Proof (wim (weq a b) (neighborhoodEquality a b z)) := by
  have hp := M6.Source.Enumeration.pair_bounds a b
  have hka : wel a b ≠ a := by simp only [wel]; omega
  have hkb : wel a b ≠ b := by simp only [wel]; omega
  exact implicationCompose (primitiveToSpecialNeighborhood a b)
    (neighborhoodBinderChange a b (wel a b) z hka hkb hza hzb)

def existentialMonotonicity (x : Nat) {a b : Nat} (p : Proof (wim a b)) :
    Proof (wim (wex x a) (wex x b)) :=
  contrapose (.mp (.all x (contrapose p)) (r2 x (wn b) (wn a)))

def neighborhoodWitness (x c z : Nat) (hzx : z ≠ x) (hzc : z ≠ c) :
    Proof (wex x (neighborhoodEquality x c z)) :=
  .mp (fromCore (.r1 x c))
    (existentialMonotonicity x (primitiveToNeighborhood x c z hzx hzc))

#print axioms primitiveToNeighborhood
#print axioms neighborhoodWitness
end M6.PA.NativeCalculus.ActualBasis

