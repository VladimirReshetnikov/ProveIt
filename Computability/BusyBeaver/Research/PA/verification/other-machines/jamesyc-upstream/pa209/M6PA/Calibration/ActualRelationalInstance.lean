module
public import M6PA.Theory
public import M6PA.Calibration.ActualRelationalVacuity
@[expose] public section
/-! Concrete atomic universal specialization in the full actual basis.
Only membership-target vacuity is used; primitive equality-vacuity is absent. -/
namespace M6.PA.NativeCalculus.ActualBasis
def Context.existsElim {Γ : List Nat} (x : Nat) {a b : Nat}
    (hv : Proof (wim b (wal x b)))
    (p : Context Γ (wal x (wim a b))) (q : Context Γ (wex x a)) : Context Γ b := by
  let hn : Context (wn b :: Γ) (wn b) := .assumption (by simp)
  let hnb : Context (wn b :: Γ) (wal x (wn b)) :=
    .mp hn (.closed (negationVacuity x b hv))
  let hc : Context (wn b :: Γ) (wal x (wim (wn b) (wn a))) :=
    (p.up (wn b)).forallMP x (.closed (.all x (contraposition a b)))
  let ha : Context (wn b :: Γ) (wal x (wn a)) := hnb.forallMP x hc
  exact (Context.mp ha (q.up (wn b))).deduction.dne


def specializeWithEquality (z c atom target : Nat)
    (hv : Proof (wim target (wal z target)))
    (hr : Proof (wim (weq z c) (wim atom target))) :
    Proof (wim (wal z atom) target) := by
  let he : Context [weq z c,atom] (weq z c) := .assumption (by simp)
  let ha : Context [weq z c,atom] atom := .assumption (by simp)
  let hs : Proof (wim atom (wim (weq z c) target)) :=
    (Context.mp ha (.mp he (.closed hr))).deduction.deduction.empty
  let hu : Context [wal z atom] (wal z atom) := .assumption (by simp)
  let ht : Context [wal z atom] (wal z (wim (weq z c) target)) :=
    hu.forallMP z (.closed (.all z hs))
  exact (Context.existsElim z hv ht (.closed (fromCore (.r1 z c)))).deduction.empty

def membershipInstanceRight (a z c : Nat) (hza : z ≠ a) (hzc : z ≠ c) :
    Proof (wim (wal z (wel a z)) (wel a c)) := by
  have hr : Proof (wim (weq z c) (wim (wel a z) (wel a c))) := by
    simpa only [M6.Source.ActualAXCode.rho3,M6.Source.AXCode.wim,
      M6.Source.AXCode.weq,M6.Source.AXCode.wel,wim,weq,wel] using Proof.r3 z c a
  exact specializeWithEquality z c _ _ (membershipVacuity a c z hza hzc) hr

def membershipInstanceLeft (a z c : Nat) (hza : z ≠ a) (hzc : z ≠ c) :
    Proof (wim (wal z (wel z a)) (wel c a)) := by
  have hr : Proof (wim (weq z c) (wim (wel z a) (wel c a))) := by
    simpa only [M6.Source.ActualAXCode.rho5,M6.Source.AXCode.wim,
      M6.Source.AXCode.weq,M6.Source.AXCode.wel,wim,weq,wel] using Proof.r5 c a z
  exact specializeWithEquality z c _ _ (membershipVacuity c a z hzc hza) hr

#print axioms membershipInstanceRight
#print axioms membershipInstanceLeft
end M6.PA.NativeCalculus.ActualBasis

