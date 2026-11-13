module
public import M6PA.Theory
public import M6PA.Scheduler.ActualBasis
@[expose] public section

/-! First concrete atomic obligation for a possible equality-free image:
membership vacuity has a finite proof in the literal actual basis. This does
not supply equality vacuity, equality elimination, or a PA interpretation. -/
namespace M6.PA.NativeCalculus.ActualCore

def negatedImplicationLeft (a b : Nat) : Proof (wim (wn (wim a b)) a) := by
  let hp : Context [a,wn a,wn (wim a b)] a := .assumption (by simp)
  let hn : Context [a,wn a,wn (wim a b)] (wn a) := .assumption (by simp)
  let hab : Context [wn a,wn (wim a b)] (wim a b) :=
    ((Context.mp hp hn).explosion b).deduction
  let hnot : Context [wn a,wn (wim a b)] (wn (wim a b)) := .assumption (by simp)
  exact (Context.mp hab hnot).deduction.dne.deduction.empty

end M6.PA.NativeCalculus.ActualCore

namespace M6.PA.NativeCalculus.ActualBasis
open M6.Source

def membershipVacuity (a b c : Nat) (ha : c ≠ a) (hb : c ≠ b) :
    Proof (wim (wel a b) (wal c (wel a b))) := by
  have raw : ActualAXCode.bundle a b c =
      wn (wim (wim (wel a b) (wal c (wel a b)))
        (AXCode.wal c (AXCode.wim (ActualAXCode.separation a b c)
          (AXCode.wn (ActualAXCode.point a b c))))) := by
    simp only [ActualAXCode.bundle,ActualAXCode.memVac,AXCode.wn,AXCode.wim,
      AXCode.wal,AXCode.wel,wn,wim,wal,wel]
  exact .mp (raw ▸ Proof.bundle a b c ha hb)
    (fromCore (ActualCore.negatedImplicationLeft _ _))

#print axioms membershipVacuity
end M6.PA.NativeCalculus.ActualBasis
