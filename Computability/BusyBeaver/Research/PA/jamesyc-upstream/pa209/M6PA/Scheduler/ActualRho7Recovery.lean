module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualModal
@[expose] public section
open M6.Arithmetic.PA

/-! Noncircular recovery of ordinary equality reflexivity and plain rho7
from the ACTUAL quantified rho7. Every term inhabits the new actual-only
Proof datatype. Its only leaves are R1/R2/R6/actual-R7/dominated-R8;
there is no historical rho7 or arbitrary equality-vacuity constructor.
Arbitrary-label equality-vacuity and full reverse calibration remain OPEN. -/
namespace M6.PA.NativeCalculus.ActualCore

def actualReflexivity (a : Nat) : Proof (weq a a) := by
  let k := wel a a
  let h : Context [weq k a] (weq k a) := .assumption (by simp)
  let hp : Proof (wim (weq k a) (wal k (weq a a))) :=
    (Context.mp h (.mp h (.closed (.r7 a a k)))).deduction.empty
  let hex : Proof (wex k (wal k (weq a a))) :=
    .mp (.r1 k a) (existentialMonotonicity k hp)
  exact .mp hex (.r6 k (weq a a))

/-- This is the special numeric label supplied by actualR7 itself, not an
assumed arbitrary fresh-label equality-vacuity schema. -/
def actualSpecialVacuity (a b : Nat) :
    Proof (wim (weq a b) (wal (wel a b) (weq a b))) :=
  .mp (actualReflexivity a) (.r7 a b a)

/-- The quantifier stripping precondition is paid by an actual finite proof
of special-label vacuity. No historical Named universal-instance lemma. -/
def actualEqualityStrip (a b : Nat) :
    Proof (wim (wal (wel a b) (weq a b)) (weq a b)) := by
  let k := wel a b
  let h : Context [wal k (weq a b)] (wal k (weq a b)) := .assumption (by simp)
  let himp : Context [wal k (weq a b)] (wal k (wim (weq k a) (weq a b))) :=
    h.forallMP k (.closed (.all k (Dominated.k (weq a b) (weq k a))))
  exact (Context.existsElim k (actualSpecialVacuity a b) himp (.closed (.r1 k a))).deduction.empty

def actualPlainRho7 (a b c : Nat) : Proof (rho7 a b c) := by
  let hab : Context [weq a c,weq a b] (weq a b) := .assumption (by simp)
  let hac : Context [weq a c,weq a b] (weq a c) := .assumption (by simp)
  let hall : Context [weq a c,weq a b] (wal (wel b c) (weq b c)) :=
    .mp hac (.mp hab (.closed (.r7 b c a)))
  exact (Context.mp hall (.closed (actualEqualityStrip b c))).deduction.deduction.empty

#print axioms actualReflexivity
#print axioms actualSpecialVacuity
#print axioms actualEqualityStrip
#print axioms actualPlainRho7
end M6.PA.NativeCalculus.ActualCore

