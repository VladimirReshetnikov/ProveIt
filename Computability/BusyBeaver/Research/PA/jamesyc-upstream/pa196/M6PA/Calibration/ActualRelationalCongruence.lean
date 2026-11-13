module
public import M6PA.Theory
public import M6PA.Calibration.ActualRelationalInstance
@[expose] public section

/-! Both membership-argument congruence tests for the explicit neighborhood
equality replacement. Fresh representative labels are explicit hypotheses.
This is not a proof of the full PA interpretation or induction suppliers. -/
namespace M6.PA.NativeCalculus.ActualBasis

def primitiveSymmetry (a b : Nat) : Proof (wim (weq a b) (weq b a)) := by
  let h : Context [weq a b] (weq a b) := .assumption (by simp)
  exact (Context.mp (.closed (fromCore (ActualCore.actualReflexivity a)))
    (.mp h (.closed (fromCore (ActualCore.actualPlainRho7 a b a))))).deduction.empty

def memRightRewrite (a z c : Nat) : Proof (wim (weq z c) (wim (wel a z) (wel a c))) := by
  simpa only [M6.Source.ActualAXCode.rho3,M6.Source.AXCode.wim,
    M6.Source.AXCode.weq,M6.Source.AXCode.wel,wim,weq,wel] using Proof.r3 z c a

def memLeftRewrite (a z c : Nat) : Proof (wim (weq z c) (wim (wel z a) (wel c a))) := by
  simpa only [M6.Source.ActualAXCode.rho5,M6.Source.AXCode.wim,
    M6.Source.AXCode.weq,M6.Source.AXCode.wel,wim,weq,wel] using Proof.r5 c a z

def implicationRewrite (p q p' q' e e' : Nat)
    (hs : Proof (wim e e')) (hp : Proof (wim e' (wim p' p)))
    (hq : Proof (wim e (wim q q'))) :
    Proof (wim e (wim (wim p q) (wim p' q'))) := by
  let he : Context [p',wim p q,e] e := .assumption (by simp)
  let hpp : Context [p',wim p q,e] p' := .assumption (by simp)
  let hi : Context [p',wim p q,e] (wim p q) := .assumption (by simp)
  let hpa : Context [p',wim p q,e] p := .mp hpp (.mp (.mp he (.closed hs)) (.closed hp))
  exact (Context.mp (.mp hpa hi) (.mp he (.closed hq))).deduction.deduction.deduction.empty

def universalMembershipImplicationRight (a b z c : Nat)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    Proof (wim (wal z (wim (wel a z) (wel b z))) (wim (wel a c) (wel b c))) :=
  specializeWithEquality z c _ _
    (implicationVacuity z _ _ (membershipVacuity a c z hza hzc)
      (membershipVacuity b c z hzb hzc))
    (implicationRewrite _ _ _ _ _ _ (primitiveSymmetry z c)
      (memRightRewrite a c z) (memRightRewrite b z c))

def universalMembershipImplicationLeft (a b z c : Nat)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    Proof (wim (wal z (wim (wel z a) (wel z b))) (wim (wel c a) (wel c b))) :=
  specializeWithEquality z c _ _
    (implicationVacuity z _ _ (membershipVacuity c a z hzc hza)
      (membershipVacuity c b z hzc hzb))
    (implicationRewrite _ _ _ _ _ _ (primitiveSymmetry z c)
      (memLeftRewrite a c z) (memLeftRewrite b z c))

def forallIffForward (z p q : Nat) :
    Proof (wim (wal z (iffCode p q)) (wal z (wim p q))) := by
  let hp : Context [iffCode p q] (wa (wim p q) (wim q p)) := .assumption (by simp [iffCode])
  let proj : Proof (wim (iffCode p q) (wim p q)) := hp.andLeft.deduction.empty
  exact .mp (.all z proj) (r2 z _ _)

def neighborhoodRightCongruence (a b z c : Nat)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    Proof (wim (neighborhoodEquality a b z) (wim (wel a c) (wel b c))) := by
  let h : Context [neighborhoodEquality a b z] (neighborhoodEquality a b z) := .assumption (by simp)
  let hi := Context.mp h.andLeft (.closed (forallIffForward z (wel a z) (wel b z)))
  exact (Context.mp hi (.closed (universalMembershipImplicationRight a b z c hza hzb hzc))).deduction.empty

def neighborhoodLeftCongruence (a b z c : Nat)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    Proof (wim (neighborhoodEquality a b z) (wim (wel c a) (wel c b))) := by
  let h : Context [neighborhoodEquality a b z] (neighborhoodEquality a b z) := .assumption (by simp)
  let hi := Context.mp h.andRight (.closed (forallIffForward z (wel z a) (wel z b)))
  exact (Context.mp hi (.closed (universalMembershipImplicationLeft a b z c hza hzb hzc))).deduction.empty

#print axioms neighborhoodRightCongruence
#print axioms neighborhoodLeftCongruence
end M6.PA.NativeCalculus.ActualBasis

