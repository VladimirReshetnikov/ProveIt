module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateNeighborhoodPrimitive
@[expose] public section

/-! Guarded native membership specialization and neighborhood congruence. -/
namespace M6.PA.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCheckerBlueprint ActualHeadGraphs
universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]


noncomputable def specializeWithEquality (z c atom target : V)
    (hv : Certificate (wim target (wal z target)))
    (hr : Certificate (wim (weq z c) (wim atom target))) :
    Certificate (wim (wal z atom) target) := by
  let he : Context [weq z c,atom] (weq z c) := .assumption (by simp)
  let ha : Context [weq z c,atom] atom := .assumption (by simp)
  let hs : Certificate (wim atom (wim (weq z c) target)) :=
    (Context.mp ha (.mp he (.closed hr))).deduction.deduction.empty
  let hu : Context [wal z atom] (wal z atom) := .assumption (by simp)
  let ht : Context [wal z atom] (wal z (wim (weq z c) target)) :=
    hu.forallMP z (.closed (.all z hs))
  exact (Context.existsElim z hv ht (.closed (r1 z c))).deduction.empty

noncomputable def primitiveSymmetry (a b : V) : Certificate (wim (weq a b) (weq b a)) := by
  let h : Context [weq a b] (weq a b) := .assumption (by simp)
  exact (Context.mp (.closed (actualReflexivity a))
    (.mp h (.closed (actualPlainRho7 a b a)))).deduction.empty

noncomputable def memRightRewrite (a z c : V) : Certificate (wim (weq z c) (wim (wel a z) (wel a c))) := r3 z c a
noncomputable def memLeftRewrite (a z c : V) : Certificate (wim (weq z c) (wim (wel z a) (wel c a))) := r5 c a z

noncomputable def implicationRewrite (p q p' q' e e' : V)
    (hs : Certificate (wim e e')) (hp : Certificate (wim e' (wim p' p)))
    (hq : Certificate (wim e (wim q q'))) :
    Certificate (wim e (wim (wim p q) (wim p' q'))) := by
  let he : Context [p',wim p q,e] e := .assumption (by simp)
  let hpp : Context [p',wim p q,e] p' := .assumption (by simp)
  let hi : Context [p',wim p q,e] (wim p q) := .assumption (by simp)
  let hpa : Context [p',wim p q,e] p := .mp hpp (.mp (.mp he (.closed hs)) (.closed hp))
  exact (Context.mp (.mp hpa hi) (.mp he (.closed hq))).deduction.deduction.deduction.empty

noncomputable def universalMembershipImplicationRight (a b z c : V)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    Certificate (wim (wal z (wim (wel a z) (wel b z))) (wim (wel a c) (wel b c))) :=
  specializeWithEquality z c _ _
    (implicationVacuity z _ _ (membershipVacuity a c z hza hzc)
      (membershipVacuity b c z hzb hzc))
    (implicationRewrite _ _ _ _ _ _ (primitiveSymmetry z c)
      (memRightRewrite a c z) (memRightRewrite b z c))

noncomputable def universalMembershipImplicationLeft (a b z c : V)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    Certificate (wim (wal z (wim (wel z a) (wel z b))) (wim (wel c a) (wel c b))) :=
  specializeWithEquality z c _ _
    (implicationVacuity z _ _ (membershipVacuity c a z hzc hza)
      (membershipVacuity c b z hzc hzb))
    (implicationRewrite _ _ _ _ _ _ (primitiveSymmetry z c)
      (memLeftRewrite a c z) (memLeftRewrite b z c))

noncomputable def forallIffForward (z p q : V) :
    Certificate (wim (wal z (iffCode p q)) (wal z (wim p q))) := by
  let hp : Context [iffCode p q] (wa (wim p q) (wim q p)) := .assumption (by simp [iffCode])
  let proj : Certificate (wim (iffCode p q) (wim p q)) := hp.andLeft.deduction.empty
  exact .mp (.all z proj) (r2 z _ _)

noncomputable def neighborhoodRightCongruenceCore (a b z c : V)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    Certificate (wim (neighborhoodEquality a b z) (wim (wel a c) (wel b c))) := by
  let h : Context [neighborhoodEquality a b z] (neighborhoodEquality a b z) := .assumption (by simp)
  let hi := Context.mp h.andLeft (.closed (forallIffForward z (wel a z) (wel b z)))
  exact (Context.mp hi (.closed (universalMembershipImplicationRight a b z c hza hzb hzc))).deduction.empty

noncomputable def neighborhoodLeftCongruenceCore (a b z c : V)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    Certificate (wim (neighborhoodEquality a b z) (wim (wel c a) (wel c b))) := by
  let h : Context [neighborhoodEquality a b z] (neighborhoodEquality a b z) := .assumption (by simp)
  let hi := Context.mp h.andRight (.closed (forallIffForward z (wel z a) (wel z b)))
  exact (Context.mp hi (.closed (universalMembershipImplicationLeft a b z c hza hzb hzc))).deduction.empty


noncomputable def neighborhoodRightCongruence (a b z c : V)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    Certificate (wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0)
      (wim (wel a c) (wel b c))) := by
  rw [neighborhood_expr_eq]
  exact neighborhoodRightCongruenceCore a b z c hza hzb hzc

noncomputable def neighborhoodLeftCongruence (a b z c : V)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    Certificate (wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr a b z 0)
      (wim (wel c a) (wel c b))) := by
  rw [neighborhood_expr_eq]
  exact neighborhoodLeftCongruenceCore a b z c hza hzb hzc


#print axioms specializeWithEquality
#print axioms primitiveSymmetry
#print axioms memRightRewrite
#print axioms memLeftRewrite
#print axioms implicationRewrite
#print axioms universalMembershipImplicationRight
#print axioms universalMembershipImplicationLeft
#print axioms forallIffForward
#print axioms neighborhoodRightCongruenceCore
#print axioms neighborhoodLeftCongruenceCore
#print axioms neighborhoodRightCongruence
#print axioms neighborhoodLeftCongruence
end M6.PA.ActualCertificateEquivalence

