module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSequentRequestedLift
public import M6PA.Calibration.NumericPAeqSequentGuardedPropositional
@[expose] public section
namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open NumericPAeqInductionInterpretation
open RelationalSource.Numeric (translate)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem and_rule_requested {f s p q : V} (hf : IsSemitermVec language (len f) 0 f)
    (hs : SupportedSet (parameters 0 f) s) (hm : qqAnd p q∈s)
    (left : RequestedCertificate f (insert p s)) (right : RequestedCertificate f (insert q s)) :
    RequestedCertificate f s := by
  have h := supported_coverage_and (hs _ hm)
  apply requested_binary_lift hf hs (hs.insert h.1) (hs.insert h.2) left right
  intro param a b ha hb
  exact guarded_and_certificate param (parameters 0 f) s p q (translate param (freeDomain f)) a b hs hm ha hb

theorem or_rule_requested {f s p q : V} (hf : IsSemitermVec language (len f) 0 f)
    (hs : SupportedSet (parameters 0 f) s) (hm : qqOr p q∈s)
    (child : RequestedCertificate f (insert p (insert q s))) : RequestedCertificate f s := by
  have h := supported_coverage_or (hs _ hm)
  have ht := (hs.insert h.2).insert h.1
  apply requested_binary_lift hf hs ht ht child child
  intro param a b ha hb
  exact guarded_or_certificate param (parameters 0 f) s p q (translate param (freeDomain f)) a hs hm ha

theorem cut_rule_requested {f s p : V} (hf : IsSemitermVec language (len f) 0 f)
    (hs : SupportedSet (parameters 0 f) s)
    (hp : SupportedFormulaCovered 0 0 (parameters 0 f) p)
    (hn : SupportedFormulaCovered 0 0 (parameters 0 f) (neg Presentation.language p))
    (left : RequestedCertificate f (insert p s))
    (right : RequestedCertificate f (insert (neg Presentation.language p) s)) : RequestedCertificate f s := by
  apply requested_binary_lift hf hs (hs.insert hp) (hs.insert hn) left right
  intro param a b ha hb
  exact guarded_cut_certificate param (parameters 0 f) s p (translate param (freeDomain f)) a b hs hp hn ha hb

theorem weakening_rule_requested {f s t : V} (hf : IsSemitermVec language (len f) 0 f)
    (hs : SupportedSet (parameters 0 f) s) (ht : SupportedSet (parameters 0 f) t)
    (hst : s⊆t) (child : RequestedCertificate f s) : RequestedCertificate f t := by
  apply requested_binary_lift hf ht hs hs child child
  intro param a b ha hb
  exact guarded_weakening_certificate param (parameters 0 f) s t (translate param (freeDomain f)) a hs ht hst ha

#print axioms and_rule_requested
#print axioms or_rule_requested
#print axioms cut_rule_requested
#print axioms weakening_rule_requested
end M6.PA.NumericPAeqFormula.Sequent

