module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSequentGuardedLogic
@[expose] public section

/-! Guard-preserving closures for the literal HFS conjunction, disjunction,
and cut premises. The guard is an arbitrary native formula code and remains
on every accepted implication. -/
namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint
open RelationalSource.Numeric (translate nativeOr translate_and translate_or translationAnd_eq
  translationOr_eq orLeft orRight)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem guarded_insert_disjunction (native param s p guard code : V)
    (hs : SupportedSet param s) (hp : SupportedFormulaCovered 0 0 param p)
    (hc : verifyValue code=wim guard (translate native (sequentCode param (insert p s)))+1) :
    ∃ out, verifyValue out=wim guard
      (nativeOr (translate native (formulaSyntax param p)) (translate native (sequentCode param s)))+1 := by
  obtain ⟨arrow,ha⟩ := insert_forward_certificate native param s p hs hp
  let out := implicationCompose (⟨code,hc⟩ : Certificate
    (wim guard (translate native (sequentCode param (insert p s))))) ⟨arrow,ha⟩
  exact ⟨out.code,out.accepted⟩

theorem guarded_and_certificate (native param s p q guard dp dq : V)
    (hs : SupportedSet param s) (hm : qqAnd p q∈s)
    (hdp : verifyValue dp=wim guard (translate native (sequentCode param (insert p s)))+1)
    (hdq : verifyValue dq=wim guard (translate native (sequentCode param (insert q s)))+1) :
    ∃ code, verifyValue code=wim guard (translate native (sequentCode param s))+1 := by
  have hc := supported_coverage_and (hs _ hm)
  obtain ⟨left,hl⟩ := guarded_insert_disjunction native param s p guard dp hs hc.1 hdp
  obtain ⟨right,hr⟩ := guarded_insert_disjunction native param s q guard dq hs hc.2 hdq
  obtain ⟨arrow,ha⟩ := member_certificate native param s (qqAnd p q) hs hm
  rw [formulaSyntax_and _ _ _ hc.1.2.1.isUFormula hc.2.2.1.isUFormula,
    translate_and _ _ _ (formulaSyntax_supported_isSemiformula hc.1).isUFormula
      (formulaSyntax_supported_isSemiformula hc.2).isUFormula,translationAnd_eq] at ha
  let out := guardedConjunctionSequent (⟨left,hl⟩ : Certificate
    (wim guard (nativeOr (translate native (formulaSyntax param p)) (translate native (sequentCode param s)))))
    (⟨right,hr⟩ : Certificate
      (wim guard (nativeOr (translate native (formulaSyntax param q)) (translate native (sequentCode param s)))))
    ⟨arrow,ha⟩
  exact ⟨out.code,out.accepted⟩

theorem guarded_or_certificate (native param s p q guard child : V)
    (hs : SupportedSet param s) (hm : qqOr p q∈s)
    (hd : verifyValue child=wim guard (translate native (sequentCode param (insert p (insert q s))))+1) :
    ∃ code, verifyValue code=wim guard (translate native (sequentCode param s))+1 := by
  have hc := supported_coverage_or (hs _ hm)
  obtain ⟨arrow,ha⟩ := member_certificate native param s (qqOr p q) hs hm
  rw [formulaSyntax_or _ _ _ hc.1.2.1.isUFormula hc.2.2.1.isUFormula,
    translate_or _ _ _ (formulaSyntax_supported_isSemiformula hc.1).isUFormula
      (formulaSyntax_supported_isSemiformula hc.2).isUFormula,translationOr_eq] at ha
  let toS : Certificate (wim (nativeOr (translate native (formulaSyntax param p))
    (translate native (formulaSyntax param q))) (translate native (sequentCode param s))) := ⟨arrow,ha⟩
  obtain ⟨fold,hfold⟩ := sequent_eliminate_certificate native param (insert p (insert q s))
    (translate native (sequentCode param s)) ((hs.insert hc.2).insert hc.1) (by
      intro r hr
      rcases (show r=p ∨ r=q ∨ r∈s from by simpa using hr) with he | he | hm
      · subst r
        let out := implicationCompose (orLeft (translate native (formulaSyntax param p))
          (translate native (formulaSyntax param q))) toS
        exact ⟨out.code,out.accepted⟩
      · subst r
        let out := implicationCompose (orRight (translate native (formulaSyntax param p))
          (translate native (formulaSyntax param q))) toS
        exact ⟨out.code,out.accepted⟩
      · exact member_certificate native param s r hs hm)
  let out := implicationCompose (⟨child,hd⟩ : Certificate
    (wim guard (translate native (sequentCode param (insert p (insert q s)))))) ⟨fold,hfold⟩
  exact ⟨out.code,out.accepted⟩

theorem guarded_cut_certificate (native param s p guard dp dn : V)
    (hs : SupportedSet param s) (hp : SupportedFormulaCovered 0 0 param p)
    (hn : SupportedFormulaCovered 0 0 param (neg Presentation.language p))
    (hdp : verifyValue dp=wim guard (translate native (sequentCode param (insert p s)))+1)
    (hdn : verifyValue dn=wim guard
      (translate native (sequentCode param (insert (neg Presentation.language p) s)))+1) :
    ∃ code, verifyValue code=wim guard (translate native (sequentCode param s))+1 := by
  obtain ⟨left,hl⟩ := guarded_insert_disjunction native param s p guard dp hs hp hdp
  obtain ⟨right,hr⟩ := guarded_insert_disjunction native param s (neg Presentation.language p) guard dn hs hn hdn
  obtain ⟨forward,backward,hforward,hbackward⟩ := interpreted_negation_certificates native param p hp
  let out := guardedCutSequent (⟨left,hl⟩ : Certificate
    (wim guard (nativeOr (translate native (formulaSyntax param p)) (translate native (sequentCode param s)))))
    (⟨right,hr⟩ : Certificate (wim guard (nativeOr
      (translate native (formulaSyntax param (neg Presentation.language p))) (translate native (sequentCode param s)))))
    ⟨forward,hforward⟩
  exact ⟨out.code,out.accepted⟩

theorem guarded_weakening_certificate (native param s t guard child : V)
    (hs : SupportedSet param s) (ht : SupportedSet param t) (hst : s⊆t)
    (hc : verifyValue child=wim guard (translate native (sequentCode param s))+1) :
    ∃ code, verifyValue code=wim guard (translate native (sequentCode param t))+1 := by
  obtain ⟨arrow,ha⟩ := sequent_weakening_certificate native param s t hs ht hst
  let out := implicationCompose (⟨child,hc⟩ : Certificate
    (wim guard (translate native (sequentCode param s)))) ⟨arrow,ha⟩
  exact ⟨out.code,out.accepted⟩

theorem guarded_identity_certificate (native param s p guard : V) (hs : SupportedSet param s)
    (hm : p∈s) (hn : neg Presentation.language p∈s) :
    ∃ code, verifyValue code=wim guard (translate native (sequentCode param s))+1 := by
  obtain ⟨code,hc⟩ := sequent_identity_certificate native param s p hs hm hn
  let out := (Context.closed (Γ:=[guard]) (⟨code,hc⟩ : Certificate
    (translate native (sequentCode param s)))).deduction.empty
  exact ⟨out.code,out.accepted⟩

theorem guarded_verum_certificate (native param s guard : V) (hs : SupportedSet param s)
    (hm : qqVerum∈s) :
    ∃ code, verifyValue code=wim guard (translate native (sequentCode param s))+1 := by
  obtain ⟨code,hc⟩ := sequent_verum_certificate native param s hs hm
  let out := (Context.closed (Γ:=[guard]) (⟨code,hc⟩ : Certificate
    (translate native (sequentCode param s)))).deduction.empty
  exact ⟨out.code,out.accepted⟩

#print axioms guarded_weakening_certificate
#print axioms guarded_identity_certificate
#print axioms guarded_verum_certificate
#print axioms guarded_insert_disjunction
#print axioms guarded_and_certificate
#print axioms guarded_or_certificate
#print axioms guarded_cut_certificate
end M6.PA.NumericPAeqFormula.Sequent

