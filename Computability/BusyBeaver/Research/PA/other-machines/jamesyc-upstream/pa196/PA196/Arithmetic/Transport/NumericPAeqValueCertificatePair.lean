module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueCertificateComposition
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic


/-! Parallel composition of two supplied source implications, retaining
exact caller labels after paying all intermediate formula budgets. -/
namespace PA196.Arithmetic.Transport.NumericPAeqValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Numeric PA196.Arithmetic.Checker
open PA196.Arithmetic.Certificates.Dominated ActualCertificateEquivalence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

theorem source_implication_pair (a b c g lo z : V)
    (ha:IsFormula L a) (hb:IsFormula L b) (hc:IsFormula L c)
    (hgoal:FormulaCovered 0 g lo z (imp L a (qqAnd b c)))
    (hab:∀g lo z : V, FormulaCovered 0 g lo z (imp L a b) →
      ∃code,verifyValue code=translate (parameters 0 g lo z) (imp L a b)+1)
    (hac:∀g lo z : V, FormulaCovered 0 g lo z (imp L a c) →
      ∃code,verifyValue code=translate (parameters 0 g lo z) (imp L a c)+1) :
    ∃code,verifyValue code=translate (parameters 0 g lo z) (imp L a (qqAnd b c))+1 := by
  let d := max (imp L a b) (max (imp L a c) (imp L a (qqAnd b c)))
  have he := padded_proofEnvironment d g lo z hgoal.1.1
  have cab : FormulaCovered 0 (padEnvironment g d) lo (z+lo+d) (imp L a b) :=
    he.coverage (IsSemiformula.imp.mpr ⟨ha,hb⟩) (le_max_left _ _)
  have cac : FormulaCovered 0 (padEnvironment g d) lo (z+lo+d) (imp L a c) :=
    he.coverage (IsSemiformula.imp.mpr ⟨ha,hc⟩) ((le_max_left _ _).trans (le_max_right _ _))
  let param := parameters 0 (padEnvironment g d) lo (z+lo+d)
  obtain ⟨x,hx⟩ := hab _ _ _ cab
  obtain ⟨y,hy⟩ := hac _ _ _ cac
  obtain ⟨xf,_,hxf,_⟩ := translate_imp_certificates param a b ha.isUFormula hb.isUFormula
  obtain ⟨yf,_,hyf,_⟩ := translate_imp_certificates param a c ha.isUFormula hc.isUFormula
  obtain ⟨_,back,_,hback⟩ := translate_imp_certificates param a (qqAnd b c) ha.isUFormula
    (IsSemiformula.and.mpr ⟨hb,hc⟩).isUFormula
  let left := (⟨x,hx⟩ : Certificate (translate param (imp L a b))).mp ⟨xf,hxf⟩
  let right := (⟨y,hy⟩ : Certificate (translate param (imp L a c))).mp ⟨yf,hyf⟩
  let assume : Context [translate param a] (translate param a) := .assumption (by simp)
  let pair := (assume.mp (.closed left)).andIntro (assume.mp (.closed right))
  have hpair : verifyValue pair.deduction.empty.code=wim (translate param a) (translate param (qqAnd b c))+1 := by
    rw [translate_and _ _ _ hb.isUFormula hc.isUFormula,translationAnd_eq]
    exact pair.deduction.empty.accepted
  let result := (⟨pair.deduction.empty.code,hpair⟩ : Certificate _).mp ⟨back,hback⟩
  exact padded_proof_certificate_readback (imp L a (qqAnd b c)) g lo z d result.code hgoal result.accepted

#print axioms source_implication_pair
end PA196.Arithmetic.Transport.NumericPAeqValueTotality

