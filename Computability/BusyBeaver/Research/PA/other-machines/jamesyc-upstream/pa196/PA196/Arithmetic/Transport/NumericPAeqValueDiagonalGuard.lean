module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueSourceProjections
public import PA196.Arithmetic.Transport.NumericPAeqIsoReflexivityCertificate
public import M6PA.Calibration.NumericPAeqValueIsoGuardValidity
public import M6PA.Calibration.NumericPAeqValueDomainGuardValidity
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqValueCoherence

namespace PA196.Arithmetic.Transport.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def diagonalGuardCode (env count:V):V :=
  imp language (NumericPAeqValueDomainGuard.guard env count) (NumericPAeqValueIsoGuard.guard env env count)
def DiagonalSupply (count:V):Prop := ∀env:V,(∀i<count,IsSemiterm language 0 (nth env i)) → ∀native lo z:V,
  RelationalSource.Numeric.FormulaCovered 0 native lo z (diagonalGuardCode env count) →
  ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
    (diagonalGuardCode env count)+1

theorem diagonal_zero_supply : DiagonalSupply (V:=V) 0 := by
  intro env h native lo z hc
  simpa [diagonalGuardCode] using source_identity_certificate (RelationalSource.Numeric.parameters 0 native lo z) (qqVerum:V) (by simp)

theorem diagonal_successor_supply (count:V) (ih:DiagonalSupply (V:=V) count):DiagonalSupply (V:=V) (count+1) := by
  intro env h native lo z hc
  have hprev : ∀i<count,IsSemiterm language 0 (nth env i) := fun i hi => h i (lt_trans hi (lt_add_one count))
  have hx := h count (lt_add_one count)
  have hA := NumericPAeqValueDomainGuard.guard_isSemiformula env count 0 hprev
  have hB := NumericPAeqValueIsoGuard.guard_isSemiformula env env count 0 (fun i hi => ⟨hprev i hi,hprev i hi⟩)
  have hD := domainCode_isSemiformula hx
  have hI := NumericPAeqValueIsoGuard.isoCode_isSemiformula hx hx
  rw [diagonalGuardCode,NumericPAeqValueDomainGuard.guard_succ,NumericPAeqValueIsoGuard.guard_succ] at hc ⊢
  apply source_implication_pair _ _ _ native lo z (IsSemiformula.and.mpr ⟨hA,hD⟩) hB hI hc
  · intro native lo z hc
    apply source_implication_compose _ (NumericPAeqValueDomainGuard.guard env count) _ native lo z
      (IsSemiformula.and.mpr ⟨hA,hD⟩) hA hB hc
    · intro native lo z _
      exact source_conjunction_projection (RelationalSource.Numeric.parameters 0 native lo z) _ _ hA.isUFormula hD.isUFormula true
    · intro native lo z hc; exact ih env hprev native lo z hc
  · intro native lo z hc
    apply source_implication_compose _ (domainCode (nth env count)) _ native lo z
      (IsSemiformula.and.mpr ⟨hA,hD⟩) hD hI hc
    · intro native lo z _
      exact source_conjunction_projection (RelationalSource.Numeric.parameters 0 native lo z) _ _ hA.isUFormula hD.isUFormula false
    · intro native lo z hc; exact isoReflexivity_requested_certificate _ native lo z hx hc
#print axioms diagonal_zero_supply
#print axioms diagonal_successor_supply
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence
