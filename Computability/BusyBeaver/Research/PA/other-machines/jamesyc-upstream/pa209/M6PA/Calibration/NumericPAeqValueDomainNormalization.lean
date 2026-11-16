module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateBinaryRequested
@[expose] public section

/-! Actual model-valued logical derivation duplicating a domain conjunct
under an existential. The two predicates retain all free parameters. -/
namespace M6.PA.NumericPAeqValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
variable {T : InternalTheory V L}

noncomputable def duplicateDomain (D P : SF (V:=V) 1) :
    ND.Proof (T:=T) ∅ ((∃¹ (D ⋏ P)) 🡒 (∃¹ (D ⋏ (D ⋏ P)))) := by
  apply ND.impIntro
  let Γ : ND.Seq (V:=V) := insert (∼(∃¹ (D ⋏ P))) ∅
  have h : ND.Proof (T:=T) Γ (∃¹ (D ⋏ P)) := ND.assumption _ (by simp [Γ])
  apply ND.exsElim h
  let C : ND.Seq (V:=V) := insert (∼(D ⋏ P).free) Γ.shift
  have hp : ND.Proof (T:=T) C (D.free ⋏ P.free) := by
    simpa [Bootstrapping.Semiformula.free] using
      ND.assumption (T:=T) (Γ:=C) (D ⋏ P).free (by simp [C])
  have hd := ND.andIntro (ND.andLeft hp) hp
  have he : ND.Proof (T:=T) C (∃¹ (D.shift ⋏ (D.shift ⋏ P.shift))) := by
    apply ND.exsIntro _ (Bootstrapping.Semiterm.fvar 0)
    simpa [Bootstrapping.Semiformula.free] using hd
  simpa using he

variable [V↓[ℒₒᵣ] ⊧* theory]
open ActualCheckerBlueprint RelationalSource.Numeric ActualCertificateEquivalence

theorem duplicateDomain_requested_certificate (D P : SF (V:=V) 1) (g lo z : V)
    (hc:FormulaCovered 0 g lo z (((∃¹ (D ⋏ P)) 🡒 (∃¹ (D ⋏ (D ⋏ P)))).val)) :
    ∃code,verifyValue code=translate (parameters 0 g lo z)
      (((∃¹ (D ⋏ P)) 🡒 (∃¹ (D ⋏ (D ⋏ P)))).val)+1 := by
  apply singleton_requested_certificate (⊤ : SF (V:=V) 0) _
    (ND.up (duplicateDomain (T:=(∅:Theory L).internalize V) D P) ⊤) g lo z hc
  intro g lo z _
  have h := (truthCertificate (V:=V)).accepted
  exact ⟨(truthCertificate (V:=V)).code,by simpa [translate_verum] using h⟩

#print axioms duplicateDomain
#print axioms duplicateDomain_requested_certificate
end M6.PA.NumericPAeqValueTotality

