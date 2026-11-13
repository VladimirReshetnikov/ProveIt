module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaQuantifierTemplatesCode
public import M6PA.Calibration.NumericPAeqFormulaOpeningLogic
public import M6PA.Calibration.NumericPAeqSourceCertificateMP
public import M6PA.Calibration.FoundationRelationalSequentRequestedUniversal
@[expose] public section
namespace M6.PA.NumericPAeqFormulaLogical
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqFormulaQuantifierTemplates
open NumericPAeqValueTotality RelationalSource.Numeric ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def universalCurry (H:SF (V:=V) 0) (P:SF (V:=V) 1):
    ND.Proof (T:=(∅:Theory L).internalize V) ∅ ((∀¹ (liftClosed H 🡒 P)) 🡒 (H 🡒 ∀¹ P)) := by
  apply ND.impIntro
  apply ND.impIntro
  let C:ND.Seq (V:=V) := insert (∼H) (insert (∼(∀¹ (liftClosed H 🡒 P))) ∅)
  have h:ND.Proof (T:=(∅:Theory L).internalize V) C (∀¹ (liftClosed H 🡒 P)) := ND.assumption _ (by simp [C])
  have hh:ND.Proof (T:=(∅:Theory L).internalize V) C H := ND.assumption _ (by simp [C])
  apply ND.allIntro
  let t:ST (V:=V) 0 := Semiterm.fvar 0
  have hall : ND.Proof (T:=(∅:Theory L).internalize V) C.shift (∀¹ (liftClosed H.shift 🡒 P.shift)) := by simpa using ND.shift h
  have hs : ND.Proof (T:=(∅:Theory L).internalize V) C.shift (H.shift 🡒 P.free) := by
    simpa [Bootstrapping.Semiformula.free,t] using ND.allElim hall t
  exact ND.mp (ND.shift hh) hs
variable [V↓[ℒₒᵣ] ⊧* theory]
theorem universalCurry_requested_certificate (H P native lo z:V)
    (hH:IsFormula L H) (hP:IsSemiformula L 1 P)
    (hc:FormulaCovered 0 native lo z (imp L (qqAll (imp L H P)) (imp L H (qqAll P)))):
    ∃code,verifyValue code=translate (parameters 0 native lo z)
      (imp L (qqAll (imp L H P)) (imp L H (qqAll P)))+1 := by
  let HH:SF (V:=V) 0 := ⟨H,hH⟩
  let PP:SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  have he : ((∀¹ (liftClosed HH 🡒 PP)) 🡒 (HH 🡒 ∀¹ PP)).val=
      imp L (qqAll (imp L H P)) (imp L H (qqAll P)) := by
    simp only [Bootstrapping.Semiformula.val_imp,Bootstrapping.Semiformula.val_all,liftClosed_val,HH,PP]
  rw [←he] at hc ⊢
  exact empty_requested_certificate _ (universalCurry HH PP) native lo z hc
theorem guarded_universal_certificate (H P native lo z:V)
    (hH:IsFormula L H) (hP:IsSemiformula L 1 P)
    (hc:FormulaCovered 0 native lo z (imp L H (qqAll P)))
    (child:∀g l r:V,FormulaCovered 0 g l r (imp L (shift L H) (free L P))→
      ∃code,verifyValue code=translate (parameters 0 g l r) (imp L (shift L H) (free L P))+1):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (imp L H (qqAll P))+1 := by
  have hH1 : IsSemiformula L 1 H := ⟨hH.isUFormula,le_trans hH.bv_le (by simp)⟩
  have hM : IsSemiformula L 1 (imp L H P) := IsSemiformula.imp.mpr ⟨hH1,hP⟩
  apply source_certificate_mp (qqAll (imp L H P)) (imp L H (qqAll P)) native lo z
    (IsSemiformula.all.mpr (by simpa using hM))
    (IsSemiformula.imp.mpr ⟨hH,IsSemiformula.all.mpr (by simpa using hP)⟩) hc
  · intro native lo z hc
    apply requested_universal_certificate _ native lo z hM hc
    intro g l r hc
    rw [NumericPAeqFormulaRealization.free_imp_code hH1 hP,NumericPAeqFormulaRealization.free_zero_arity hH] at hc ⊢
    exact child g l r hc
  · intro g l r hc
    exact universalCurry_requested_certificate H P g l r hH hP hc
#print axioms universalCurry
#print axioms universalCurry_requested_certificate
#print axioms guarded_universal_certificate
end M6.PA.NumericPAeqFormulaLogical

