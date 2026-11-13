module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedFixedCertificateSeeds
public import M6PA.Calibration.FoundationRelationalCodeAgreement
@[expose] public section
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Ordinal (Term Formula)

theorem closed_interpreted_no_free (p : SourceFormula 0) (hp : p.freeVariables=∅)
    (f : Nat → Term 0) (i : Nat) : ¬(formula p Fin.elim0 f).FVar? i := by
  intro hi
  rw [formula_env_closed_source p hp f (fun j => (.fvar j : Term 0))] at hi
  have h := canonical_formula_support p i hi
  simpa [Semiformula.FVar?,hp] using h

theorem fixedImageSeed_translate (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms)
    (b f : Nat) :
    Numeric.translate (Numeric.parameters b f 1 (fixedImageReserve p hp))
      (⌜formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0))⌝ : Nat)=fixedImageNativeCode p hp := by
  rw [Numeric.translate_quote]
  unfold fixedImageNativeCode code
  apply congrArg (NativeCalculus.ActualBasis.relationalCode (fixedImageReserve p hp))
  apply Numeric.toNamed_agree
  · intro i; exact Fin.elim0 i
  · intro i hi
    exact False.elim (closed_interpreted_no_free p (fixedAxiom_freeVariables p hp) _ i hi)

#print axioms closed_interpreted_no_free
#print axioms fixedImageSeed_translate
end M6.PA.ForwardRelational

