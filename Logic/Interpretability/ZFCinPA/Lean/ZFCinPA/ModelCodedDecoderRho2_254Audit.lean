import ZFCinPA.ModelCodedDecoderRho2_254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedBindOne
open _root_.SetTheory.BusyBeaver.ZFC
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254.namedBody_imp
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254.namedFormula_mono
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254.namedFormula_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254.decoded_all_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254.decoded_rho2_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254.decoded_rho2_provable_of_gen
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254.zf_decoded_rho2_provable
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254.zfc_decoded_rho2_provable
example (a b c : V) : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticTemplates254.rho2 a b c)) := zf_decoded_rho2_provable a b c
example (a b c : V) : Provable (𝗭𝗙𝗖 : SetTheory)
    (decode (ArithmeticTemplates254.rho2 a b c)) := zfc_decoded_rho2_provable a b c
example : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticTemplates254.rho2 (0 : V) 0 0)) := zf_decoded_rho2_provable 0 0 0
example (b c : V) : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticTemplates254.rho2 (0 : V) b c)) := zf_decoded_rho2_provable 0 b c
example (T : Theory ℒₛₑₜ) [T.Δ₁] (a : V)
    (hGen : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p))
    (p q : Formula V ℒₛₑₜ) (h : T.internalize V ⊢ p 🡒 q) :
    T.internalize V ⊢ namedFormula a p 🡒 namedFormula a q := namedFormula_mono T a hGen p q h
example (T : Theory ℒₛₑₜ) [T.Δ₁] (a : V)
    (hGen : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p))
    (p q : Formula V ℒₛₑₜ) (h : T.internalize V ⊢ p 🡘 q) :
    T.internalize V ⊢ namedFormula a p 🡘 namedFormula a q := namedFormula_equiv T a hGen p q h
example (a b c : V) : ∃ d : V, Proof (𝗭𝗙 : SetTheory) d
    (decode (ArithmeticTemplates254.rho2 a b c)) := zf_decoded_rho2_provable a b c
example (a c : V) : Provable (𝗭𝗙𝗖 : SetTheory)
    (decode (ArithmeticTemplates254.rho2 a a c)) := zfc_decoded_rho2_provable a a c
