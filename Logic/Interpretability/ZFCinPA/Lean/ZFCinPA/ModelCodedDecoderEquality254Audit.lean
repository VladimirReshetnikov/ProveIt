import ZFCinPA.ModelCodedDecoderEquality254
set_option autoImplicit false
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderEquality254
open _root_.SetTheory.BusyBeaver.ZFC
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderEquality254.decoded_weq
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderEquality254.decoded_wel
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderEquality254.rho7Template
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderEquality254.decoded_rho7_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderEquality254.decoded_rho7_provable
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderEquality254.rho5Template
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderEquality254.decoded_rho5_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderEquality254.decoded_rho5_provable
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderEquality254.rho3Template
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderEquality254.decoded_rho3_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderEquality254.decoded_rho3_provable
example (a b c : V) : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticTemplates254.rho7 a b c)) := decoded_rho7_provable (𝗭𝗙 : SetTheory) a b c
example (a b c : V) : Provable (𝗭𝗙𝗖 : SetTheory)
    (decode (ArithmeticTemplates254.rho7 a b c)) := decoded_rho7_provable (𝗭𝗙𝗖 : SetTheory) a b c
example : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticTemplates254.rho7 (0 : V) 0 0)) := decoded_rho7_provable (𝗭𝗙 : SetTheory) 0 0 0
example (a b : V) : ∃ d : V, Proof (𝗭𝗙𝗖 : SetTheory) d
    (decode (ArithmeticTemplates254.rho7 a b a)) := decoded_rho7_provable (𝗭𝗙𝗖 : SetTheory) a b a
example (a b c : V) : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticTemplates254.rho5 a b c)) := decoded_rho5_provable (𝗭𝗙 : SetTheory) a b c
example (a b c : V) : Provable (𝗭𝗙𝗖 : SetTheory)
    (decode (ArithmeticTemplates254.rho5 a b c)) := decoded_rho5_provable (𝗭𝗙𝗖 : SetTheory) a b c
example : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticTemplates254.rho5 (0 : V) 0 0)) := decoded_rho5_provable (𝗭𝗙 : SetTheory) 0 0 0
example (a b : V) : ∃ d : V, Proof (𝗭𝗙𝗖 : SetTheory) d
    (decode (ArithmeticTemplates254.rho5 a b a)) := decoded_rho5_provable (𝗭𝗙𝗖 : SetTheory) a b a
example (a b c : V) : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticTemplates254.rho3 a b c)) := decoded_rho3_provable (𝗭𝗙 : SetTheory) a b c
example (a b c : V) : Provable (𝗭𝗙𝗖 : SetTheory)
    (decode (ArithmeticTemplates254.rho3 a b c)) := decoded_rho3_provable (𝗭𝗙𝗖 : SetTheory) a b c
example : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticTemplates254.rho3 (0 : V) 0 0)) := decoded_rho3_provable (𝗭𝗙 : SetTheory) 0 0 0
example (a b : V) : ∃ d : V, Proof (𝗭𝗙𝗖 : SetTheory) d
    (decode (ArithmeticTemplates254.rho3 a b a)) := decoded_rho3_provable (𝗭𝗙𝗖 : SetTheory) a b a
