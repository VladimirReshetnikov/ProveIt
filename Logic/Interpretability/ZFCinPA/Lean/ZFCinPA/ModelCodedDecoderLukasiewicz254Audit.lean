import ZFCinPA.ModelCodedDecoderLukasiewicz254
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (T : Theory ℒₛₑₜ) [T.Δ₁]
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254.decoded_imp_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254.decoded_imp_congr
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254.rho8Template
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254.decoded_rho8_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254.decoded_rho8_provable
example (a b : V) : T.internalize V ⊢ decoded (4*cantor a b) 🡘
    (decoded a 🡒 decoded b) := decoded_imp_equiv T a b
example : (𝗭𝗙 : SetTheory).internalize V ⊢ decoded (0 : V) 🡘
    (decoded (0 : V) 🡒 decoded 0) := by
  simpa [ArithmeticCantor.cantor,ArithmeticCantor.triangle] using
    decoded_imp_equiv (𝗭𝗙 : SetTheory) (0 : V) 0
example (a b : V) (p q : Formula V ℒₛₑₜ)
    (ha : T.internalize V ⊢ decoded a 🡘 p) (hb : T.internalize V ⊢ decoded b 🡘 q) :
    T.internalize V ⊢ decoded (4*cantor a b) 🡘 (p 🡒 q) := decoded_imp_congr T a b p q ha hb
example (a b c u : Formula V ℒₛₑₜ) :
    T.internalize V ⊢! ((c 🡒 u) 🡒 a) 🡒 ((a 🡒 c) 🡒 (b 🡒 c)) := rho8Template T a b c u
example (a b c u : V) : T.internalize V ⊢ decoded (ArithmeticTemplates254.rho8 a b c u) 🡘
    (((decoded c 🡒 decoded u) 🡒 decoded a) 🡒
      ((decoded a 🡒 decoded c) 🡒 (decoded b 🡒 decoded c))) := decoded_rho8_equiv T a b c u
example (a b c u : V) : ∃ d, Proof (𝗭𝗙 : SetTheory) d
    (decode (ArithmeticTemplates254.rho8 a b c u)) := decoded_rho8_provable (𝗭𝗙 : SetTheory) a b c u
example (a b c u : V) : Provable (𝗭𝗙𝗖 : SetTheory)
    (decode (ArithmeticTemplates254.rho8 a b c u)) := decoded_rho8_provable (𝗭𝗙𝗖 : SetTheory) a b c u
example : Provable (𝗭𝗙 : SetTheory) (decode (Code254.rho8 (0 : Nat) 0 0 0)) := by
  simpa only [ArithmeticTemplates254.rho8_nat] using decoded_rho8_provable (𝗭𝗙 : SetTheory) (0 : Nat) 0 0 0
