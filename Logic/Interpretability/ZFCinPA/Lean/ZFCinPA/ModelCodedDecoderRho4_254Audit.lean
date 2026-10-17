import ZFCinPA.ModelCodedDecoderRho4_254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoderRho4_254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open _root_.SetTheory.BusyBeaver.ZFC
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho4_254.namedFormula_twice
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho4_254.doubleBody_swap
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho4_254.namedAll_commutes
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho4_254.decoded_rho4_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho4_254.decoded_rho4_provable
example (T : Theory ℒₛₑₜ) [T.Δ₁] (a b c : V) :
    Provable T (decode (ArithmeticTemplates254.rho4 a b c)) := decoded_rho4_provable T a b c
example (a b c : V) : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticTemplates254.rho4 a b c)) := decoded_rho4_provable 𝗭𝗙 a b c
example (a b c : V) : Provable (𝗭𝗙𝗖 : SetTheory)
    (decode (ArithmeticTemplates254.rho4 a b c)) := decoded_rho4_provable 𝗭𝗙𝗖 a b c
example (a c : V) : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticTemplates254.rho4 a a c)) := decoded_rho4_provable 𝗭𝗙 a a c
example : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticTemplates254.rho4 (0 : V) 0 0)) := decoded_rho4_provable 𝗭𝗙 0 0 0
example (T : Theory ℒₛₑₜ) [T.Δ₁] (a b : V) (p : Formula V ℒₛₑₜ) :
    T.internalize V ⊢ namedFormula a (namedFormula b p) 🡒 namedFormula b (namedFormula a p) :=
  namedAll_commutes T a b p
example (a b : V) (hab : a ≠ b) (p : Formula V ℒₛₑₜ) :
    (doubleBody a b p).subst ![Semiterm.bvar 1,Semiterm.bvar 0] = doubleBody b a p :=
  doubleBody_swap a b hab p
example (a b c : V) : ∃ d : V, Proof (𝗭𝗙 : SetTheory) d
    (decode (ArithmeticTemplates254.rho4 a b c)) := decoded_rho4_provable 𝗭𝗙 a b c
