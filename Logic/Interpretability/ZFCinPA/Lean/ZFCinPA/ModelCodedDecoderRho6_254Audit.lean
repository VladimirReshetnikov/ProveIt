import ZFCinPA.ModelCodedDecoderRho6_254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedBindOne
open _root_.SetTheory.BusyBeaver.ZFC
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254.namedBody_open
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254.namedAll_elim
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254.negNamedBody_free
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254.negNamedAll_vacuous
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254.existentialAll_elim
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254.decoded_one_neg_of_zf
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254.relativeFalse_equiv_neg
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254.decoded_neg_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254.decoded_rho6_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254.decoded_rho6_provable_of_resources
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254.zf_decoded_rho6_provable
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254.zfc_decoded_rho6_provable
example (a : V) (p : Formula V ℒₛₑₜ) :
    (namedBody a p).subst ![Semiterm.fvar a] = p := namedBody_open a p
example (T : InternalTheory V ℒₛₑₜ) (a : V) (p : Formula V ℒₛₑₜ) :
    T ⊢! namedFormula a p 🡒 p := namedAll_elim T a p
example (a : V) (p : Formula V ℒₛₑₜ) :
    (namedBody a (∼namedFormula a p)).free = (∼namedFormula a p).shift := negNamedBody_free a p
example (T : InternalTheory V ℒₛₑₜ) (a : V) (p : Formula V ℒₛₑₜ) :
    T ⊢! (∼namedFormula a p) 🡒 namedFormula a (∼namedFormula a p) := negNamedAll_vacuous T a p
example (T : InternalTheory V ℒₛₑₜ) (a : V) (p : Formula V ℒₛₑₜ) :
    T ⊢ (∼namedFormula a (∼namedFormula a p)) 🡒 p := existentialAll_elim T a p
example (T : SetTheory) [T.Δ₁] (hZF : (𝗭𝗙 : SetTheory) ⪯ T) :
    T.internalize V ⊢ ∼decoded (1 : V) := decoded_one_neg_of_zf T hZF
example (T : InternalTheory V ℒₛₑₜ) (p f : Formula V ℒₛₑₜ) (hf : T ⊢ ∼f) :
    T ⊢ (p 🡒 f) 🡘 ∼p := relativeFalse_equiv_neg T p f hf
example (T : SetTheory) [T.Δ₁] (n : V) (hf : T.internalize V ⊢ ∼decoded (1 : V)) :
    T.internalize V ⊢ decoded (ArithmeticCode254.wim n 1) 🡘 ∼decoded n := decoded_neg_equiv T hf n
example (T : SetTheory) [T.Δ₁] (a b : V)
    (hf : T.internalize V ⊢ ∼decoded (1 : V))
    (hg : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p)) :
    T.internalize V ⊢ decoded (ArithmeticTemplates254.rho6 a b) 🡘
      ((∼namedFormula a (∼namedFormula a (decoded b))) 🡒 decoded b) := decoded_rho6_equiv T a b hf hg
example (T : SetTheory) [T.Δ₁] (a b : V)
    (hf : T.internalize V ⊢ ∼decoded (1 : V))
    (hg : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p)) :
    Provable T (decode (ArithmeticTemplates254.rho6 a b)) := decoded_rho6_provable_of_resources T a b hf hg
example (a b : V) : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticTemplates254.rho6 a b)) := zf_decoded_rho6_provable a b
example (a b : V) : Provable (𝗭𝗙𝗖 : SetTheory)
    (decode (ArithmeticTemplates254.rho6 a b)) := zfc_decoded_rho6_provable a b
example (b : V) : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticTemplates254.rho6 (0 : V) b)) := zf_decoded_rho6_provable 0 b
example : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticTemplates254.rho6 (0 : V) 0)) := zf_decoded_rho6_provable 0 0
example : Provable (𝗭𝗙𝗖 : SetTheory)
    (decode (ArithmeticTemplates254.rho6 (0 : V) 0)) := zfc_decoded_rho6_provable 0 0
example (a b : V) : ∃ d : V, Proof (𝗭𝗙 : SetTheory) d
    (decode (ArithmeticTemplates254.rho6 a b)) := zf_decoded_rho6_provable a b
