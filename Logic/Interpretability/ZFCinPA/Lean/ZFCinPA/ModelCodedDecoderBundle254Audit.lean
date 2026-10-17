import ZFCinPA.ModelCodedDecoderBundle254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderCircuits254
open LeanProofs.ZFCinPA.ModelCodedDecoderBundle254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticTemplates254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderBundle254.interpret_conj_intro
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderBundle254.zf_interpreted_bundle
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderBundle254.zf_decoded_bundle_provable
example (T : InternalTheory V ℒₛₑₜ) (e f : Circuit) (a b c u : V)
    (he : T ⊢ interpret e a b c u) (hf : T ⊢ interpret f a b c u) :
    T ⊢ interpret (Circuit.conj e f) a b c u := interpret_conj_intro T e f a b c u he hf
example (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ interpret bundleCircuit a b c 0 :=
  zf_interpreted_bundle a b c hca hcb
example (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    Provable (𝗭𝗙 : SetTheory) (decode (bundle a b c)) :=
  zf_decoded_bundle_provable a b c hca hcb
example (a c : V) (hca : c ≠ a) :
    Provable (𝗭𝗙 : SetTheory) (decode (bundle a a c)) :=
  zf_decoded_bundle_provable a a c hca hca
example (a b : V) (ha : (0 : V) ≠ a) (hb : (0 : V) ≠ b) :
    Provable (𝗭𝗙 : SetTheory) (decode (bundle a b 0)) :=
  zf_decoded_bundle_provable a b 0 ha hb
example : Provable (𝗭𝗙 : SetTheory) (decode (bundle (0 : V) 0 1)) :=
  zf_decoded_bundle_provable 0 0 1 (by simp) (by simp)
example : Provable (𝗭𝗙 : SetTheory) (decode (bundle (1 : V) 2 0)) :=
  zf_decoded_bundle_provable 1 2 0 (by simp) (by simp)
example (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    ∃ d : V, Proof (𝗭𝗙 : SetTheory) d (decode (bundle a b c)) :=
  zf_decoded_bundle_provable a b c hca hcb
