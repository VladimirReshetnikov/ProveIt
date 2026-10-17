import ZFCinPA.ModelCodedDecoderCollectionNormalization254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedDecoderCircuits254
open LeanProofs.ZFCinPA.ModelCodedDecoderCollectionNormalization254
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254
open scoped LO.FirstOrder.Arithmetic
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCollectionNormalization254.interpret_collection_native_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCollectionNormalization254.nativeG_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCollectionNormalization254.zf_decoded_collection_native_equiv
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (T : SetTheory) [T.Δ₁]
    (hGen : ∀ label p : V, Provable T p → Provable T (namedAll ℒₛₑₜ label p))
    (a b c : V) :
    T.internalize V ⊢ interpret bundleGCircuit a b c 0 🡘 nativeG a b c (decoded c) :=
  interpret_collection_native_equiv T hGen a b c
example (T : SetTheory) [T.Δ₁]
    (hGen : ∀ label p : V, Provable T p → Provable T (namedAll ℒₛₑₜ label p))
    (a b c : V) (p q : Formula V ℒₛₑₜ) (hpq : T.internalize V ⊢ p 🡘 q) :
    T.internalize V ⊢ nativeG a b c p 🡘 nativeG a b c q := nativeG_equiv T hGen a b c p q hpq
example (a b c : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ decoded (bundleG a b c) 🡘 nativeG a b c (decoded c) :=
  zf_decoded_collection_native_equiv a b c
example : (𝗭𝗙 : SetTheory).internalize V ⊢
    decoded (bundleG (0 : V) 0 0) 🡘 nativeG 0 0 0 (decoded 0) :=
  zf_decoded_collection_native_equiv 0 0 0
example (a c : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ decoded (bundleG a a c) 🡘 nativeG a a c (decoded c) :=
  zf_decoded_collection_native_equiv a a c
example (a b : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ decoded (bundleG a b (0 : V)) 🡘 nativeG a b 0 (decoded 0) :=
  zf_decoded_collection_native_equiv a b 0
