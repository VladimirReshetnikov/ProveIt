import ZFCinPA.ModelCodedDecoderCircuits254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedDecoderEquality254
open LeanProofs.ZFCinPA.ModelCodedDecoderCircuits254
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCircuits254.decoded_one_equiv_bottom
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCircuits254.decoded_circuit_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCircuits254.zf_decoded_circuit_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCircuits254.zfc_decoded_circuit_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCircuits254.zf_decoded_bundleC_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCircuits254.zf_decoded_bundleG_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCircuits254.zf_decoded_bundle_equiv
example (T : InternalTheory V ℒₛₑₜ) (hf : T ⊢ ∼decoded (1 : V)) :
    T ⊢ decoded (1 : V) 🡘 ⊥ := decoded_one_equiv_bottom T hf
example (T : SetTheory) [T.Δ₁]
    (hf : T.internalize V ⊢ ∼decoded (1 : V))
    (hg : ∀ a p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p))
    (e : Circuit) (a b c u : V) :
    T.internalize V ⊢ decoded (e.eval a b c u) 🡘 interpret e a b c u :=
  decoded_circuit_equiv T hf hg e a b c u
example (e : Circuit) (a b c u : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ decoded (e.eval a b c u) 🡘 interpret e a b c u :=
  zf_decoded_circuit_equiv e a b c u
example (e : Circuit) (a b c u : V) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢ decoded (e.eval a b c u) 🡘 interpret e a b c u :=
  zfc_decoded_circuit_equiv e a b c u
example (a b c : V) : (𝗭𝗙 : SetTheory).internalize V ⊢
    decoded (bundleC a b c) 🡘 interpret bundleCCircuit a b c 0 := zf_decoded_bundleC_equiv a b c
example (a b c : V) : (𝗭𝗙 : SetTheory).internalize V ⊢
    decoded (bundleG a b c) 🡘 interpret bundleGCircuit a b c 0 := zf_decoded_bundleG_equiv a b c
example (a b c : V) : (𝗭𝗙 : SetTheory).internalize V ⊢
    decoded (bundle a b c) 🡘 interpret bundleCircuit a b c 0 := zf_decoded_bundle_equiv a b c
example (a b c u : V) :
    interpret (.node .rel .one .input0) a b c u = memAtom (Semiterm.fvar 1) (Semiterm.fvar a) := rfl
example (b : V) : (𝗭𝗙 : SetTheory).internalize V ⊢
    decoded ((Circuit.al .input0 (Circuit.neg .input1)).eval 0 b 0 0) 🡘
      interpret (Circuit.al .input0 (Circuit.neg .input1)) 0 b 0 0 :=
  zf_decoded_circuit_equiv _ 0 b 0 0
example : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢
    decoded (bundle (0 : V) 0 0) 🡘 interpret bundleCircuit (0 : V) 0 0 0 :=
  zfc_decoded_circuit_equiv bundleCircuit 0 0 0 0
