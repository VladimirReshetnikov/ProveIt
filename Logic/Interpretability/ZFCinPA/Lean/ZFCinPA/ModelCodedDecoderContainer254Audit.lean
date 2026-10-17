import ZFCinPA.ModelCodedDecoderContainer254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open LeanProofs.ZFCinPA.ModelCodedDecoderCircuits254
open LeanProofs.ZFCinPA.ModelCodedNamedLogicalNormalization254
open LeanProofs.ZFCinPA.ModelCodedDecoderContainer254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticTemplates254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderContainer254.interpret_im_congr
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderContainer254.interpret_conj_congr
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderContainer254.interpret_all_congr
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderContainer254.interpret_ex_congr
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderContainer254.interpret_container_native_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderContainer254.zf_decoded_container_native_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderContainer254.canonicalContainer_quote_subst
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderContainer254.zf_canonicalContainer_provable
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderContainer254.nativeContainer_distinct
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderContainer254.zf_not_mem_self
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderContainer254.namedExists_mono
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderContainer254.zf_membershipContainer_outer
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderContainer254.zf_named_membership_exists
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderContainer254.zf_nativeContainer_coincident
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderContainer254.zf_nativeContainer_provable
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderContainer254.zf_decoded_bundleC_provable
example (T : SetTheory) [T.Δ₁] (x y : Circuit) (a b c u : V) (p q : Formula V ℒₛₑₜ)
    (hp : T.internalize V ⊢ interpret x a b c u 🡘 p)
    (hq : T.internalize V ⊢ interpret y a b c u 🡘 q) :
    T.internalize V ⊢ interpret (Circuit.im x y) a b c u 🡘 (p 🡒 q) :=
  interpret_im_congr T x y a b c u p q hp hq
example (T : SetTheory) [T.Δ₁] (x y : Circuit) (a b c u : V) (p q : Formula V ℒₛₑₜ)
    (hp : T.internalize V ⊢ interpret x a b c u 🡘 p)
    (hq : T.internalize V ⊢ interpret y a b c u 🡘 q) :
    T.internalize V ⊢ interpret (Circuit.conj x y) a b c u 🡘 (p ⋏ q) :=
  interpret_conj_congr T x y a b c u p q hp hq
example (T : SetTheory) [T.Δ₁]
    (hg : ∀ label p : V, Provable T p → Provable T (namedAll ℒₛₑₜ label p))
    (label x : Circuit) (a b c u : V) (p : Formula V ℒₛₑₜ)
    (hp : T.internalize V ⊢ interpret x a b c u 🡘 p) :
    T.internalize V ⊢ interpret (Circuit.al label x) a b c u 🡘 namedFormula (label.eval a b c u) p :=
  interpret_all_congr T hg label x a b c u p hp
example (T : SetTheory) [T.Δ₁]
    (hg : ∀ label p : V, Provable T p → Provable T (namedAll ℒₛₑₜ label p))
    (label x : Circuit) (a b c u : V) (p : Formula V ℒₛₑₜ)
    (hp : T.internalize V ⊢ interpret x a b c u 🡘 p) :
    T.internalize V ⊢ interpret (Circuit.ex label x) a b c u 🡘 namedExists (label.eval a b c u) p :=
  interpret_ex_congr T hg label x a b c u p hp
example (T : SetTheory) [T.Δ₁]
    (hg : ∀ label p : V, Provable T p → Provable T (namedAll ℒₛₑₜ label p)) (a b c : V) :
    T.internalize V ⊢ interpret bundleCCircuit a b c 0 🡘 nativeContainer a b c :=
  interpret_container_native_equiv T hg a b c
example (a b c : V) : (𝗭𝗙 : SetTheory).internalize V ⊢
    decoded (bundleC a b c) 🡘 nativeContainer a b c := zf_decoded_container_native_equiv a b c
example (c : V) :
    (⌜containerRowMatrix⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 1).subst ![Bootstrapping.Semiterm.fvar c] =
      canonicalContainer c := canonicalContainer_quote_subst c
example (c : V) : (𝗭𝗙 : SetTheory).internalize V ⊢ canonicalContainer c := zf_canonicalContainer_provable c
example (a b c : V) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    nativeContainer a b c = canonicalContainer c := nativeContainer_distinct a b c hab hca hcb
example (a : V) : (𝗭𝗙 : SetTheory).internalize V ⊢ ∼memNamed a a := zf_not_mem_self a
example (T : SetTheory) [T.Δ₁] (label : V)
    (hg : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ label p))
    (p q : Formula V ℒₛₑₜ) (h : T.internalize V ⊢ p 🡒 q) :
    T.internalize V ⊢ namedExists label p 🡒 namedExists label q := namedExists_mono T label hg h
example : (𝗭𝗙 : SetTheory) ⊢ membershipContainerSentence := zf_membershipContainer_outer
example (a c : V) (hca : c ≠ a) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ namedExists a (memNamed c a) := zf_named_membership_exists a c hca
example (a c : V) (hca : c ≠ a) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ nativeContainer a a c := zf_nativeContainer_coincident a c hca
example (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ nativeContainer a b c := zf_nativeContainer_provable a b c hca hcb
example (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    Provable (𝗭𝗙 : SetTheory) (decode (bundleC a b c)) := zf_decoded_bundleC_provable a b c hca hcb
example : Provable (𝗭𝗙 : SetTheory) (decode (bundleC (0 : V) 1 2)) :=
  zf_decoded_bundleC_provable 0 1 2 (by simp) (by simp)
example : Provable (𝗭𝗙 : SetTheory) (decode (bundleC (1 : V) 2 0)) :=
  zf_decoded_bundleC_provable 1 2 0 (by simp) (by simp)
example : Provable (𝗭𝗙 : SetTheory) (decode (bundleC (0 : V) 0 1)) :=
  zf_decoded_bundleC_provable 0 0 1 (by simp) (by simp)
example (a c : V) (hca : c ≠ a) :
    Provable (𝗭𝗙 : SetTheory) (decode (bundleC a a c)) := zf_decoded_bundleC_provable a a c hca hca
