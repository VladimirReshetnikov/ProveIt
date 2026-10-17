import ZFCinPA.ModelCodedDecoderCollection254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedDecoderCollectionNormalization254
open LeanProofs.ZFCinPA.ModelCodedDecoderCollection254
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254
open scoped LO.FirstOrder.Arithmetic
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCollection254.binaryBody_subst
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCollection254.translate_collectionSentence
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCollection254.collectionMatrix_specialize
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCollection254.zf_canonicalG_provable
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCollection254.nativeG_distinct
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCollection254.zf_nativeG_distinct
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCollection254.zf_nativeG_coincident
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCollection254.decoded_zero_equiv_top
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCollection254.zf_nativeG_decoded
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderCollection254.zf_decoded_bundleG_provable
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local prefix:max "#'" => Bootstrapping.Semiterm.bvar (V := V) (L := ℒₛₑₜ)

example {m : Nat} (p : Formula V ℒₛₑₜ) (a b : V) (hab : a ≠ b) (i j : Fin m) :
    ((binaryBody a b p).subst ![#'i,#'j]).val =
      bindOneAt ℒₛₑₜ b (j : V) (bindOneAt ℒₛₑₜ a (i : V) p.val) :=
  binaryBody_subst a b p i j hab
example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    LeanProofs.ZFCinPA.SetPlaceholders.translateFormula (fun _ : Fin 1 => K)
      (Rewriting.emb LeanProofs.ZFCinPA.CollectionTemplate254.collectionSentence) =
      ∀⁰ collectionMatrix K := translate_collectionSentence K
example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) (b : V) :
    (collectionMatrix K).subst ![Bootstrapping.Semiterm.fvar b] = canonicalG K b :=
  collectionMatrix_specialize K b
example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) (b : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ canonicalG K b := zf_canonicalG_provable K b
example (a b c : V) (p : Formula V ℒₛₑₜ) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hf : ∀ d : V, bindOneAt ℒₛₑₜ c d p.val = p.val) :
    nativeG a b c p = canonicalG (binaryBody a b p) b := nativeG_distinct a b c p hab hca hcb hf
example (a b c : V) (p : Formula V ℒₛₑₜ) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hf : ∀ d : V, bindOneAt ℒₛₑₜ c d p.val = p.val) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ nativeG a b c p := zf_nativeG_distinct a b c p hab hca hcb hf
example (a c : V) (p : Formula V ℒₛₑₜ) (hca : c ≠ a) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ nativeG a a c p := zf_nativeG_coincident a c p hca
example (T : InternalTheory V ℒₛₑₜ) : T ⊢ decoded (0 : V) 🡘 ⊤ := decoded_zero_equiv_top T
example (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ nativeG a b c (decoded c) := zf_nativeG_decoded a b c hca hcb
example (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    Provable (𝗭𝗙 : SetTheory) (decode (bundleG a b c)) := zf_decoded_bundleG_provable a b c hca hcb
example (a c : V) (hca : c ≠ a) :
    Provable (𝗭𝗙 : SetTheory) (decode (bundleG a a c)) := zf_decoded_bundleG_provable a a c hca hca
example : Provable (𝗭𝗙 : SetTheory) (decode (bundleG (0 : V) 0 1)) :=
  zf_decoded_bundleG_provable 0 0 1 (by simp) (by simp)
example : Provable (𝗭𝗙 : SetTheory) (decode (bundleG (1 : V) 2 0)) :=
  zf_decoded_bundleG_provable 1 2 0 (by simp) (by simp)
example : Provable (𝗭𝗙 : SetTheory) (decode (bundleG (1 : V) 1 0)) :=
  zf_decoded_bundleG_provable 1 1 0 (by simp) (by simp)
example (c : V) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    Provable (𝗭𝗙 : SetTheory) (decode (bundleG (0 : V) 1 c)) :=
  zf_decoded_bundleG_provable 0 1 c hc0 hc1
example (c : V) (hc : c ≠ 0) :
    Provable (𝗭𝗙 : SetTheory) (decode (bundleG (0 : V) 0 c)) :=
  zf_decoded_bundleG_provable 0 0 c hc hc
