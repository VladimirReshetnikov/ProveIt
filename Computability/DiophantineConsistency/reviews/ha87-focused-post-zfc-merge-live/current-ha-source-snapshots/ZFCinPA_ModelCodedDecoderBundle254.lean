import ZFCinPA.ModelCodedDecoderCollection254

set_option autoImplicit false
noncomputable section

/-!
Assembly of the exact C and G clients and the two
actual atomic vacuity clauses retain both original gates, including a=b and
c=0 cases. No accepted-proof translation or PA comparison is claimed here.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderBundle254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LO.Entailment
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedProofRenaming
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254
open LeanProofs.ZFCinPA.ModelCodedDecoderCircuits254
open LeanProofs.ZFCinPA.ModelCodedNamedLogicalNormalization254
open LeanProofs.ZFCinPA.ModelCodedDecoderContainer254
open LeanProofs.ZFCinPA.ModelCodedDecoderCollectionNormalization254
open LeanProofs.ZFCinPA.ModelCodedDecoderCollection254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticTemplates254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma interpret_conj_intro (T : InternalTheory V ℒₛₑₜ) (e f : Circuit) (a b c u : V)
    (he : T ⊢ interpret e a b c u) (hf : T ⊢ interpret f a b c u) :
    T ⊢ interpret (Circuit.conj e f) a b c u := relativeConj_intro T he hf

theorem zf_interpreted_bundle (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ interpret bundleCircuit a b c 0 := by
  have hc : (𝗭𝗙 : SetTheory).internalize V ⊢ interpret bundleCCircuit a b c 0 :=
    (iff_of_E! (interpret_container_native_equiv 𝗭𝗙
      (fun label _ hp => zf_provable_namedAll label hp) a b c)).mpr
        (zf_nativeContainer_provable a b c hca hcb)
  have hg : (𝗭𝗙 : SetTheory).internalize V ⊢ interpret bundleGCircuit a b c 0 :=
    (iff_of_E! (interpret_collection_native_equiv 𝗭𝗙
      (fun label _ hp => zf_provable_namedAll label hp) a b c)).mpr
        (zf_nativeG_decoded a b c hca hcb)
  have hm : (𝗭𝗙 : SetTheory).internalize V ⊢ interpret
      (Circuit.im (Circuit.el .input0 .input1)
        (Circuit.al .input2 (Circuit.el .input0 .input1))) a b c 0 := by
    change (𝗭𝗙 : SetTheory).internalize V ⊢
      memNamed a b 🡒 namedFormula c (memNamed a b)
    exact ⟨namedFormula_mem_vacuous _ a b c hca hcb⟩
  have he : (𝗭𝗙 : SetTheory).internalize V ⊢ interpret
      (Circuit.im (Circuit.eq .input0 .input1)
        (Circuit.al .input2 (Circuit.eq .input0 .input1))) a b c 0 := by
    change (𝗭𝗙 : SetTheory).internalize V ⊢
      ModelCodedDecoderEquality254.eqAtom (.fvar a) (.fvar b) 🡒
        namedFormula c (ModelCodedDecoderEquality254.eqAtom (.fvar a) (.fvar b))
    exact ⟨namedFormula_eq_vacuous _ a b c hca hcb⟩
  exact interpret_conj_intro _ _ _ a b c 0
    (interpret_conj_intro _ _ _ a b c 0 hc hg)
    (interpret_conj_intro _ _ _ a b c 0 hm he)

theorem zf_decoded_bundle_provable (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    Provable (𝗭𝗙 : SetTheory) (decode (bundle a b c)) := by
  apply (tprovable_iff_provable (σ := decoded _)).mp
  exact (iff_of_E! (zf_decoded_bundle_equiv a b c)).mpr
    (zf_interpreted_bundle a b c hca hcb)

end LeanProofs.ZFCinPA.ModelCodedDecoderBundle254
