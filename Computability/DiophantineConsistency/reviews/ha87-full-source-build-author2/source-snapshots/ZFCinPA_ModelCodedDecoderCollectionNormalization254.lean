import ZFCinPA.ModelCodedDecoderContainer254

set_option autoImplicit false

/-!
Exact logical normalization of the G circuit. The same numeric labels are
retained throughout; the input code c is both a formula code and the outer
container binder label. This is an equivalence, not yet a Collection proof.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderCollectionNormalization254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LO.Entailment
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedProofRenaming
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

noncomputable def nativeG (a b c : V) (p : Formula V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  namedExists c
    ((namedFormula a (memNamed a b 🡒
      namedFormula b (p 🡒 namedExists b (p ⋏ memNamed b c)))) ⋏
     namedFormula b (memNamed b c 🡒 namedExists a p))

/-- Gate-free identification only; gates belong to the eventual proof client. -/
theorem interpret_collection_native_equiv (T : SetTheory) [T.Δ₁]
    (hGen : ∀ label p : V, Provable T p → Provable T (namedAll ℒₛₑₜ label p))
    (a b c : V) :
    T.internalize V ⊢ interpret bundleGCircuit a b c 0 🡘 nativeG a b c (decoded c) := by
  unfold bundleGCircuit Circuit.collection nativeG
  apply interpret_ex_congr T hGen
  apply interpret_conj_congr T
  · apply interpret_all_congr T hGen
    apply interpret_im_congr T
    · exact ⟨E_Id⟩
    · apply interpret_all_congr T hGen
      apply interpret_im_congr T
      · exact ⟨E_Id⟩
      · apply interpret_ex_congr T hGen
        apply interpret_conj_congr T
        · exact ⟨E_Id⟩
        · exact ⟨E_Id⟩
  · apply interpret_all_congr T hGen
    apply interpret_im_congr T
    · exact ⟨E_Id⟩
    · apply interpret_ex_congr T hGen
      exact ⟨E_Id⟩

theorem nativeG_equiv (T : SetTheory) [T.Δ₁]
    (hGen : ∀ label p : V, Provable T p → Provable T (namedAll ℒₛₑₜ label p))
    (a b c : V) (p q : Formula V ℒₛₑₜ)
    (hpq : T.internalize V ⊢ p 🡘 q) :
    T.internalize V ⊢ nativeG a b c p 🡘 nativeG a b c q := by
  unfold nativeG
  apply namedExists_equiv T c (hGen c)
  apply EKK!_of_E!_of_E!
  · apply namedFormula_equiv T a (hGen a)
    apply ECC!_of_E!_of_E! ⟨E_Id⟩
    apply namedFormula_equiv T b (hGen b)
    apply ECC!_of_E!_of_E! hpq
    apply namedExists_equiv T b (hGen b)
    exact EKK!_of_E!_of_E! hpq ⟨E_Id⟩
  · apply namedFormula_equiv T b (hGen b)
    apply ECC!_of_E!_of_E! ⟨E_Id⟩
    exact namedExists_equiv T a (hGen a) _ _ hpq

theorem zf_decoded_collection_native_equiv (a b c : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢
      decoded (bundleG a b c) 🡘 nativeG a b c (decoded c) :=
  E!_trans (zf_decoded_bundleG_equiv a b c)
    (interpret_collection_native_equiv 𝗭𝗙
      (fun label _ hp => zf_provable_namedAll label hp) a b c)

end LeanProofs.ZFCinPA.ModelCodedDecoderCollectionNormalization254
