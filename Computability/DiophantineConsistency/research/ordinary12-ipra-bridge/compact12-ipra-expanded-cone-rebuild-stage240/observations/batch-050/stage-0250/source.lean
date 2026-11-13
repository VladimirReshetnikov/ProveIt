import ZFCinPA.ModelCodedTwoQuantifierSwap
import ZFCinPA.ModelCodedDecoderRho2_254

set_option autoImplicit false

/-!
Actual numerical rho4 (exchange of two named universals), including coincident
internal labels. Distinct labels use the represented slot exchange
and finite target double-universal proof; equal labels use literal identity.
This is a logical row, with no GEN or target set-theory axiom premise.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderRho4_254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LO.Entailment
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedBindOneSwap
open LeanProofs.ZFCinPA.ModelCodedTwoQuantifierSwap
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def doubleBody (a b : V) (p : Formula V ℒₛₑₜ) :
    Bootstrapping.Semiformula V ℒₛₑₜ 2 :=
  ⟨bindOneAt ℒₛₑₜ a 1 (bindOneAt ℒₛₑₜ b 0 p.val),by
    have hp : IsFormula ℒₛₑₜ p.val := by simpa using p.isSemiformula
    have h := bindOneAt_isSemiformula (bindOneAt_isSemiformula hp b) a
    simpa only [zero_add,one_add_one_eq_two,Nat.cast_ofNat] using h⟩

lemma namedFormula_twice (a b : V) (p : Formula V ℒₛₑₜ) :
    namedFormula a (namedFormula b p) = ∀⁰ ∀⁰ doubleBody a b p := by
  apply Bootstrapping.Semiformula.ext
  have hp : IsFormula ℒₛₑₜ p.val := by simpa using p.isSemiformula
  change ^∀ (bindOneAt ℒₛₑₜ a 0 (^∀ (bindOneAt ℒₛₑₜ b 0 p.val))) =
    ^∀ (^∀ (bindOneAt ℒₛₑₜ a 1 (bindOneAt ℒₛₑₜ b 0 p.val)))
  rw [bindOneAt_all a 0 (bindOneAt_isSemiformula hp b).isUFormula]
  simp only [zero_add]

lemma doubleBody_swap (a b : V) (hab : a ≠ b) (p : Formula V ℒₛₑₜ) :
    (doubleBody a b p).subst ![Semiterm.bvar 1,Semiterm.bvar 0] = doubleBody b a p := by
  apply Bootstrapping.Semiformula.ext
  rw [typed_swap_val]
  have hp : IsFormula ℒₛₑₜ p.val := by simpa using p.isSemiformula
  simpa only [doubleBody,zero_add] using bindOneAt_swap hp a b hab

theorem namedAll_commutes (T : Theory ℒₛₑₜ) [T.Δ₁] (a b : V)
    (p : Formula V ℒₛₑₜ) :
    T.internalize V ⊢ namedFormula a (namedFormula b p) 🡒
      namedFormula b (namedFormula a p) := by
  classical
  by_cases hab : a = b
  · subst b
    exact ⟨C_id⟩
  · have h : T.internalize V ⊢
        (∀⁰ ∀⁰ doubleBody a b p) 🡒
          (∀⁰ ∀⁰ ((doubleBody a b p).subst ![Semiterm.bvar 1,Semiterm.bvar 0])) :=
      ⟨allSwap (T.internalize V) (doubleBody a b p)⟩
    simpa only [namedFormula_twice,doubleBody_swap a b hab p] using h

theorem decoded_rho4_equiv (T : Theory ℒₛₑₜ) [T.Δ₁] (a b c : V) :
    T.internalize V ⊢ decoded (ArithmeticTemplates254.rho4 a b c) 🡘
      (namedFormula a (namedFormula b (decoded c)) 🡒
        namedFormula b (namedFormula a (decoded c))) := by
  simp only [ArithmeticTemplates254.rho4,ArithmeticTemplates254.rho4Circuit,
    ArithmeticTemplates254.Circuit.r4,ArithmeticTemplates254.Circuit.eval_im,
    ArithmeticTemplates254.Circuit.eval_al,ArithmeticTemplates254.Circuit.eval_input0,
    ArithmeticTemplates254.Circuit.eval_input1,ArithmeticTemplates254.Circuit.eval_input2,
    ArithmeticCode254.wim,ArithmeticCode254.tagged,add_zero]
  apply decoded_imp_congr
  · rw [namedFormula_decoded,namedFormula_decoded]
    exact ⟨E_Id⟩
  · rw [namedFormula_decoded,namedFormula_decoded]
    exact ⟨E_Id⟩

theorem decoded_rho4_provable (T : Theory ℒₛₑₜ) [T.Δ₁] (a b c : V) :
    Provable T (decode (ArithmeticTemplates254.rho4 a b c)) := by
  apply (tprovable_iff_provable (σ := decoded _)).mp
  exact (iff_of_E! (decoded_rho4_equiv T a b c)).mpr
    (namedAll_commutes T a b (decoded c))

end LeanProofs.ZFCinPA.ModelCodedDecoderRho4_254
