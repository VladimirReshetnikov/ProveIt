import ZFCinPA.SeparationKernel

set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SeparationKernelFocusedAudit

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.SeparationKernel
open LeanProofs.BoundedPAConsistency.TypedTemplateProofCompiler

#print axioms LeanProofs.ZFCinPA.SeparationKernel.zfc_delta1ch_eq
#print axioms LeanProofs.ZFCinPA.SeparationKernel.mem_zfc_delta1Class_of_sepR
#print axioms LeanProofs.ZFCinPA.SeparationKernel.sepBody_shift_fixed
#print axioms LeanProofs.ZFCinPA.SeparationKernel.sepBody_mem_zfc_delta1Class_of_shift_fixed
#print axioms LeanProofs.ZFCinPA.SeparationKernel.zfcSeparationProofOfShiftFixed
#print axioms LeanProofs.ZFCinPA.SeparationKernel.translateFormula_neg
#print axioms LeanProofs.ZFCinPA.SeparationKernel.translateFormula_shift
#print axioms LeanProofs.ZFCinPA.SeparationKernel.translateFormula_subst
#print axioms LeanProofs.ZFCinPA.SeparationKernel.translateFormula_free
#print axioms LeanProofs.ZFCinPA.SeparationKernel.setTemplateTranslation
#print axioms LeanProofs.ZFCinPA.SeparationKernel.translateFormula_lMap_set_emb
#print axioms LeanProofs.ZFCinPA.SeparationKernel.translate_srcSeparation
#print axioms LeanProofs.ZFCinPA.SeparationKernel.translate_srcOmegaZero
#print axioms LeanProofs.ZFCinPA.SeparationKernel.translate_srcOmegaSucc
#print axioms LeanProofs.ZFCinPA.SeparationKernel.translate_srcOmegaConcl
#print axioms LeanProofs.ZFCinPA.SeparationKernel.translate_srcOmegaInduction
#print axioms LeanProofs.ZFCinPA.SeparationKernel.omegaTheoryTranslation
#print axioms LeanProofs.ZFCinPA.SeparationKernel.compileOmegaTemplate
#print axioms LeanProofs.ZFCinPA.SeparationKernel.zfc_proves_inductiveSetExists
#print axioms LeanProofs.ZFCinPA.SeparationKernel.liftedInductiveSetExistsProof
#print axioms LeanProofs.ZFCinPA.SeparationKernel.omegaSourceProof
#print axioms LeanProofs.ZFCinPA.SeparationKernel.zfcOmegaInductionOfShiftFixed

example : (setTemplateLanguage).DecidableEq := inferInstance

example :
    (𝗭𝗙𝗖 : SetTheory).Δ₁ch =
      ((((𝗘𝗤 ℒₛₑₜ : SetTheory).Δ₁ch ⋎ zfFixed.Δ₁ch) ⋎ sepCh) ⋎ repCh)
        ⋎ (𝗔𝗖 : SetTheory).Δ₁ch := zfc_delta1ch_eq

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example {p : V} (hp : SepR p) : p ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class :=
  mem_zfc_delta1Class_of_sepR hp

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val) :
    (sepBody K).shift = sepBody K := sepBody_shift_fixed K hK

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val) :
    (sepBody K).val ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class :=
  sepBody_mem_zfc_delta1Class_of_shift_fixed K hK

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! sepBody K :=
  zfcSeparationProofOfShiftFixed K hK

example {n : ℕ} (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (p : Semiproposition setTemplateLanguage n) :
    translateFormula K (∼p) = ∼translateFormula K p :=
  translateFormula_neg K p

example {n : ℕ} (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : K.shift = K) (p : Semiproposition setTemplateLanguage n) :
    translateFormula K (Rewriting.shift p) = (translateFormula K p).shift :=
  translateFormula_shift K hK p

example {n m : ℕ} (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (w : Fin n → SyntacticSemiterm setTemplateLanguage m)
    (p : Semiproposition setTemplateLanguage n) :
    translateFormula K (Rew.subst w ▹ p) =
      (translateFormula K p).subst (fun i ↦ translateTerm (V := V) (w i)) :=
  translateFormula_subst K w p

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) (hK : K.shift = K)
    (p : Semiproposition setTemplateLanguage 1) :
    translateFormula K (Rewriting.free p) = (translateFormula K p).free :=
  translateFormula_free K hK p

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) (hK : K.shift = K) :
    TypedTemplateTranslation V setTemplateLanguage ℒₛₑₜ :=
  setTemplateTranslation K hK

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) (σ : SetTheorySentence) :
    translateFormula K (Rewriting.emb (σ.lMap setHom) : Proposition setTemplateLanguage) =
      (⌜σ⌝ : Bootstrapping.Formula V ℒₛₑₜ) :=
  translateFormula_lMap_set_emb K σ

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    translateFormula K (Rewriting.emb srcSeparation : Proposition setTemplateLanguage) =
      sepBody K := translate_srcSeparation K

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    translateFormula K (Rewriting.emb srcOmegaZero : Proposition setTemplateLanguage) =
      ∀⁰ (isEmptyQ 🡒 K) := translate_srcOmegaZero K

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    translateFormula K (Rewriting.emb srcOmegaSucc : Proposition setTemplateLanguage) =
      ∀⁰ ∀⁰ (K.subst ![.bvar 1] 🡒 (isSuccQ 🡒 K.subst ![.bvar 0])) :=
  translate_srcOmegaSucc K

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    translateFormula K (Rewriting.emb srcOmegaConcl : Proposition setTemplateLanguage) =
      ∀⁰ (isVonNeumannNatQ 🡒 K) := translate_srcOmegaConcl K

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    translateFormula K (Rewriting.emb srcOmegaInduction : Proposition setTemplateLanguage) =
      ((∀⁰ (isEmptyQ 🡒 K)) 🡒
        ((∀⁰ ∀⁰ (K.subst ![.bvar 1] 🡒 (isSuccQ 🡒 K.subst ![.bvar 0]))) 🡒
          (∀⁰ (isVonNeumannNatQ 🡒 K)))) := translate_srcOmegaInduction K

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val) :
    TypedTheoryTemplateTranslation omegaSourceTheory ((𝗭𝗙𝗖 : SetTheory).internalize V) :=
  omegaTheoryTranslation K hK

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val)
    {σ : Sentence setTemplateLanguage} (d : omegaSourceTheory ⊢! σ) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! translateFormula K (Rewriting.emb σ) :=
  compileOmegaTemplate K hK d

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val)
    (hzero : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! ∀⁰ (isEmptyQ 🡒 K))
    (hsucc : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ∀⁰ ∀⁰ (K.subst ![.bvar 1] 🡒 (isSuccQ 🡒 K.subst ![.bvar 0]))) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! ∀⁰ (isVonNeumannNatQ 🡒 K) :=
  zfcOmegaInductionOfShiftFixed K hK hzero hsucc
end Internal

example : 𝗭𝗙𝗖 ⊢ inductiveSetExists := zfc_proves_inductiveSetExists

example : omegaSourceTheory ⊢! Semiformula.lMap setHom inductiveSetExists :=
  liftedInductiveSetExistsProof

example : omegaSourceTheory ⊢! srcOmegaInduction := omegaSourceProof

end LeanProofs.ZFCinPA.SeparationKernelFocusedAudit
