import ZFCinPA.NTInterp

set_option autoImplicit false
noncomputable section

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.NativeInterp LeanProofs.ZFCinPA.NTInterp

#print axioms LeanProofs.ZFCinPA.NTInterp.intT_rel_inr
#print axioms LeanProofs.ZFCinPA.NTInterp.intT_nrel_inr
#print axioms LeanProofs.ZFCinPA.NTInterp.intT_neg
#print axioms LeanProofs.ZFCinPA.NTInterp.intT_imp
#print axioms LeanProofs.ZFCinPA.NTInterp.intT_iff
#print axioms LeanProofs.ZFCinPA.NTInterp.emb_comp_embSubstsT
#print axioms LeanProofs.ZFCinPA.NTInterp.emb_atomT
#print axioms LeanProofs.ZFCinPA.NTInterp.emb_domT
#print axioms LeanProofs.ZFCinPA.NTInterp.emb_intT
#print axioms LeanProofs.ZFCinPA.NTInterp.IK_val
#print axioms LeanProofs.ZFCinPA.NTInterp.embSubsts_app
#print axioms LeanProofs.ZFCinPA.NTInterp.translate_embSubsts_liftSet
#print axioms LeanProofs.ZFCinPA.NTInterp.translate_domT
#print axioms LeanProofs.ZFCinPA.NTInterp.translate_atomT_eq
#print axioms LeanProofs.ZFCinPA.NTInterp.translate_atomT_mem
#print axioms LeanProofs.ZFCinPA.NTInterp.interp_translate
#print axioms LeanProofs.ZFCinPA.NTInterp.interp_translate_emb

variable {k : ℕ} {arities : Fin k → ℕ}
section Meta
variable {ξ : Type*}

example {n m : ℕ} (r : (multiPlaceholderLanguage k arities).Rel m)
    (v : Fin m → Semiterm (setTemplateLanguage k arities) ξ n) :
    intT (.rel (L := setTemplateLanguage k arities) (Sum.inr r) v) = .rel (Sum.inr r) v :=
  intT_rel_inr r v

example {n m : ℕ} (r : (multiPlaceholderLanguage k arities).Rel m)
    (v : Fin m → Semiterm (setTemplateLanguage k arities) ξ n) :
    intT (.nrel (L := setTemplateLanguage k arities) (Sum.inr r) v) = .nrel (Sum.inr r) v :=
  intT_nrel_inr r v

example {n : ℕ} (φ : Semiformula (setTemplateLanguage k arities) ξ n) :
    intT (∼φ) = ∼intT φ := intT_neg φ

example {n : ℕ} (φ ψ : Semiformula (setTemplateLanguage k arities) ξ n) :
    intT (φ 🡒 ψ) = intT φ 🡒 intT ψ := intT_imp φ ψ

example {n : ℕ} (φ ψ : Semiformula (setTemplateLanguage k arities) ξ n) :
    intT (φ 🡘 ψ) = intT φ 🡘 intT ψ := intT_iff φ ψ

example {ο : Type*} [IsEmpty ο] {n m : ℕ}
    (v : Fin m → Semiterm (setTemplateLanguage k arities) ο n) :
    ((Rew.emb : Rew (setTemplateLanguage k arities) ο n ξ n).comp (Rew.embSubsts v)) =
      Rew.embSubsts (fun i ↦ Rew.emb (v i)) := emb_comp_embSubstsT v

example {ο : Type*} [IsEmpty ο] {n m : ℕ} (R : (ℒₛₑₜ).Rel m)
    (v : Fin m → Semiterm (setTemplateLanguage k arities) ο n) :
    (Rew.emb ▹ atomT R v : Semiformula (setTemplateLanguage k arities) ξ n) =
      atomT R (fun i ↦ Rew.emb (v i)) := emb_atomT R v

example {ο : Type*} [IsEmpty ο] {n : ℕ} :
    (Rew.emb ▹ (domT n : Semiformula (setTemplateLanguage k arities) ο (n + 1)) :
      Semiformula (setTemplateLanguage k arities) ξ (n + 1)) = domT n := emb_domT

example {ο : Type*} [IsEmpty ο] {n : ℕ}
    (φ : Semiformula (setTemplateLanguage k arities) ο n) :
    (Rew.emb ▹ intT φ : Semiformula (setTemplateLanguage k arities) ξ n) =
      intT (Rew.emb ▹ φ) := emb_intT φ
end Meta

section Internal
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.InternalInterpretation
open LeanProofs.BoundedPAConsistency.InternalRelativization
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example {a : ℕ} (K : Bootstrapping.Semiformula V ℒₛₑₜ a) :
    (IK K).val = interp (PN : V) K.val := IK_val K

example {n m : ℕ} (v : Fin m → SyntacticSemiterm (setTemplateLanguage k arities) n)
    (σ : Semisentence (setTemplateLanguage k arities) m) :
    (Rew.embSubsts v ▹ σ : Semiproposition (setTemplateLanguage k arities) n) =
      Rew.subst v ▹ (Rewriting.emb σ : Semiproposition (setTemplateLanguage k arities) m) :=
  embSubsts_app v σ

example (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {n m : ℕ} (v : Fin m → SyntacticSemiterm (setTemplateLanguage k arities) n)
    (σ : SetTheorySemisentence m) :
    (translateFormula Ks (Rew.embSubsts v ▹ liftSet σ)).val =
      subst ℒₛₑₜ (SemitermVec.val fun i ↦ translateTerm (V := V) (v i)) (⌜σ⌝ : V) :=
  translate_embSubsts_liftSet Ks v σ

example (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)) (n : ℕ) :
    (translateFormula Ks (domT n : Semiproposition (setTemplateLanguage k arities) (n + 1))).val =
      (⌜domS⌝ : V) := translate_domT Ks n

example (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {n : ℕ} (v : Fin 2 → SyntacticSemiterm (setTemplateLanguage k arities) n) :
    (translateFormula Ks (atomT Language.Set.Rel.eq v)).val =
      subst ℒₛₑₜ (SemitermVec.val fun i ↦ translateTerm (V := V) (v i)) (⌜eqS⌝ : V) :=
  translate_atomT_eq Ks v

example (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {n : ℕ} (v : Fin 2 → SyntacticSemiterm (setTemplateLanguage k arities) n) :
    (translateFormula Ks (atomT Language.Set.Rel.mem v)).val =
      subst ℒₛₑₜ (SemitermVec.val fun i ↦ translateTerm (V := V) (v i)) (⌜memS⌝ : V) :=
  translate_atomT_mem Ks v

example (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {n : ℕ} (φ : Semiproposition (setTemplateLanguage k arities) n) :
    interp (PN : V) (translateFormula Ks φ).val =
      (translateFormula (fun i ↦ IK (Ks i)) (intT φ)).val := interp_translate Ks φ

example (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (σ : Sentence (setTemplateLanguage k arities)) :
    interp (PN : V) (translateFormula Ks (Rewriting.emb σ)).val =
      (translateFormula (fun i ↦ IK (Ks i)) (Rewriting.emb (intT σ))).val :=
  interp_translate_emb Ks σ

example (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {n : ℕ} (φ : Semiproposition (setTemplateLanguage k arities) (n + 1)) :
    interp (PN : V) (translateFormula Ks (∀⁰ φ)).val =
      (translateFormula (fun i ↦ IK (Ks i)) (intT (∀⁰ φ))).val :=
  interp_translate Ks (∀⁰ φ)

example (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {n : ℕ} (φ : Semiproposition (setTemplateLanguage k arities) (n + 1)) :
    interp (PN : V) (translateFormula Ks (∃⁰ φ)).val =
      (translateFormula (fun i ↦ IK (Ks i)) (intT (∃⁰ φ))).val :=
  interp_translate Ks (∃⁰ φ)
end Internal
