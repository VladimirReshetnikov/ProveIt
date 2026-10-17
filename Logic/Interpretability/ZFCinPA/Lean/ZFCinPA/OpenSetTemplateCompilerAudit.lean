import ZFCinPA.OpenSetTemplateCompiler
set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.OpenSetTemplateCompiler
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {k : Nat} {arities : Fin k → Nat}
variable (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
#print axioms LeanProofs.BoundedPAConsistency.TypedTemplateProofCompiler.TypedTheoryTemplateTranslation.compileProof
#print axioms LeanProofs.BoundedPAConsistency.TypedTemplateProofCompiler.TypedTheoryTemplateTranslation.compileProof_isProof
#print axioms LeanProofs.ZFCinPA.SetPlaceholders.translateFormula_subst
#print axioms LeanProofs.ZFCinPA.OpenSetTemplateCompiler.translate_shift_family
#print axioms LeanProofs.ZFCinPA.OpenSetTemplateCompiler.translate_free_family
#print axioms LeanProofs.ZFCinPA.OpenSetTemplateCompiler.openTranslation
#print axioms LeanProofs.ZFCinPA.OpenSetTemplateCompiler.compileOpenTemplate
#print axioms LeanProofs.ZFCinPA.OpenSetTemplateCompiler.compileOpenTemplate_isProof
example {n : Nat} (p : Semiproposition (setTemplateLanguage k arities) n) :
    translateFormula (fun i => (Ks i).shift) (Rewriting.shift p) =
      (translateFormula Ks p).shift := translate_shift_family Ks p
example (p : Semiproposition (setTemplateLanguage k arities) 1) :
    translateFormula (fun i => (Ks i).shift) (Rewriting.free p) =
      (translateFormula Ks p).free := translate_free_family Ks p
example (b : Nat) {n : Nat} (p : Semiproposition (setTemplateLanguage k arities) n) :
    (openTranslation Ks).formula (b+1) (Rewriting.shift p) =
      ((openTranslation Ks).formula b p).shift := (openTranslation Ks).shift b p
example (b : Nat) (p : Semiproposition (setTemplateLanguage k arities) 1) :
    (openTranslation Ks).formula (b+1) (Rewriting.free p) =
      ((openTranslation Ks).formula b p).free := (openTranslation Ks).free b p
example {T : Theory (setTemplateLanguage k arities)} {U : InternalTheory V ℒₛₑₜ}
    (ax : ∀ b (σ : Sentence (setTemplateLanguage k arities)), σ ∈ T →
      U ⊢! translateFormula (shiftedPredicates Ks b) (Rewriting.emb σ))
    {σ : Sentence (setTemplateLanguage k arities)} (d : T ⊢! σ) :
    U ⊢! translateFormula Ks (Rewriting.emb σ) := compileOpenTemplate Ks ax d
example {T : Theory (setTemplateLanguage k arities)} {U : InternalTheory V ℒₛₑₜ}
    (ax : ∀ b (σ : Sentence (setTemplateLanguage k arities)), σ ∈ T →
      U ⊢! translateFormula (shiftedPredicates Ks b) (Rewriting.emb σ))
    {σ : Sentence (setTemplateLanguage k arities)} (d : T ⊢! σ) :
    Proof U.theory (compileOpenTemplate Ks ax d).val
      (translateFormula Ks (Rewriting.emb σ)).val := compileOpenTemplate_isProof Ks ax d
example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2)
    (p : Semiproposition (setTemplateLanguage 1 (fun _ => 2)) 1) :
    translateFormula (fun _ : Fin 1 => K.shift) (Rewriting.free p) =
      (translateFormula (fun _ : Fin 1 => K) p).free :=
  translate_free_family (fun _ : Fin 1 => K) p
example {n m : Nat} (w : Fin n → SyntacticSemiterm (setTemplateLanguage k arities) m)
    (p : Semiproposition (setTemplateLanguage k arities) n) :
    translateFormula Ks (Rew.subst w ▹ p) =
      (translateFormula Ks p).subst (fun i => translateTerm (V := V) (w i)) :=
  translateFormula_subst Ks w p
