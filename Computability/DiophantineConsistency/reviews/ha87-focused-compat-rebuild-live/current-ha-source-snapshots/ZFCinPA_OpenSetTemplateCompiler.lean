import ZFCinPA.SetPlaceholders
import ZFCinPA.BufferedTemplateProofCompiler

set_option autoImplicit false

/-!
Instantiate the finite-buffer compiler at arbitrary internal set predicates.
No predicate is assumed shift-fixed. Source axiom translations still require
actual target proof callbacks; this module does not supply Collection schemas.
-/
namespace LeanProofs.ZFCinPA.OpenSetTemplateCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.BufferedTemplateProofCompiler
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {k : Nat} {arities : Fin k → Nat}

lemma translate_shift_family
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {n : Nat} (p : Semiproposition (setTemplateLanguage k arities) n) :
    translateFormula (fun i => (Ks i).shift) (Rewriting.shift p) =
      (translateFormula Ks p).shift := by
  induction p using FirstOrder.Semiformula.rec' with
  | hverum => simp [translateFormula]
  | hfalsum => simp [translateFormula]
  | @hrel n m r v =>
      rcases r with r | r
      · simp [translateFormula,translateTerm_shift,Matrix.map,Function.comp_def]
      · simp [translateFormula,Bootstrapping.Semiformula.shift_substs,Matrix.map,Function.comp_def]
  | @hnrel n m r v =>
      rcases r with r | r
      · simp [translateFormula,translateTerm_shift,Matrix.map,Function.comp_def]
      · simp [translateFormula,Bootstrapping.Semiformula.shift_substs,Matrix.map,Function.comp_def]
  | hand p q hp hq => simp [translateFormula,hp,hq]
  | hor p q hp hq => simp [translateFormula,hp,hq]
  | hall p hp => simp [translateFormula,hp]
  | hexs p hp => simp [translateFormula,hp]

lemma translate_free_family
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (p : Semiproposition (setTemplateLanguage k arities) 1) :
    translateFormula (fun i => (Ks i).shift) (Rewriting.free p) =
      (translateFormula Ks p).free := by
  rw [←LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free]
  rw [translateFormula_subst,translate_shift_family]
  unfold Bootstrapping.Semiformula.free
  congr 1
  funext i
  have hi : i=0 := Fin.eq_zero i
  subst i
  rfl

noncomputable def shiftedPredicates
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)) :
    Nat → (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)
  | 0 => Ks
  | b+1 => fun i => (shiftedPredicates Ks b i).shift

noncomputable def openTranslation
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)) :
    BufferedTranslation V (setTemplateLanguage k arities) ℒₛₑₜ where
  term := translateTerm
  formula := fun b => translateFormula (shiftedPredicates Ks b)
  neg := fun b {_} p => translateFormula_neg _ p
  and := fun _ {_} _ _ => rfl
  or := fun _ {_} _ _ => rfl
  verum := fun _ => rfl
  all := fun _ {_} _ => rfl
  exs := fun _ {_} _ => rfl
  shift := fun b {_} p => translate_shift_family (shiftedPredicates Ks b) p
  free := fun b p => translate_free_family (shiftedPredicates Ks b) p
  subst₁ := fun b p t => translateFormula_subst (shiftedPredicates Ks b) ![t] p

/-- The source theory can contain predicate-dependent schema instances, provided
its translated instances have actual internal proofs at every finite buffer. -/
noncomputable def compileOpenTemplate
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {T : Theory (setTemplateLanguage k arities)} {U : InternalTheory V ℒₛₑₜ}
    (axiomProof : ∀ b (σ : Sentence (setTemplateLanguage k arities)), σ ∈ T →
      U ⊢! translateFormula (shiftedPredicates Ks b) (Rewriting.emb σ))
    {σ : Sentence (setTemplateLanguage k arities)} (d : T ⊢! σ) :
    U ⊢! translateFormula Ks (Rewriting.emb σ) :=
  compileProof (openTranslation Ks) axiomProof d

lemma compileOpenTemplate_isProof
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {T : Theory (setTemplateLanguage k arities)} {U : InternalTheory V ℒₛₑₜ}
    (axiomProof : ∀ b (σ : Sentence (setTemplateLanguage k arities)), σ ∈ T →
      U ⊢! translateFormula (shiftedPredicates Ks b) (Rewriting.emb σ))
    {σ : Sentence (setTemplateLanguage k arities)} (d : T ⊢! σ) :
    Proof U.theory (compileOpenTemplate Ks axiomProof d).val
      (translateFormula Ks (Rewriting.emb σ)).val := by
  simpa [Proof] using (compileOpenTemplate Ks axiomProof d).derivationOf

end LeanProofs.ZFCinPA.OpenSetTemplateCompiler
