import ZFCinPA.BufferedTemplateProofCompiler
set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.BufferedTemplateProofCompiler
open LeanProofs.ZFCinPA.ModelCodedShiftCancellation
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L₁ L₂ : Language} [L₁.DecidableEq] [L₂.Encodable] [L₂.LORDefinable]
variable {T₁ : Theory L₁} {T₂ : InternalTheory V L₂}
variable (tr : BufferedTranslation V L₁ L₂)
variable (ax : ∀ b (σ : Sentence L₁), σ ∈ T₁ → T₂ ⊢! tr.formula b (Rewriting.emb σ))
#print axioms LeanProofs.ZFCinPA.BufferedTemplateProofCompiler.translateSequent_insert
#print axioms LeanProofs.ZFCinPA.BufferedTemplateProofCompiler.BufferedTranslation.sequent_shift
#print axioms LeanProofs.ZFCinPA.BufferedTemplateProofCompiler.BufferedTranslation.closed_buffer
#print axioms LeanProofs.ZFCinPA.BufferedTemplateProofCompiler.bufferBound
#print axioms LeanProofs.ZFCinPA.BufferedTemplateProofCompiler.compileDerivation
#print axioms LeanProofs.ZFCinPA.BufferedTemplateProofCompiler.compileProof
#print axioms LeanProofs.ZFCinPA.BufferedTemplateProofCompiler.compileProof_isProof
example (b : Nat) (Γ : Finset (Proposition L₁)) :
    translateSequent (tr.formula (b+1)) (Γ.image Rewriting.shift) =
      (translateSequent (tr.formula b) Γ).shift := tr.sequent_shift b Γ
example (p : Proposition L₁) (hp : Rewriting.shift p = p) (b : Nat) :
    tr.formula b p = shiftN b (tr.formula 0 p) := tr.closed_buffer p hp b
example (Γ : Finset (Proposition L₁)) (d : T₁ ⟹₂ Γ) (b : Nat) (h : bufferBound d ≤ b) :
    T₂ ⊢!ᵈᵉʳ translateSequent (tr.formula b) Γ := compileDerivation tr ax d b h
example (Γ : Finset (Proposition L₁)) (d : T₁ ⟹₂ Γ) :
    T₂ ⊢!ᵈᵉʳ translateSequent (tr.formula (bufferBound d)) Γ :=
  compileDerivation tr ax d _ (Nat.le_refl _)
example (σ : Sentence L₁) (d : T₁ ⊢! σ) : T₂ ⊢! tr.formula 0 (Rewriting.emb σ) :=
  compileProof tr ax d
example (σ : Sentence L₁) (d : T₁ ⊢! σ) :
    Proof T₂.theory (compileProof tr ax d).val (tr.formula 0 (Rewriting.emb σ)).val :=
  compileProof_isProof tr ax d
example (Γ : Finset (Proposition L₁)) (d : T₁ ⟹₂ Γ) :
    bufferBound (Derivation2.shift d) = bufferBound d + 1 := rfl
example (Γ : Finset (Proposition L₁)) (p : Semiproposition L₁ 1)
    (h : ∀⁰ p ∈ Γ) (d : T₁ ⟹₂ insert (Rewriting.free p) (Γ.image Rewriting.shift)) :
    bufferBound (Derivation2.all h d) = bufferBound d := rfl
example (σ : Sentence L₁) (b : Nat) :
    tr.formula b (Rewriting.emb σ) = shiftN b (tr.formula 0 (Rewriting.emb σ)) :=
  tr.closed_buffer _ (by simp) b
