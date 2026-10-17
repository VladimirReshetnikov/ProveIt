import ZFCinPA.CompiledCollection254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.CollectionTemplate254
open LeanProofs.ZFCinPA.CompiledCollection254
open scoped LO.FirstOrder.Arithmetic
#print axioms LeanProofs.ZFCinPA.CompiledCollection254.equality_cases
#print axioms LeanProofs.ZFCinPA.CompiledCollection254.translated_equality
#print axioms LeanProofs.ZFCinPA.CompiledCollection254.translated_axiom
#print axioms LeanProofs.ZFCinPA.CompiledCollection254.collectionProof
#print axioms LeanProofs.ZFCinPA.CompiledCollection254.collectionProof_isProof
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    (𝗭𝗙 : SetTheory).internalize V ⊢!
      translateFormula (fun _ : Fin 1 => K) (Rewriting.emb collectionSentence) :=
  collectionProof K
example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    Proof (𝗭𝗙 : SetTheory) (collectionProof K).val
      (translateFormula (fun _ : Fin 1 => K) (Rewriting.emb collectionSentence)).val :=
  collectionProof_isProof K
example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    (𝗭𝗙 : SetTheory).internalize V ⊢!
      translateFormula (fun _ : Fin 1 => K.shift) (Rewriting.emb collectionSentence) :=
  collectionProof K.shift
example (c : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢!
      translateFormula (fun _ : Fin 1 => Bootstrapping.Semiformula.rel Language.Set.Rel.mem
        ![.bvar 0,.fvar c]) (Rewriting.emb collectionSentence) :=
  collectionProof _
example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2)
    (σ : Sentence Lang) (h : σ ∈ 𝗘𝗤 Lang) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ translateFormula (fun _ : Fin 1 => K) (Rewriting.emb σ) :=
  translated_equality (fun _ => K) σ h
example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    (𝗭𝗙 : SetTheory).internalize V ⊢
      translateFormula (fun _ : Fin 1 => K) (Rewriting.emb witnessSeparation) :=
  translated_axiom (fun _ => K) _ (Or.inr (Or.inr (by simp)))
example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    (𝗭𝗙 : SetTheory).internalize V ⊢
      translateFormula (fun _ : Fin 1 => K) (Rewriting.emb rankReplacement) :=
  translated_axiom (fun _ => K) _ (Or.inr (Or.inr (by simp)))
example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    (𝗭𝗙 : SetTheory).internalize V ⊢
      translateFormula (fun _ : Fin 1 => K) (Rewriting.emb outputSeparation) :=
  translated_axiom (fun _ => K) _ (Or.inr (Or.inr (by simp)))
