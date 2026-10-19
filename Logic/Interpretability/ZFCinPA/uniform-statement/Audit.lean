import ZFCinPA.UniformStatement

set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.UniformStatementFreshAudit

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA

#print axioms LeanProofs.ZFCinPA.conZFCBodyF_eq
#print axioms LeanProofs.ZFCinPA.free_fNumF
#print axioms LeanProofs.ZFCinPA.toNat_toSet_congr
#print axioms LeanProofs.ZFCinPA.quote_toSet_congr
#print axioms LeanProofs.ZFCinPA.sealCount_zero
#print axioms LeanProofs.ZFCinPA.sealCount_succ
#print axioms LeanProofs.ZFCinPA.quote_toSet_fAllIter
#print axioms LeanProofs.ZFCinPA.quote_conZFCSet
#print axioms LeanProofs.ZFCinPA.numChainCode_natCast
#print axioms LeanProofs.ZFCinPA.conNumCode_natCast
#print axioms LeanProofs.ZFCinPA.sealCountV_natCast
#print axioms LeanProofs.ZFCinPA.allClosure_natCast
#print axioms LeanProofs.ZFCinPA.conZFCBodyCode_natCast
#print axioms LeanProofs.ZFCinPA.conZFCSetCodeFun.defined
#print axioms LeanProofs.ZFCinPA.eval_conZFCSetCodeGraph_iff
#print axioms LeanProofs.ZFCinPA.conZFCSetCode_total
#print axioms LeanProofs.ZFCinPA.conZFCSetCode_functional
#print axioms LeanProofs.ZFCinPA.conZFCSetCode_existsUnique
#print axioms LeanProofs.ZFCinPA.conZFCSetCodeFun_natCast
#print axioms LeanProofs.ZFCinPA.conZFCSetCode_quote_numeral
#print axioms LeanProofs.ZFCinPA.eval_paUniformZFCProvabilitySentence_iff
#print axioms LeanProofs.ZFCinPA.eval_paUniformZFCProvabilitySentence_iff_fun
#print axioms LeanProofs.ZFCinPA.provable_conZFCSet_standard_point
#print axioms LeanProofs.ZFCinPA.paUniformZFCProvability_standard_instance
#print axioms LeanProofs.ZFCinPA.eval_paUniformZFCProvabilitySentence_iff_selector
#print axioms LeanProofs.ZFCinPA.peano_proves_uniformZFCProvability_of_selectorInAllModels
#print axioms LeanProofs.ZFCinPA.peano_proves_uniformZFCProvability_iff_selectorInAllModels

example (n : ℕ) :
    BoundedZFCConsistency.conZFCBodyF n =
      .fAll (.fAll (.fAll (.fAll
        (.fImp (BoundedZFCConsistency.fNumF 3 n) restForm)))) :=
  conZFCBodyF_eq n

example {i k n : ℕ} (h : SetTheory.Free n (BoundedZFCConsistency.fNumF i k)) :
    n = i := free_fNumF h

example (φ : SetTheory.Form) (k₁ k₂ : ℕ)
    (h₁ : ∀ i, SetTheory.Free i φ → i < k₁)
    (h₂ : ∀ i, SetTheory.Free i φ → i < k₂) :
    (toSet k₁ φ).toNat = (toSet k₂ φ).toNat ∧
      ((toSet k₁ φ).neg).toNat = ((toSet k₂ φ).neg).toNat :=
  toNat_toSet_congr φ k₁ k₂ h₁ h₂

example : sealCount 0 = 6 + restFormBound := sealCount_zero

example (m : ℕ) :
    sealCount (m + 1) = (3 + m * succFormBound1 + succFormBound4) + restFormBound :=
  sealCount_succ m

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example {φ : SetTheory.Form} {k₁ k₂ : ℕ}
    (h₁ : ∀ i, SetTheory.Free i φ → i < k₁)
    (h₂ : ∀ i, SetTheory.Free i φ → i < k₂) :
    (⌜toSet k₁ φ⌝ : V) = ⌜toSet k₂ φ⌝ :=
  quote_toSet_congr h₁ h₂

example (f : SetTheory.Form) (m k : ℕ) :
    (⌜toSet k (fAllIter m f)⌝ : V) = qqAllIter m (⌜toSet (k + m) f⌝ : V) :=
  quote_toSet_fAllIter f m k

example (n : ℕ) :
    (⌜conZFCSet n⌝ : V) = ⌜toSet 0 (BoundedZFCConsistency.conZFCForm n)⌝ :=
  quote_conZFCSet n

example (m : ℕ) :
    numChainCode ((m : ℕ) : V) = ⌜toSet 1 (BoundedZFCConsistency.fNumF 0 m)⌝ :=
  numChainCode_natCast m

example (m : ℕ) :
    conNumCode ((m : ℕ) : V) = ⌜toSet 4 (BoundedZFCConsistency.fNumF 3 m)⌝ :=
  conNumCode_natCast m

example (m : ℕ) : sealCountV ((m : ℕ) : V) = ((sealCount m : ℕ) : V) :=
  sealCountV_natCast m

example (c : V) (m : ℕ) : allClosure c ((m : ℕ) : V) = qqAllIter m c :=
  allClosure_natCast c m

example (m : ℕ) :
    conZFCBodyCode ((m : ℕ) : V) =
      ⌜toSet (sealCount m) (BoundedZFCConsistency.conZFCBodyF m)⌝ :=
  conZFCBodyCode_natCast m

example : 𝚺₁-Function₁ (conZFCSetCodeFun : V → V) via conZFCSetCodeGraph :=
  conZFCSetCodeFun.defined

example {c x : V} :
    conZFCSetCodeGraph.val.Evalb ![c, x] ↔ ConZFCSetCode c x :=
  eval_conZFCSetCodeGraph_iff

example (x : V) : ∃ c : V, ConZFCSetCode c x := conZFCSetCode_total x

example {c₁ c₂ x : V} (h₁ : ConZFCSetCode c₁ x) (h₂ : ConZFCSetCode c₂ x) :
    c₁ = c₂ := conZFCSetCode_functional h₁ h₂

example (x : V) : ∃! c : V, ConZFCSetCode c x := conZFCSetCode_existsUnique x

example (n : ℕ) : conZFCSetCodeFun ((n : ℕ) : V) = ⌜conZFCSet n⌝ :=
  conZFCSetCodeFun_natCast n

example (n : ℕ) : ConZFCSetCode (⌜conZFCSet n⌝ : V) (ORingStructure.numeral n) :=
  conZFCSetCode_quote_numeral n

example : paUniformZFCProvabilitySentence.Evalb (M := V) ![] ↔
    ∀ x : V, ∃ c : V, ConZFCSetCode c x ∧ Provable 𝗭𝗙𝗖 c :=
  eval_paUniformZFCProvabilitySentence_iff

example : paUniformZFCProvabilitySentence.Evalb (M := V) ![] ↔
    ∀ x : V, Provable 𝗭𝗙𝗖 (conZFCSetCodeFun x) :=
  eval_paUniformZFCProvabilitySentence_iff_fun

example (n : ℕ) : Provable 𝗭𝗙𝗖 (⌜conZFCSet n⌝ : V) :=
  provable_conZFCSet_standard_point n

example (n : ℕ) :
    ∃ c : V, ConZFCSetCode c (ORingStructure.numeral n) ∧ Provable 𝗭𝗙𝗖 c :=
  paUniformZFCProvability_standard_instance n

example : paUniformZFCProvabilitySentence.Evalb (M := V) ![] ↔ ZFCProofSelectorIn V :=
  eval_paUniformZFCProvabilitySentence_iff_selector
end Models

example (hselector : ZFCProofSelectorInAllModels) :
    Peano ⊢ paUniformZFCProvabilitySentence :=
  peano_proves_uniformZFCProvability_of_selectorInAllModels hselector

example : (Peano ⊢ paUniformZFCProvabilitySentence) ↔ ZFCProofSelectorInAllModels :=
  peano_proves_uniformZFCProvability_iff_selectorInAllModels

end LeanProofs.ZFCinPA.UniformStatementFreshAudit
