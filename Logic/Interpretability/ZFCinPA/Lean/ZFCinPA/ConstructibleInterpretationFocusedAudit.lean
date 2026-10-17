import ZFCinPA.ConstructibleInterpretation

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.ConstructibleInterpretation
open LeanProofs.ZFCinPA.NativeZFContainers254 (memRel)
open LeanProofs.BoundedPAConsistency.InternalRelativization
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.inLSyn_eq
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.sat_inLForm
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.eval_domL
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.eval_domAt
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.eval_relF
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.models_relF_iff
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.modelsZ_of_modelsZF
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.repl_clauseZF
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.zfAxioms_of_modelsZF
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.power_of_modelsZF
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.regular_of_modelsZF
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.inLV_nonempty
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.L_models
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.zf_proves_relL
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.zf_proves_exists_L
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.quote_domAt
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.quote_relF
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.quote_relF_sentence
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.isSemiformula_quote_domL
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.shift_quote_domL
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.provable_exists_L
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.mem_ZFC_class
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.standard_of_mem_class
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.standard_obligation
#print axioms LeanProofs.ZFCinPA.ConstructibleInterpretation.provable_falsum_ZF_of_ZFC

example {M : Type*} {mem : M → M → Prop} (H : _root_.SetTheory.ZFAxioms mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ _root_.SetTheory.Sub mem x a) (x : Nat) :
    inLSyn x=SetTheory.BusyBeaver.ZFC.Constructible.inLF H hP x := inLSyn_eq H hP x
example {M : Type*} [SetStructure M] (H : _root_.SetTheory.ZFAxioms (memRel M))
    (hP : ∀ a, ∃ p, ∀ x, memRel M x p ↔ _root_.SetTheory.Sub (memRel M) x a)
    (x : M) (ε : Empty → M) : domL.Eval ![x] ε ↔ SetTheory.BusyBeaver.ZFC.Constructible.InL H hP x :=
  eval_domL H hP x ε

section OrdinaryZF
variable {M : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
example : _root_.SetTheory.ZFAxioms (memRel M) := zfAxioms_of_modelsZF
example (a : M) : ∃ p : M, ∀ x, memRel M x p ↔ _root_.SetTheory.Sub (memRel M) x a :=
  power_of_modelsZF a
example : SetTheory.BusyBeaver.ZFC.InternalOrd.Regular (memRel M) := regular_of_modelsZF
local instance : SetStructure {x : M // InLV x} := subtypeSetStructure (InLV (V := M))
example (σ : SetTheorySentence) (hσ : σ ∈ 𝗘𝗤 ℒₛₑₜ ∪ zfFixed ∪ 𝗔𝗖) :
    {x : M // InLV x}↓[ℒₛₑₜ] ⊧ σ := L_models σ hσ
end OrdinaryZF

example (σ : SetTheorySentence) (hσ : σ ∈ 𝗘𝗤 ℒₛₑₜ ∪ zfFixed ∪ 𝗔𝗖) :
    𝗭𝗙 ⊢ relF domL σ := zf_proves_relL σ hσ
example : 𝗭𝗙 ⊢ (∃⁰ domL : SetTheorySentence) := zf_proves_exists_L

section Internal
variable {W : Type*} [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (n : Nat) : (⌜(domAt domL n : SetTheorySemiproposition (n+1))⌝ : W)=⌜domL⌝ :=
  quote_domAt n
example {n : Nat} (φ : SetTheorySemiproposition n) :
    (⌜relF domL φ⌝ : W)=relativize ℒₛₑₜ (⌜domL⌝ : W) ⌜φ⌝ := quote_relF φ
example (σ : SetTheorySentence) :
    (⌜relF domL σ⌝ : W)=relativize ℒₛₑₜ (⌜domL⌝ : W) ⌜σ⌝ := quote_relF_sentence σ
example : IsSemiformula ℒₛₑₜ 1 (⌜domL⌝ : W) := isSemiformula_quote_domL
example : shift ℒₛₑₜ (⌜domL⌝ : W)=⌜domL⌝ := shift_quote_domL
example : Provable 𝗭𝗙 (^∃ (⌜domL⌝ : W)) := provable_exists_L
example (p : W) (hp : p ∈ (𝗘𝗤 ℒₛₑₜ : SetTheory).Δ₁Class ∨ p ∈ zfFixed.Δ₁Class ∨
      p ∈ (𝗔𝗖 : SetTheory).Δ₁Class) :
    ∃ σ ∈ 𝗘𝗤 ℒₛₑₜ ∪ zfFixed ∪ 𝗔𝗖, p=⌜σ⌝ := standard_of_mem_class hp
example (p : W) (hp : p ∈ (𝗘𝗤 ℒₛₑₜ : SetTheory).Δ₁Class ∨ p ∈ zfFixed.Δ₁Class ∨
      p ∈ (𝗔𝗖 : SetTheory).Δ₁Class) :
    ∃ m, Derivable 𝗭𝗙 (insert (relativize ℒₛₑₜ (⌜domL⌝ : W) p) (domSet ℒₛₑₜ (⌜domL⌝ : W) m)) :=
  standard_obligation hp
example
    (hSchema : ∀ p : W, IsFormula ℒₛₑₜ p →
      p ∈ separationTheory.Δ₁Class ∨ p ∈ replacementTheory.Δ₁Class →
      ∃ m, Derivable 𝗭𝗙 (insert (relativize ℒₛₑₜ (⌜domL⌝ : W) p) (domSet ℒₛₑₜ (⌜domL⌝ : W) m)))
    (h : Provable 𝗭𝗙𝗖 (^⊥ : W)) : Provable 𝗭𝗙 (^⊥ : W) :=
  provable_falsum_ZF_of_ZFC hSchema h
example (p : W) (hp : p ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class) :
    p ∈ (𝗘𝗤 ℒₛₑₜ : SetTheory).Δ₁Class ∨ p ∈ zfFixed.Δ₁Class ∨ p ∈ (𝗔𝗖 : SetTheory).Δ₁Class ∨
      p ∈ separationTheory.Δ₁Class ∨ p ∈ replacementTheory.Δ₁Class := mem_ZFC_class hp
end Internal
