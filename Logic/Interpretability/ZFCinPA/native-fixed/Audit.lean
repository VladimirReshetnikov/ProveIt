import ZFCinPA.NativeFixed

set_option autoImplicit false
noncomputable section

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.NativeInterp LeanProofs.ZFCinPA.NativeFixed
open SetTheory.BusyBeaver.ZFC

#print axioms LeanProofs.ZFCinPA.NativeFixed.fixed_models
#print axioms LeanProofs.ZFCinPA.NativeFixed.wq_zfAxioms
#print axioms LeanProofs.ZFCinPA.NativeFixed.wq_power
#print axioms LeanProofs.ZFCinPA.NativeFixed.wq_regular
#print axioms LeanProofs.ZFCinPA.NativeFixed.models_intF_iff
#print axioms LeanProofs.ZFCinPA.NativeFixed.native_proves_intF
#print axioms LeanProofs.ZFCinPA.NativeFixed.native_proves_domain
#print axioms LeanProofs.ZFCinPA.NativeFixed.emb_comp_embSubsts
#print axioms LeanProofs.ZFCinPA.NativeFixed.emb_atomI
#print axioms LeanProofs.ZFCinPA.NativeFixed.emb_domAtS
#print axioms LeanProofs.ZFCinPA.NativeFixed.emb_intF
#print axioms LeanProofs.ZFCinPA.NativeFixed.quote_intF_sentence
#print axioms LeanProofs.ZFCinPA.NativeFixed.provable_interp_fixed
#print axioms LeanProofs.ZFCinPA.NativeFixed.provable_domain

example {S : Type} [Nonempty S] [SetStructure S]
    (HL : _root_.SetTheory.ZFAxioms (memRel S))
    (hPow : ∀ x : S, ∃ p : S, ∀ z, z ∈ p ↔ ∀ u, u ∈ z → u ∈ x)
    (hReg : ∀ x : S, (∃ z, z ∈ x) → ∃ m, m ∈ x ∧ ¬∃ z, z ∈ m ∧ z ∈ x)
    (σ : SetTheorySentence) (hσ : σ ∈ 𝗘𝗤 ℒₛₑₜ ∪ zfFixed) : S↓[ℒₛₑₜ] ⊧ σ :=
  fixed_models HL hPow hReg σ hσ

section Models
variable {M : Type} [Nonempty M] [SetStructure M]
  [M↓[ℒₛₑₜ] ⊧* NativeSet.nativeTheory]

example : Nonempty (WQ M) := inferInstance

example : _root_.SetTheory.ZFAxioms (memRel (WQ M)) := wq_zfAxioms

example (x : WQ M) : ∃ p : WQ M, ∀ z, z ∈ p ↔ ∀ u, u ∈ z → u ∈ x := wq_power x

example (x : WQ M) (hx : ∃ z, z ∈ x) : ∃ m, m ∈ x ∧ ¬∃ z, z ∈ m ∧ z ∈ x :=
  wq_regular x hx

example (σ : SetTheorySentence) :
    M↓[ℒₛₑₜ] ⊧ intF σ ↔ (WQ M)↓[ℒₛₑₜ] ⊧ σ := models_intF_iff σ
end Models

example (σ : SetTheorySentence) (hσ : σ ∈ 𝗘𝗤 ℒₛₑₜ ∪ zfFixed) :
    NativeSet.nativeTheory ⊢ intF σ := native_proves_intF σ hσ

example : NativeSet.nativeTheory ⊢ (∃⁰ domS : SetTheorySentence) := native_proves_domain

section Embedding
variable {ξ : Type*}

example {ο : Type*} [IsEmpty ο] {n k : ℕ} (v : Fin k → Semiterm ℒₛₑₜ ο n) :
    ((Rew.emb : Rew ℒₛₑₜ ο n ξ n).comp (Rew.embSubsts v)) =
      Rew.embSubsts (fun i ↦ Rew.emb (v i)) := emb_comp_embSubsts v

example {ο : Type*} [IsEmpty ο] {n k : ℕ} (R : (ℒₛₑₜ).Rel k)
    (v : Fin k → Semiterm ℒₛₑₜ ο n) :
    (Rew.emb ▹ atomI R v : Semiformula ℒₛₑₜ ξ n) =
      atomI R (fun i ↦ Rew.emb (v i)) := emb_atomI R v

example {ο : Type*} [IsEmpty ο] {n : ℕ} :
    (Rew.emb ▹ (domAtS n : Semiformula ℒₛₑₜ ο (n + 1)) : Semiformula ℒₛₑₜ ξ (n + 1)) =
      domAtS n := emb_domAtS

example {ο : Type*} [IsEmpty ο] {n : ℕ} (φ : Semiformula ℒₛₑₜ ο n) :
    (Rew.emb ▹ intF φ : Semiformula ℒₛₑₜ ξ n) = intF (Rew.emb ▹ φ) := emb_intF φ
end Embedding

section Internal
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.InternalInterpretation
variable {W : Type} [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (σ : SetTheorySentence) :
    (⌜intF σ⌝ : W) = interp (PN : W) ⌜σ⌝ := quote_intF_sentence σ

example (σ : SetTheorySentence) (hσ : σ ∈ 𝗘𝗤 ℒₛₑₜ ∪ zfFixed) :
    Bootstrapping.Provable NativeSet.nativeTheory (interp (PN : W) ⌜σ⌝) :=
  provable_interp_fixed σ hσ

example : Bootstrapping.Provable NativeSet.nativeTheory (^∃ (dom (PN : W))) := provable_domain
end Internal
