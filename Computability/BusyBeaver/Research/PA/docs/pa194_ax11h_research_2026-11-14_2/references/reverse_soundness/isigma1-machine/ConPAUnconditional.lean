import ConPAISigma1Models
import ConPAMachineEndpoint
import PA196PACertificateComplete

/-!
# The transfers with the PA witness certificate discharged

`ConPA.ISigma1Transfer.BoundCertificate` is the proposition
`PA196ReverseGG.BoundCertificate`, which `PA196PACertificateComplete.certificate` proves. This
file instantiates the transfer theorems with it, so that they have no hypothesis besides the
machine statement.

* `ipra_of_models`: for a bounded open halting matrix `halt` of the PRA language, if halting
  and the mapped PA refutation agree in every candidate PRA model whose arithmetic reduct
  satisfies `𝗜𝚺₁`, then standard iPRA proves that PA is consistent if and only if the machine
  does not halt.
* `machine_endpoint`: the same from `Calibrated T h` for a transition table.

No machine statement is proved here.
-/
set_option autoImplicit false
noncomputable section
namespace ConPA.Unconditional
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRATheory DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRANativeForwardTheory
open ConPA.ISigma1Transfer ConPA.ISigma1Models ConPA.Machine ConPA.MachineEndpoint
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

/-- The PA witness certificate, proved in `pa196-vs-u208/ipra`. -/
theorem certificate : BoundCertificate := PA196PACertificateComplete.certificate

/-- A calibrated table gives the iPRA equivalence. -/
theorem machine_endpoint (T : Table) (h : ℕ) (hc : Calibrated T h) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence T h :=
  ConPA.MachineEndpoint.endpoint T h hc certificate

/-- The two classical reductions for a halting matrix of the PRA language. -/
theorem classical_reductions (halt : Semisentence language 1) (hopen : halt.Open)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M →
        ((M↓[language] ⊧ ∃⁰ halt) ↔ (M↓[language] ⊧ mappedPARefutation))) :
    PRA ⊢ (mappedPARefutation 🡒 ∃⁰ halt) ∧ PRA ⊢ ((∃⁰ halt) 🡒 mappedPARefutation) :=
  ⟨forward_of_models halt hopen h certificate, reverse_of_models halt hopen h certificate⟩

/-- **The iPRA equivalence from a model statement.** `native (∃⁰ halt)` is the halting
sentence of iPRA with the matrix `halt`. -/
theorem ipra_of_models (halt : Semisentence language 1) (hopen : halt.Open)
    (hbounded : Hierarchy 𝚺 0 halt)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M →
        ((M↓[language] ⊧ ∃⁰ halt) ↔ (M↓[language] ⊧ mappedPARefutation))) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼native (∃⁰ halt) := by
  obtain ⟨hfwd, hrev⟩ := classical_reductions halt hopen h
  have hggf : nativeTheory ⊢ mappedPARefutationᴺ 🡒 (∃⁰ halt)ᴺ :=
    DiophantineConsistency.IPRAImpGG.unpack_imp_image nativeTheory _ _
      (DiophantineConsistency.IPRAFullGGTransfer.from_classical hfwd)
  have hggr : nativeTheory ⊢ (∃⁰ halt)ᴺ 🡒 mappedPARefutationᴺ :=
    DiophantineConsistency.IPRAImpGG.unpack_imp_image nativeTheory _ _
      (DiophantineConsistency.IPRAFullGGTransfer.from_classical hrev)
  have hback : nativeTheory ⊢! (∃⁰ halt)ᴺ 🡒 ∼∼native (∃⁰ halt) := by
    simpa only [native] using exists_backward halt hbounded
  have hf : nativeTheory ⊢! nativePARefutation 🡒 ∼∼native (∃⁰ halt) :=
    Entailment.C_trans (theoryNativeForward mappedPARefutation)
      (Entailment.C_trans (Classical.choice hggf) hback)
  have hr : nativeTheory ⊢! native (∃⁰ halt) 🡒 ∼∼nativePARefutation :=
    Entailment.C_trans (theoryNativeForward (∃⁰ halt))
      (Entailment.C_trans (Classical.choice hggr) (refutation_backward certificate))
  have hf' := Classical.choice ((DiophantineConsistency.IPRAStandardTheory.provable_iff _).2 ⟨hf⟩)
  have hr' := Classical.choice ((DiophantineConsistency.IPRAStandardTheory.provable_iff _).2 ⟨hr⟩)
  refine ⟨?_⟩
  unfold nativePAConsistency
  exact Entailment.K_intro
    (Entailment.C_trans Entailment.dni (Entailment.contra hr'))
    (Entailment.C_trans Entailment.dni (Entailment.contra hf'))

#print axioms certificate
#print axioms machine_endpoint
#print axioms ipra_of_models
end ConPA.Unconditional
