import ConPAISigma1Transfer
import ConPAMachine

/-!
# The obligation for a machine, and what it gives

`Calibrated T h` is the statement that is left for a transition table `T` with halting state
`h`: in every model `V` of `𝗜𝚺₁`, Foundation's `𝗣𝗔` proves `⊥` in the sense of `V` exactly when
the run of `T` inside `V` reaches the state `h`. Both the proof and the halting time may be
nonstandard elements of `V`.

`endpoint`: from `Calibrated T h` and the PA witness certificate, standard iPRA proves that PA
is consistent if and only if the machine does not halt. No table is shown to be calibrated
here.
-/
set_option autoImplicit false
noncomputable section
namespace ConPA.MachineEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open DiophantineConsistency.StrictSigmaOneInduction
open ConPA.ISigma1Transfer ConPA.Machine

/-- In every model of `𝗜𝚺₁`: `𝗣𝗔` refutes itself internally iff the run reaches `h`. -/
def Calibrated (T : Table) (h : ℕ) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    Provable (𝗣𝗔 : ArithmeticTheory) (⌜(⊥ : ArithmeticSentence)⌝ : V) ↔
      ∃ t : V, π₁ (run T t) = (h : V)

theorem isigma1_iff (T : Table) (h : ℕ) (hc : Calibrated T h) :
    𝗜𝚺₁ ⊢ (paRefutation 🡘 (haltDef T h).val) := by
  refine complete.{0} _ _ fun M _ hM => ?_
  haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := hM
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply]
  have hp : paRefutation.Evalb (M := M) ![] ↔
      Provable (𝗣𝗔 : ArithmeticTheory) (⌜(⊥ : ArithmeticSentence)⌝ : M) := by
    simp [paRefutation, provabilityPred, Provable]
  have hh := haltDef_iff (V := M) T h
  have hm := hc M
  exact ⟨fun a => hh.mpr (hm.mp (hp.mp a)), fun a => hp.mpr (hm.mpr (hh.mp a))⟩

/-- The halting sentence of iPRA for the table `T` and the halting state `h`. -/
def machineHaltSentence (T : Table) (h : ℕ) : Sentenceᵢ DiophantineConsistency.PRALanguage.language :=
  haltSentence (bnd (haltDef T h).val)

/-- **A calibrated table gives the iPRA equivalence.** -/
theorem endpoint (T : Table) (h : ℕ) (hc : Calibrated T h) (hb : BoundCertificate) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence T h :=
  endpoint_sigma_one _ (haltDef_sigma_one T h) (isigma1_iff T h hc) hb

#print axioms isigma1_iff
#print axioms endpoint
end ConPA.MachineEndpoint
