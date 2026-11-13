import DiophantineConsistency.SharingSeed38
import DiophantineConsistency.ForwardWitness38
import DiophantineConsistency.ModelThirteenCarrierPrelude

/-! UNCOMPILED DRAFT. Conditional assembly of the 38-seed model bridge.
The explicit extraction and witness-construction obligations are not proved. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingNormCompose
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ModelArithmetic
open FreshCarrierSpheres
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Four natural model representatives, with the high mask shifted once. -/
def naturalPorts : Fin 4 → V :=
  ![(CurrentMasks2011.beta : V), (CurrentKernel2011.K : V),
    (CurrentMasks2011.lowPort : V), (((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V))]

/-- The first 14 witness coordinates encode the original positive inputs. -/
def inputPrefix (w : Fin 38 → V) : Fin 14 → V :=
  fun j => w (Fin.castLE (by decide : 14 ≤ 38) j)

/-- The five original unit norms in the model's ring of differences. -/
def unitNorms (u : Fin 14 → V) : Prop :=
  let d := Carrier65.core (ModelThirteenCarrier.ringPorts (V := V))
    (fun j => ι (u j + 1))
  d.P = 1 ∧ d.Q = 1 ∧ d.U = 1 ∧ Carrier65.strong d = 1 ∧ d.W = 1

/-- The fixed current seed at Jones input 1. -/
def seedZero (w : Fin 38 → V) : Prop :=
  InternalZero (SharingSeed38.seed CurrentWindowCarry2011.ports) (Fin.cons 1 w)

/-- Candidate reuse of the checked norm theorem; this file is uncompiled. -/
theorem current_zero_iff_unitNorms (u : Fin 14 → V) :
    InternalZero ObjectCurrentEquation2011.naturalExpression u ↔ unitNorms u := by
  change InternalZero (ObjectCurrentEquation2011.positiveShift ObjectCurrentEquation2011.expression) u ↔ _
  rw [ObjectCurrentEquation2011.internalZero_positiveShift, internalZero_iff,
    ObjectCurrentEquation2011.expression, FreshModel106.evalRing_expressionAt65]
  exact FreshCarrierSpheres.value65_zero_iff_norms FreshCarrierSpheres.modelFacts
    (ModelThirteenCarrier.ringPorts (V := V)) (fun j => ι (u j + 1))
    FreshModel106.beta_pos (fun j => ι_pos (lt_of_lt_of_le _root_.zero_lt_one le_add_self))

end Model

/-- Unresolved: extract the original unit norms from any seed-zero witness. -/
def Extraction : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (w : Fin 38 → V),
    seedZero w → unitNorms (inputPrefix w)

/-- Unresolved: the generated semiring assignment satisfies the seed if the
original five unit norms hold. -/
def Construction : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (u : Fin 14 → V),
    unitNorms u → seedZero (SharingForward38.witnessCoordinates (naturalPorts (V := V)) u)

/-- Candidate assembly, conditional on the two genuinely unproved obligations. -/
theorem existential_seed_iff_current (hextract : Extraction) (hconstruct : Construction)
    (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    (∃ w : Fin 38 → V, seedZero w) ↔
      ∃ u : Fin 14 → V, InternalZero ObjectCurrentEquation2011.naturalExpression u := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨inputPrefix w, (current_zero_iff_unitNorms _).mpr (hextract V w hw)⟩
  · rintro ⟨u, hu⟩
    exact ⟨SharingForward38.witnessCoordinates (naturalPorts (V := V)) u,
      hconstruct V u ((current_zero_iff_unitNorms u).mp hu)⟩

-- Remaining: prove Extraction and Construction from the frozen residuals,
-- port cast lemmas, model sum-of-squares and topological graph identities.
end DiophantineConsistency.SharingNormCompose
