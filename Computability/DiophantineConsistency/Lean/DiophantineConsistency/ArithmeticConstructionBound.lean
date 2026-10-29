import DiophantineConsistency.ArithmeticConstructionAssembly
import DiophantineConsistency.ArithmeticConstructionZero
import DiophantineConsistency.ArithmeticCurrentSentence2011
import DiophantineConsistency.ArithmeticLocalNormalization
import DiophantineConsistency.ArithmeticConstructionBoundPell

/-! **K7 with an explicit witness bound**: if the represented decimal215 run is
halted at an internal time `T`, the literal fourteen-variable current
polynomial has a positive zero all of whose coordinates are at most
`zeroBound T`, an explicit elementary (𝚺₁-definable) term in `T` built from
`+`, `*`, `Exp.exp` and `ArithmeticPow.power` with a fixed nesting depth.

Tracing `ArithmeticConstructionAssembly.construction` (whose shared proof
records the sizes):

* dimensions: `N = 120199^(2T+4)` exactly, `q = 2^(94517*N)` exactly;
* K-stage coordinates `J, F, α ≤ q` (repunit and `C+F+α = q`);
* rank `R ≤ Rq q = (q²+q)q² + (q+2q²)q` (the rank formula, with the standard
  masks `lowPort, highPort, β < 2^94517 ≤ q`);
* derived multiplier `w' = 2^(R−94517N) ≤ 2^R`, and `z ≤ (q+2^R+1)q`
  from the transport equation (the kernel `K < 2^(2·94517) ≤ q` comes from the
  proved Local Normalization product bound);
* Pell coordinates via `ArithmeticConstructionBoundPell` (bounds `Ys … Us`).

`zeroBound T = Wb (Q T) (Rq (Q T))` with `Q T = 2^(94517*120199^(2T+4))`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.ArithmeticConstructionBound
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticWindowDigits ArithmeticPackingBlocks ArithmeticPacking
  ArithmeticPackingCells ArithmeticWangTable ArithmeticWangPlane ArithmeticRepunit
  ArithmeticBinaryPopulation ArithmeticPellRecurrence ArithmeticConstructionAssembly
  ArithmeticConstructionBoundPell
open ArithmeticCantor (first)
open ArithmeticMachineRun215 (run)
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem construction_below (T : V) (hT : first (ArithmeticMachineRun215.run T) = 0) :
    ∃ v : Fin 14 → V, (∀ j, 0 < v j) ∧ v 1 ≤ (CurrentMasks2011.beta : V) * v 0 + 1 ∧
      ArithmeticCarrierSoundness2011.Equations (CurrentMasks2011.beta : V)
        (CurrentKernel2011.K : V) (CurrentMasks2011.lowPort : V)
        ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V) v ∧
      ∀ j, v j ≤ zeroBound T := by
  exact construction_below_hL ArithmeticLocalNormalization.localNormalization T hT

/-! ## The main statement -/

/-- **Halting gives a positive zero below an explicit elementary bound.** -/
theorem halt_positive_zero_below (T : V) (hT : first (ArithmeticMachineRun215.run T) = 0) :
    ∃ u : Fin 14 → V, ArithmeticCurrentSentence2011.PositiveZero u ∧ ∀ j, u j ≤ zeroBound T := by
  obtain ⟨v, hv, hF, heq, hb⟩ := construction_below T hT
  exact ⟨v, ⟨hv, ArithmeticConstructionZero.current_zero v hv hF heq⟩, hb⟩

/-! ## Definability of the bound -/

instance Ys_definable : 𝚺₁-Function₁ (Ys : V → V) := by unfold Ys; definability
instance As_definable : 𝚺₁-Function₁ (As : V → V) := by unfold As; definability
instance Bs_definable : 𝚺₁-Function₁ (Bs : V → V) := by unfold Bs; definability
instance Ps_definable : 𝚺₁-Function₁ (Ps : V → V) := by unfold Ps; definability
instance Gs_definable : 𝚺₁-Function₁ (Gs : V → V) := by unfold Gs; definability
instance Fs_definable : 𝚺₁-Function₁ (Fs : V → V) := by unfold Fs; definability
instance Is_definable : 𝚺₁-Function₁ (Is : V → V) := by unfold Is; definability
instance Us_definable : 𝚺₁-Function₁ (Us : V → V) := by unfold Us; definability
instance Nb_definable : 𝚺₁-Function₁ (Nb : V → V) := by unfold Nb; definability
instance Q_definable : 𝚺₁-Function₁ (Q : V → V) := by unfold Q; definability
instance Rq_definable : 𝚺₁-Function₁ (Rq : V → V) := by unfold Rq; definability
instance Wb_definable : 𝚺₁-Function₂ (Wb : V → V → V) := by unfold Wb; definability

/-- **The witness bound is 𝚺₁-definable.** -/
instance zeroBound_definable : 𝚺₁-Function₁ (zeroBound : V → V) := by
  unfold zeroBound; definability

end DiophantineConsistency.ArithmeticConstructionBound
