import DiophantineConsistency.ArithmeticConstructionUnboundedCompat
import DiophantineConsistency.ArithmeticAdaptiveConstructionReduced2011

/-! Direct link from an unbounded assembly to the 87-gate zero.
The finite witness vector supplies the bound required by the reduced construction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionRunDraft2011
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor (first)
open ArithmeticPackingCells ArithmeticConstructionBound
  ArithmeticAdaptiveConstructionReduced2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Draft: the run and local-normalization premises supply an 87-gate zero. -/
theorem reduced_zero_of_run (hL : LocalNormalization) (T : V)
    (hT : first (ArithmeticMachineRun215.run T)=0) :
    ∃ x : Fin 13 → V,
      AdaptiveEquationSyntax2011.InternalZero AdaptiveFirstRootFactor87Literal.naturalExpression87 x := by
  obtain ⟨v, hv, hf, heq, hphase, hy, hseed⟩ :=
    ArithmeticConstructionUnboundedCompat.construction_unbounded_seed_phase_hL hL T hT
  let B : V := ∑ j : Fin 14, v j
  have hb : ∀ j, v j ≤ B := by
    intro j
    exact Finset.single_le_sum (fun _ _ => Arithmetic.zero_le _) (Finset.mem_univ j)
  exact reduced_zero_of_enriched_assembly B ⟨v, hv, hf, heq, hb, hphase, hy, hseed⟩
end DiophantineConsistency.ArithmeticAdaptiveConstructionRunDraft2011
