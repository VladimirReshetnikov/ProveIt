import DiophantineConsistency.Norm38SeedStaticIff
import DiophantineConsistency.CurrentKernelData2011

/-! Candidate fixed-current-port model casts and static-seed specialization. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38CurrentPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def naturalPorts : Fin 4 → V :=
  ![(CurrentMasks2011.beta : V), (CurrentKernel2011.K : V),
    (CurrentMasks2011.lowPort : V),
    (((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V))]

abbrev ringPorts : Fin 4 → DiffRing V :=
  fun j => ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V)

theorem port0 : (ringPorts (V := V)) 0 = ι (CurrentMasks2011.beta : V) := by
  show ((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) = _
  rw [show CurrentWindowCarry2011.ports 0 = (CurrentMasks2011.beta : ℤ) from rfl,
    Int.cast_natCast, map_natCast]
theorem port1 : (ringPorts (V := V)) 1 = ι (CurrentKernel2011.K : V) := by
  show ((CurrentWindowCarry2011.ports 1 : ℤ) : DiffRing V) = _
  rw [show CurrentWindowCarry2011.ports 1 = (CurrentKernel2011.K : ℤ) from rfl,
    Int.cast_natCast, map_natCast]
theorem port2 : (ringPorts (V := V)) 2 = ι (CurrentMasks2011.lowPort : V) := by
  show ((CurrentWindowCarry2011.ports 2 : ℤ) : DiffRing V) = _
  rw [show CurrentWindowCarry2011.ports 2 = (CurrentMasks2011.lowPort : ℤ) from rfl,
    Int.cast_natCast, map_natCast]
theorem port3 : (ringPorts (V := V)) 3 =
    ι (((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V)) := by
  show ((CurrentWindowCarry2011.ports 3 : ℤ) : DiffRing V) = _
  rw [show CurrentWindowCarry2011.ports 3 =
    (CurrentMasks2011.highPort : ℤ) + (CurrentMasks2011.beta : ℤ) from rfl,
    Int.cast_add, Int.cast_natCast, Int.cast_natCast, map_natCast, Nat.cast_add]

theorem port_casts (j : Fin 4) :
    ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V) = ι (naturalPorts (V := V) j) := by
  fin_cases j
  · exact port0
  · exact port1
  · exact port2
  · exact port3

theorem current_seed_zero_iff_static (w : Fin 38 → V) :
    InternalZero (SharingSeed38.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) ↔
      NormAssignment38.gatesHold ι (naturalPorts (V := V)) w ∧
        NormAssignment38.fiveNorms ι (naturalPorts (V := V)) w :=
  Norm38SeedStaticIff.seed_zero_iff_static _ _ w (port_casts (V := V))
end DiophantineConsistency.Norm38CurrentPorts
#print axioms DiophantineConsistency.Norm38CurrentPorts.port_casts
#print axioms DiophantineConsistency.Norm38CurrentPorts.current_seed_zero_iff_static
