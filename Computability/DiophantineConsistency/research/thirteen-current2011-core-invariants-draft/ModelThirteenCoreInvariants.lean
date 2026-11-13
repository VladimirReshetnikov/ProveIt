import DiophantineConsistency.ModelThirteenCarrierPrelude
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ModelThirteenCarrier
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts FreshCarrierSpheres
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticCarrierRadix2011 ArithmeticCurrentSentence2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Ring images of the maintained carrier parameters, extracted from completion. -/
theorem core_invariants (w : Fin 14 → V) (hFq : w 1 < q w) :
    let x : Fin 14 → DiffRing V := fun j => ι (w j)
    (Carrier65.core ringPorts x).q = ι (q w) ∧
    (Carrier65.core ringPorts x).Y = ι (Y w) ∧
    (Carrier65.core ringPorts x).E = ι (X w * Y w) ∧
    (Carrier65.core ringPorts x).a = ι (X w * Y w + Y w) ∧
    (Carrier65.core ringPorts x).c = ι ((w 10 + w 11) * Y w + w 10) ∧
    (Carrier65.core ringPorts x).delta = ι (delta (X w * Y w + Y w)) ∧
    (Carrier65.core ringPorts x).rank = ι (rank w) := by
  dsimp only
  set x : Fin 14 → DiffRing V := fun j => ι (w j) with hxdef
  have hq1 : 1 ≤ q w := by show 1 ≤ (CurrentMasks2011.beta : V) * w 0 + 1; exact le_add_self
  have hq2 : 1 ≤ q w ^ 2 := one_le_pow₀ hq1
  -- ring-level core quantities are images of the model quantities
  have eq_q : (Carrier65.core ringPorts x).q = ι (q w) := by
    change ringPorts 0 * x 0 + 1 = _; rw [port0]
    simp only [hxdef, q, map_add, map_mul, map_one]
  have eq_Y : (Carrier65.core ringPorts x).Y = ι (Y w) := by
    change x 7 * (Carrier65.core ringPorts x).q ^ 3 = _; rw [eq_q]
    simp only [hxdef, Y, map_mul, map_pow]
  have eq_E : (Carrier65.core ringPorts x).E = ι (X w * Y w) := by
    change (x 8 * (Carrier65.core ringPorts x).q) * (Carrier65.core ringPorts x).Y = _
    rw [eq_q, eq_Y]; simp only [hxdef, X, map_mul]
  have eq_a : (Carrier65.core ringPorts x).a = ι (X w * Y w + Y w) := by
    change (Carrier65.core ringPorts x).E + (Carrier65.core ringPorts x).Y = _
    rw [eq_E, eq_Y, map_add]
  have eq_c : (Carrier65.core ringPorts x).c = ι ((w 10 + w 11) * Y w + w 10) := by
    change (x 10 + x 11) * (Carrier65.core ringPorts x).Y + x 10 = _
    rw [eq_Y]; simp only [hxdef, map_add, map_mul]
  have eq_delta : (Carrier65.core ringPorts x).delta = ι (delta (X w * Y w + Y w)) := by
    change (Carrier65.core ringPorts x).a ^ 2 + (4 * (Carrier65.core ringPorts x).a + 3) = _
    rw [eq_a]; unfold delta; simp only [map_mul, map_add, map_ofNat, map_one]; ring
  have eq_rank : (Carrier65.core ringPorts x).rank = ι (rank w) := by
    change (ringPorts 0 * x 0 * ((Carrier65.core ringPorts x).q - x 1) + x 2) *
      ((Carrier65.core ringPorts x).q ^ 2 - 1) +
      (ringPorts 2 + (Carrier65.core ringPorts x).q * ringPorts 3) * x 0 = _
    rw [eq_q, port0, port2, port3]
    show _ = ι (((q w - 1) * (q w - w 1) + w 2) * (q w ^ 2 - 1) +
      ((CurrentMasks2011.lowPort : V) + q w * ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V)) * w 0)
    simp only [map_add, map_mul, map_pow, ArithmeticThirteenOuter.ι_tsub hq1,
      ArithmeticThirteenOuter.ι_tsub hFq.le, ArithmeticThirteenOuter.ι_tsub hq2, map_one]
    have hqx : ι (q w) = ι (CurrentMasks2011.beta : V) * x 0 + 1 := by
      simp only [hxdef, q, map_add, map_mul, map_one]
    rw [hqx]
    simp only [hxdef]
    ring
  exact ⟨eq_q, eq_Y, eq_E, eq_a, eq_c, eq_delta, eq_rank⟩

end DiophantineConsistency.ModelThirteenCarrier
