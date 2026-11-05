import DiophantineConsistency.Compact44.P57Graph
import DiophantineConsistency.Compact44.P72Aux
import DiophantineConsistency.ModelArithmetic
import DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011

/-! # Package 57: the product-unit guard

At a positive zero, `Nt·(1 + N)·(1 + J_M) = 1` in the ring of differences of a
model of `𝗜𝚺₁`, so every factor is `±1`. Both `N` and `J_M` have the shape
`P² − 4w`. So `N = −2` or `J_M = −2` would give `P² + 2 = 4w`, impossible
modulo 4. Hence `Nt = 1`, `N = 0` and `J_M = 0`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace P57Units
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing P57Graph
open ArithmeticAdaptiveFactorUnits2011 (residue residue_add residue_mul residue_nat)
open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem r2 : residue (V := V) 2 = 2 := by simpa using residue_nat (V := V) 2
private theorem r4 : residue (V := V) 4 = 4 := by simpa using residue_nat (V := V) 4
private theorem norm_bad : ∀ x w : ZMod 4, x * x + 2 ≠ 4 * w := by decide

/-- `P² − 4w = −2` is impossible in the ring of differences. -/
theorem not_neg_two (P w : DiffRing V) (h : P * P - 4 * w = -2) : False := by
  obtain ⟨P0, N0, hPN⟩ := exists_mk P
  rw [mk_eq_sub] at hPN
  have hsq : P * P = ι (absdiff P0 N0) * ι (absdiff P0 N0) := by rw [P72Aux.ι_absdiff_sq, hPN]
  rw [hsq] at h
  have hpos : 0 ≤ w := by
    have := mul_self_nonneg (ι (absdiff P0 N0))
    linarith
  obtain ⟨w0, hw0⟩ := nonneg_iff.mp hpos
  rw [hw0] at h
  have hV : absdiff P0 N0 * absdiff P0 N0 + 2 = 4 * w0 := by
    apply ι_injective
    simp only [map_add, map_mul, map_ofNat]
    linear_combination h
  have hr := congrArg (residue (V := V)) hV
  simp only [residue_add, residue_mul, r2, r4] at hr
  exact norm_bad _ _ hr

/-- A positive zero makes the three factors `1, 0, 0`. -/
theorem units (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hz : InternalZero (graph (fun j => (p j : ℤ))).output v) :
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Nt = 1 ∧
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).N = 0 ∧
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).inner = 0 := by
  rw [internalZero_iff, output_eval] at hz
  set W := vals (fun j => (p j : ℤ)) (fun j => ι (v j)) with hW
  have hprod : W.Nt * (W.N + 1) * (W.inner + 1) = 1 := by linear_combination hz
  have hd := ModelArithmetic.model_discrete (V := V)
  have u2 := DiscreteOrderedRingFacts.eq_one_or_neg_one_of_mul_eq_one hd
    (x := W.N + 1) (y := W.Nt * (W.inner + 1)) (by linear_combination hprod)
  have u3 := DiscreteOrderedRingFacts.eq_one_or_neg_one_of_mul_eq_one hd
    (x := W.inner + 1) (y := W.Nt * (W.N + 1)) (by linear_combination hprod)
  have h2 : W.N + 1 = 1 := by
    rcases u2 with h | h
    · exact h
    · exfalso
      have hN : W.N = ((W.W * W.W + (W.U * W.U) * W.G) - (W.S * W.S) * W.A) *
          ((W.W * W.W + (W.U * W.U) * W.G) - (W.S * W.S) * W.A) - 4 * ((W.W * W.W) * ((W.U * W.U) * W.G)) := rfl
      exact not_neg_two _ _ (by rw [← hN]; linear_combination h)
  have h3 : W.inner + 1 = 1 := by
    rcases u3 with h | h
    · exact h
    · exfalso
      have hJ : W.inner = W.Z * W.Z - 4 * ((W.D * (W.v * W.v)) * (W.baux * W.baux)) := rfl
      exact not_neg_two _ _ (by rw [← hJ]; linear_combination h)
  have h1 : W.Nt = 1 := by
    rw [h2, h3] at hprod; linear_combination hprod
  exact ⟨h1, by linear_combination h2, by linear_combination h3⟩

end P57Units

#print axioms P57Units.not_neg_two
#print axioms P57Units.units
