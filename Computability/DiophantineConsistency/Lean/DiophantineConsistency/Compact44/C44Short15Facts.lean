import DiophantineConsistency.Mixed121.Short15Facts
import DiophantineConsistency.Compact44.CompactLeafFactsHalt
import DiophantineConsistency.Compact44.CompactMaskBoundFinish
import DiophantineConsistency.Compact44.TopDigitClean
import DiophantineConsistency.Compact44.CompactSymbolicPortProjections

/-! # Fifteen-positive forms at the compact44 ports: the halt

`Short15Facts.facts_core` is port-generic: from the first norm, the main norm,
an index oracle and the sign of `Nk = Nt`, it gives the six leaf facts at
`![J, F, α, 1, 1, X, Y, 1, η, ζ, 1, 1]` for any natural ports `p` with
`0 < β`, `MC < β`, `MF < 2β`, `46 ≤ β` and `0 < K0`. This module discharges
those bounds at the compact44 ports `ports betaNat (paramKernel rho) lowNat
highNat` (`CompactMaskBoundFinish.bounds`, `TopDigit.kernel_bounds`) and closes
the halt with `CompactLeafFactsHalt.halts_of_facts`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace C44Short15Facts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticPellRecurrence
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactLeafFacts
open Short15Graph Short15Root
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The compact44 ports, as natural numbers. -/
abbrev c44 : Fin 4 → ℕ := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat

/-- The compact44 ports, as integers (definitionally
`CompactSymbolicPortProjections.portsInt (paramKernel rho)`). -/
abbrev intPorts : Fin 4 → ℤ := fun j => (c44 j : ℤ)

theorem intPorts_eq : intPorts = CompactSymbolicPortProjections.portsInt (paramKernel rho) := rfl

/-- The port bounds of `Short15Facts.facts_core`, stated for variables. -/
theorem port_bounds (B K L H : ℕ) (hB : (B : V) + 1 = Exp.exp ((67 : V) * 8807))
    (hL : L = lowNat) (hH : H = highNat) :
    0 < (ports B K L H 0 : V) ∧ (ports B K L H 2 : V) < (ports B K L H 0 : V) ∧
      (ports B K L H 3 : V) < 2 * (ports B K L H 0 : V) ∧ (46 : V) ≤ (ports B K L H 0 : V) := by
  obtain ⟨hb, hl', hh', _⟩ := CompactMaskBoundFinish.bounds (B : V) 1 hB (by simp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 0 < (B : V); exact hb
  · change (L : V) < (B : V); rw [hL]; exact hl'
  · change ((B + H : ℕ) : V) < 2 * (B : V); rw [Nat.cast_add, hH]; exact hh'
  · have h64 : (64 : V) = Exp.exp (6 : V) := by
      have h := ArithmeticStandardCasts.cast_exp (V := V) 6
      norm_num at h
      exact h.symm
    have hbig : (64 : V) ≤ (B : V) + 1 := by
      rw [hB, h64]; exact exp_monotone_le.mpr (by norm_num)
    change (46 : V) ≤ (B : V)
    apply le_iff_lt_succ.mpr
    exact lt_of_lt_of_le (by norm_num : (46 : V) < 64) hbig

/-- `0 < K0`, stated for variables. -/
theorem K_pos (B K L H : ℕ) (hK : K = paramKernel rho) : 0 < (ports B K L H 1 : V) := by
  have h : 0 < ports B K L H 1 := by
    rw [Short15Facts.ports_one, hK]
    exact lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℕ) < 2) 592883) TopDigit.kernel_bounds.1
  exact_mod_cast h

attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat

/-- The halt at the compact44 ports. -/
theorem halts_core (v : Fin 15 → V) (hv : ∀ j, 0 < v j) (τ : V)
    (hτ : τ * τ = ellV c44 v * (ellV c44 v + kV v) + 1)
    (hN1 : rN1 (fun j => (c44 j : ℤ)) (fun j => ι (v j)) = 1)
    (horacle : v 1 ≤ qV c44 v → 0 < RV c44 v → ∀ m g : V, 0 < m →
      ycoord m (aV c44 v) = cV c44 v →
      g * g = 1 + delta (aV c44 v) * cV c44 v * cV c44 v →
      2 * RV c44 v < cV c44 v →
      (aV c44 v + 2) * delta (aV c44 v) * delta (aV c44 v) < cV c44 v → m = RV c44 v)
    (hsign : (rNk (fun j => (c44 j : ℤ)) (fun j => ι (v j)) = 1 ∧
        rNt (fun j => (c44 j : ℤ)) (fun j => ι (v j)) = 1) ∨
      (rNk (fun j => (c44 j : ℤ)) (fun j => ι (v j)) = -1 ∧
        rNt (fun j => (c44 j : ℤ)) (fun j => ι (v j)) = -1)) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  obtain ⟨hb, hl, hh, h46⟩ := port_bounds (V := V) CompactFixedBeta.betaNat (paramKernel rho) lowNat
    highNat CompactFixedBeta.beta_identity rfl rfl
  have hK := K_pos (V := V) CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat rfl
  obtain ⟨X, Y, hX, hY, hF⟩ := Short15Facts.facts_core c44 hb hl hh h46 hK v hv τ hτ hN1
    horacle hsign
  apply CompactLeafFactsHalt.halts_of_facts _ _ hF
  intro i
  fin_cases i <;> simp [hX, hY, hv]

end C44Short15Facts

#print axioms C44Short15Facts.port_bounds
#print axioms C44Short15Facts.K_pos
#print axioms C44Short15Facts.halts_core
